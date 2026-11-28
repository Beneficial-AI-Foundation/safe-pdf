import SafePdf.Core.Doc

/-!
# Navigation: outline, destinations, links, page labels (task 4.2)

Plan.md §6 Phase 4 ("Outline, named destinations, internal links, page labels (Tier 1
navigation) — same visited-set discipline (outlines in the wild contain cycles)"), §5.2
(termination by visited sets and fuel), §4 S2 (totality). ISO 32000-2 §12.3.3 (document
outline), §12.3.2 (destinations, named destinations), §7.9.6 (name trees), §7.9.7 (number
trees), §12.6.4.2 (GoTo actions), §12.5.6.5 (link annotations), §12.4.2 (page labels).

**Navigation never fails the document.** Every function here is total and returns plain data:
a failed fetch, a value of the wrong shape, a cycle or a node reached twice is skipped and
counted in a `warnings` field (where the result has one), never an `Error`.

## Rules

* N1. **Lenient resolution.** Values are resolved one level (`Doc.resolve`); a fetch error or a
  stream counts as `null` (`res`, `getL`).
* N2. **Trees** (name trees, number trees; `treeWalk`). A worklist in preorder: the root (a
  reference, or a direct dictionary processed before the loop) and then `/Kids` entries, which
  must be indirect references (§7.9.6). Popping a reference whose object number was already
  visited, or a `/Kids` element that is not a reference, is a **warning** and the branch is
  cut. Every fresh reference popped is marked visited and costs one unit of fuel; fuel is
  `objectCount`, and running out with work left is one warning. A node that is not a
  dictionary is a warning. Entries are collected from `/Names` (`/Nums`) of every node, in
  document order; a malformed key or an odd-length array is a warning per bad pair.
* N3. **Lookup** (`treeLookup`) uses the same walk with a wanted key: a node whose `/Limits`
  (two valid keys) exclude the key is skipped with its subtree, entries with other keys are
  dropped, and the walk stops at the first match. Name keys compare as raw bytes (§7.9.6);
  name-tree keys may also be names (lenient).
* N4. **Destinations** (§12.3.2). An explicit destination `[page /Fit …]` keeps its page
  reference (or integer page index, which some producers write) as data and resolves it to a
  page index of the document when it is one of its pages (`pageIndex`); otherwise the index
  is `none`. The fit spec is kept with optional (exact) numbers; an unknown fit name is kept.
  A **named destination** (name or string) is looked up in the catalog `/Dests` dictionary
  (PDF 1.1) and in the `/Names /Dests` name tree: names try the dictionary first, strings the
  tree first. The value is an array or a dictionary with `/D`; any other value, or no entry,
  is `Target.unresolved` with the name (kept as data). Named values are not followed further.
* N5. **Actions** (§12.6.4.2): `/A` with `/S /GoTo` resolves its `/D` as N4; any `/S /URI` is kept as `Target.uri` with its `/URI` string (at most `maxUriBytes`); any other action
  type is kept as `Target.action` with its `/S` bytes (GoToR, Launch, … — not followed).
  `/Dest` takes precedence over `/A` (§12.3.3, §12.5.6.5).
* N6. **Outline** (§12.3.3; `outline`). From `/Outlines /First`, a preorder worklist of
  `(reference, depth)`: a visited item pushes its `/First` (depth + 1) and then its `/Next`
  (same depth). A reference already visited (a `/Next` back to an earlier item, a `/First` to
  an ancestor) or equal to the outline root is a warning and that branch is cut; fuel is
  `objectCount`. `/Prev`, `/Last`, `/Parent` and `/Count` are not used for the walk
  (`/Count` is kept). Items come out as a **flat preorder list with depths**; titles are raw
  bytes (text decoding is phase 6; strings of encrypted files are not yet decrypted, task
  4.3b).
* N7. **Links** (§12.5.6.5; `pageLinks`). The page's own `/Annots` (resolved one level), each
  element resolved one level; dictionaries with `/Subtype /Link` and a valid `/Rect`
  (`Doc.rectOf`, normalized) give `(rect, target)` by N4/N5; others are skipped.
* N8. **Page labels** (§12.4.2; `pageLabel`). The `/PageLabels` number tree is enumerated (N2);
  each entry with a key `k ≥ 0` and a dictionary value is a range from page index `k`. Page
  `i` uses the range with the greatest start `≤ i` (the later one on ties); with no
  applicable range the label is the decimal `i + 1`. The label is `/P` followed by the
  numeric part for value `/St + (i − start)` (`/St` defaults to 1; a value below 1 counts as
  1) in style `/S`: `D` decimal, `R`/`r` roman upper/lower, `A`/`a` letters (A..Z, then AA..ZZ,
  AAA..: 27 is AA, 28 is BB); no `/S` means no numeric part. Roman and letter forms are used
  for values `1..3999` (`labelCap`); larger values fall back to decimal digits so that label
  length stays bounded (a `/St 1000000000` cannot produce a huge string).

## Work bounds

A tree walk and the outline walk each fetch at most `objectCount` nodes (one `getObject`
each, plus one-level resolutions of a bounded number of keys per node). Every outline item and
link may look up one named destination (one tree walk, pruned by `/Limits`), so the outline
costs at most `objectCount · (objectCount + c)` fetches in the worst case (an unpruned
adversarial name tree); with valid `/Limits` a lookup fetches the kids of the nodes on one
root-to-leaf path only (each kid is fetched to read its `/Limits`). `pageIndex` is linear in the
page count.

## Theorems

* Totality: by construction (structural recursion on fuel, lists, and pairs).
* `popFresh_fresh`, `popOutline_fresh`: a popped reference was not visited.
  The outline walk tests visited references in a `VSet` that mirrors `visited ++ root`
  (`O(log n)`; task 13.26: a list scan made a flat outline of n items quadratic); the list
  stays the specification.
* `treeLoop_inv`, `treeLoop_nil`: the loop keeps the visited list duplicate-free and adds at
  most one node per unit of fuel; `visitTree_visited`; `treeWalk_visited_le` (**nodes visited ≤ objectCount**), `treeWalk_nodup`
  (**no node visited twice**); `treeLookup` and `treeEntries` are projections of `treeWalk`.
* `outlineLoop_inv`, `outline_ofState_inv`, `outline_inv`; `outline_visited_le`, `outline_nodup`, `outline_items_le` (**items ≤
  objectCount**), `outline_items_le_visited`.
* `labelTable_visited_le`, `labelTable_nodup`, `destsTree_visited_le`.
* Page-label formatting (`toRoman`, `toLetters`, `formatLabel`): `#guard` checks, including a
  round trip of `toRoman` on all of `1..3999`.
-/

set_option autoImplicit false

namespace SafePdf.Core.Doc.Nav

open SafePdf
open SafePdf.Core.Doc

/-! ## Lenient access (rule N1) -/

/-- Resolve one level, leniently: a reference is fetched once; a fetch error or a stream is
`null` (rule N1). -/
def res (doc : Doc) (limits : Limits) (o : PdfObject) : PdfObject :=
  match resolve doc.file limits o with
  | .ok v => v
  | .error _ => .null

/-- The value of key `k` resolved one level (rule N1); `null` if absent. -/
def getL (doc : Doc) (limits : Limits) (nd : Dict) (k : String) : PdfObject :=
  match Dict.get? nd (Name.ofString k) with
  | none => .null
  | some o => res doc limits o

/-- The raw (unresolved) value of key `k`. -/
def raw (nd : Dict) (k : String) : Option PdfObject := Dict.get? nd (Name.ofString k)

/-- Fetch object `n g` as a dictionary; `none` for anything else or a fetch error. -/
def fetchDict (doc : Doc) (limits : Limits) (n g : Nat) : Option Dict :=
  match doc.file.getObject limits n g with
  | .ok (.obj (.dict nd)) => some nd
  | _ => none

/-- Byte-lexicographic order on strings (name-tree key order, §7.9.6). -/
def bytesLe : List UInt8 → List UInt8 → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a < b then true else if b < a then false else bytesLe as bs

/-! ## Name trees and number trees (rules N2, N3) -/

/-- The kind of a tree: the entries key and the key type with its order. -/
structure TreeSpec (K : Type) where
  /-- `"Names"` (name tree) or `"Nums"` (number tree). -/
  entries : String
  /-- The key of an entry, if it has the right shape. -/
  keyOf : PdfObject → Option K
  /-- The key order. -/
  le : K → K → Bool

/-- Name trees (§7.9.6): string keys (names accepted leniently), byte order. -/
def nameTree : TreeSpec (List UInt8) where
  entries := "Names"
  keyOf := fun
    | .string s => some s
    | .name n => some n.bytes
    | _ => none
  le := bytesLe

/-- Number trees (§7.9.7): integer keys. -/
def numberTree : TreeSpec Int where
  entries := "Nums"
  keyOf := fun
    | .int i => some i
    | _ => none
  le := fun a b => decide (a ≤ b)

/-- The key/value pairs of a `/Names` or `/Nums` array, and the number of bad pairs (a key of
the wrong shape, or a dangling last element). -/
def pairs {K : Type} (spec : TreeSpec K) : List PdfObject → List (K × PdfObject) × Nat
  | [] => ([], 0)
  | [_] => ([], 1)
  | k :: v :: rest =>
    let r := pairs spec rest
    match spec.keyOf k with
    | some key => ((key, v) :: r.1, r.2)
    | none => (r.1, r.2 + 1)

/-- Whether a `/Limits` value admits key `k` (rule N3); a malformed `/Limits` admits all. -/
def inLimits {K : Type} (spec : TreeSpec K) (k : K) : PdfObject → Bool
  | .array [lo, hi] =>
    match spec.keyOf lo, spec.keyOf hi with
    | some lo, some hi => spec.le lo k && spec.le k hi
    | _, _ => true
  | _ => true

/-- Key equality from the order. -/
def keyEq {K : Type} (spec : TreeSpec K) (a b : K) : Bool := spec.le a b && spec.le b a

/-- The walk state of a tree. -/
structure TreeState (K : Type) where
  /-- Kid references still to visit, next first. -/
  stack : List PdfObject
  /-- Object numbers of the visited nodes, newest first. -/
  visited : List Nat
  /-- Entries found, newest first. -/
  out : List (K × PdfObject)
  /-- Problems skipped (rule N2). -/
  warnings : Nat

/-- What one node contributes (rules N2, N3): its kids, its (wanted) entries in order, and the
number of warnings. -/
def nodeStep {K : Type} (doc : Doc) (limits : Limits) (spec : TreeSpec K) (want : Option K)
    (nd : Dict) : List PdfObject × List (K × PdfObject) × Nat :=
  let skip : Bool :=
    match want with
    | some k => !inLimits spec k (getL doc limits nd "Limits")
    | none => false
  if skip then ([], [], 0)
  else
    let kids : List PdfObject × Nat :=
      match getL doc limits nd "Kids" with
      | .array xs => (xs, 0)
      | .null => ([], 0)
      | _ => ([], 1)
    let ents : List (K × PdfObject) × Nat :=
      match getL doc limits nd spec.entries with
      | .array xs => pairs spec xs
      | .null => ([], 0)
      | _ => ([], 1)
    let sel : List (K × PdfObject) :=
      match want with
      | some k => ents.1.filter (fun p => keyEq spec p.1 k)
      | none => ents.1
    (kids.1, sel, kids.2 + ents.2)

/-- Visit a node dictionary: push its kids (before the rest: preorder), record its entries. -/
def visitTree {K : Type} (doc : Doc) (limits : Limits) (spec : TreeSpec K) (want : Option K)
    (nd : Dict) (st : TreeState K) : TreeState K :=
  let r := nodeStep doc limits spec want nd
  { st with stack := r.1 ++ st.stack, out := r.2.1.reverse ++ st.out,
            warnings := st.warnings + r.2.2 }

/-- Pop the next fresh reference (rule N2): visited references and non-references are skipped
and counted. -/
def popFresh (visited : List Nat) :
    List PdfObject → Nat → Option (Nat × Nat × List PdfObject) × Nat
  | [], w => (none, w)
  | .ref n g :: rest, w =>
    if n ∈ visited then popFresh visited rest (w + 1) else (some (n, g, rest), w)
  | _ :: rest, w => popFresh visited rest (w + 1)

/-- The tree loop (rules N2, N3): one fresh node per unit of fuel. -/
def treeLoop {K : Type} (doc : Doc) (limits : Limits) (spec : TreeSpec K) (want : Option K) :
    Nat → TreeState K → TreeState K
  | 0, st => if st.stack.isEmpty then st else { st with warnings := st.warnings + 1 }
  | f + 1, st =>
    if want.isSome && !st.out.isEmpty then st
    else
      match popFresh st.visited st.stack st.warnings with
      | (none, w) => { st with stack := [], warnings := w }
      | (some (n, g, rest), w) =>
        match fetchDict doc limits n g with
        | some nd =>
          treeLoop doc limits spec want f
            (visitTree doc limits spec want nd
              { st with stack := rest, visited := n :: st.visited, warnings := w })
        | none =>
          treeLoop doc limits spec want f
            { st with stack := rest, visited := n :: st.visited, warnings := w + 1 }

/-- The empty tree state with `w` warnings. -/
def TreeState.empty {K : Type} (w : Nat) : TreeState K := ⟨[], [], [], w⟩

/-- **Walk a tree** from its root value (a reference, or a direct dictionary): fuel
`objectCount` (rule N2). -/
def treeWalk {K : Type} (doc : Doc) (limits : Limits) (spec : TreeSpec K) (want : Option K)
    (root : PdfObject) : TreeState K :=
  match root with
  | .ref _ _ => treeLoop doc limits spec want doc.file.objectCount ⟨[root], [], [], 0⟩
  | .dict nd =>
    treeLoop doc limits spec want doc.file.objectCount
      (visitTree doc limits spec want nd (TreeState.empty 0))
  | .null => TreeState.empty 0
  | _ => TreeState.empty 1

/-- All entries of a tree, in document order. -/
def treeEntries {K : Type} (doc : Doc) (limits : Limits) (spec : TreeSpec K)
    (root : PdfObject) : List (K × PdfObject) :=
  (treeWalk doc limits spec none root).out.reverse

/-- The value of key `k` in a tree (rule N3), if found. -/
def treeLookup {K : Type} (doc : Doc) (limits : Limits) (spec : TreeSpec K)
    (root : PdfObject) (k : K) : Option PdfObject :=
  ((treeWalk doc limits spec (some k) root).out.reverse.head?).map Prod.snd

/-! ## Destinations (rule N4) -/

/-- A fit specification (§12.3.2.2, Table 149); numbers are exact, `none` for `null`. -/
inductive Fit where
  /-- `/XYZ left top zoom`. -/
  | xyz (left top zoom : Option Decimal)
  /-- `/Fit`. -/
  | fit
  /-- `/FitH top`. -/
  | fitH (top : Option Decimal)
  /-- `/FitV left`. -/
  | fitV (left : Option Decimal)
  /-- `/FitR left bottom right top`. -/
  | fitR (left bottom right top : Option Decimal)
  /-- `/FitB`. -/
  | fitB
  /-- `/FitBH top`. -/
  | fitBH (top : Option Decimal)
  /-- `/FitBV left`. -/
  | fitBV (left : Option Decimal)
  /-- Another (or a missing: `[]`) fit name, kept as data. -/
  | unknown (name : List UInt8)
  deriving DecidableEq, Repr

/-- The `i`-th fit argument as a number, `none` if absent or not a number. -/
def fitArg (args : List PdfObject) (i : Nat) : Option Decimal := (args[i]?).bind numOf

/-- The fit spec of the elements after the page in an explicit destination. -/
def fitOf : List PdfObject → Fit
  | .name nm :: a =>
    if nm = Name.ofString "XYZ" then .xyz (fitArg a 0) (fitArg a 1) (fitArg a 2)
    else if nm = Name.ofString "Fit" then .fit
    else if nm = Name.ofString "FitH" then .fitH (fitArg a 0)
    else if nm = Name.ofString "FitV" then .fitV (fitArg a 0)
    else if nm = Name.ofString "FitR" then .fitR (fitArg a 0) (fitArg a 1) (fitArg a 2) (fitArg a 3)
    else if nm = Name.ofString "FitB" then .fitB
    else if nm = Name.ofString "FitBH" then .fitBH (fitArg a 0)
    else if nm = Name.ofString "FitBV" then .fitBV (fitArg a 0)
    else .unknown nm.bytes
  | _ => .unknown []

/-- The page designator of an explicit destination, as written. -/
inductive PageRef where
  /-- An indirect reference to a page object (§12.3.2.2). -/
  | ref (num gen : Nat)
  /-- An integer page index (remote destinations; also written by some producers locally). -/
  | index (i : Int)
  /-- Anything else. -/
  | other
  deriving DecidableEq, Repr

/-- An explicit destination in a document of `n` pages: the page as written, the page index if
it is one of the document's pages (else `none`: kept as data), and the fit. -/
structure Dest (n : Nat) where
  /-- The named destination this was reached through, if any. -/
  name : Option (List UInt8)
  /-- The page designator as written. -/
  target : PageRef
  /-- The resolved page index, if the designator is one of the document's pages. -/
  page : Option (Fin n)
  /-- The fit specification. -/
  fit : Fit
  deriving DecidableEq, Repr

/-- Where a link, an outline item or an action leads (rules N4, N5). -/
inductive Target (n : Nat) where
  /-- No destination or action (or a malformed one). -/
  | none
  /-- An explicit destination (possibly reached through a name). -/
  | dest (d : Dest n)
  /-- A named destination that was not found or whose value is malformed. -/
  | unresolved (name : List UInt8)
  /-- A URI action (`/S /URI`) with its `/URI` string, raw bytes of at most `maxUriBytes`
  (never followed). -/
  | uri (bytes : List UInt8)
  /-- Another action type, kept with its `/S` name bytes (not followed). -/
  | action (kind : List UInt8)
  deriving DecidableEq, Repr

/-- Longest `/URI` string kept by `Target.uri`; a longer one leaves a bare `Target.action`
(a URI is never truncated: a prefix could name another address). -/
def maxUriBytes : Nat := 8192

/-- The index of the page whose object number is `num`, if any. -/
def pageIndex (pages : Array Page) (num : Nat) : Option (Fin pages.size) :=
  pages.findFinIdx? (fun p => p.num == num)

/-- The page of a designator: a reference to one of the pages, or an in-range integer. -/
def pageOf (doc : Doc) : PdfObject → PageRef × Option (Fin doc.pages.size)
  | .ref n g => (.ref n g, pageIndex doc.pages n)
  | .int i =>
    (.index i, if h : 0 ≤ i ∧ i.toNat < doc.pages.size then some ⟨i.toNat, h.2⟩ else none)
  | _ => (.other, none)

/-- An explicit destination from its array elements; `none` for an empty array. -/
def explicitDest (doc : Doc) (name : Option (List UInt8)) :
    List PdfObject → Option (Dest doc.pages.size)
  | [] => none
  | p :: rest =>
    let t := pageOf doc p
    some ⟨name, t.1, t.2, fitOf rest⟩

/-- The catalog's `/Dests` dictionary (PDF 1.1), if any. -/
def destsDict (doc : Doc) (limits : Limits) : Option Dict :=
  match getL doc limits doc.catalog "Dests" with
  | .dict dd => some dd
  | _ => none

/-- `destsDict` is `destsDictOf` on the document's file and catalog. -/
theorem destsDict_eq (doc : Doc) (limits : Limits) :
    destsDict doc limits = destsDictOf doc.file limits doc.catalog := by
  unfold destsDict getL destsDictOf res
  cases Dict.get? doc.catalog (Name.ofString "Dests") with
  | none => rfl
  | some o =>
    simp only
    cases resolve doc.file limits o with
    | error e => rfl
    | ok v => cases v <;> rfl

/-- The entry `k` of the catalog's `/Dests` dictionary (`Dict.get?`), through the document's
ordered index when `limits` are those it was built under (`O(log n)`), else by scanning
`destsDict` (task 13.24). -/
def destsLookup (doc : Doc) (limits : Limits) (k : Name) : Option PdfObject :=
  if limits = doc.dests.limits then
    match doc.dests.idx.get with
    | some m => Dict.getIdx m k
    | none => none
  else
    match destsDict doc limits with
    | some dd => Dict.get? dd k
    | none => none

/-- **`destsLookup` is the list scan** `Dict.get?` on `destsDict`, for every document and every
`limits` (duplicate keys included: both take the first entry). -/
theorem destsLookup_eq (doc : Doc) (limits : Limits) (k : Name) :
    destsLookup doc limits k =
      (match destsDict doc limits with
        | some dd => Dict.get? dd k
        | none => none) := by
  unfold destsLookup
  split
  · rename_i hl
    have h := doc.dests.h
    rw [← hl] at h
    rw [destsDict_eq]
    rw [h]
    cases destsDictOf doc.file limits doc.catalog with
    | none => rfl
    | some dd => exact Dict.getIdx_index dd k
  · rfl

/-- The root of the `/Names /Dests` name tree, unresolved (`null` if absent). -/
def destsRoot (doc : Doc) (limits : Limits) : PdfObject :=
  match getL doc limits doc.catalog "Names" with
  | .dict nd => (raw nd "Dests").getD .null
  | _ => .null

/-- The value of a named destination (rule N4): names try `/Dests` first, strings the name
tree first. -/
def namedValue (doc : Doc) (limits : Limits) (isName : Bool) (s : List UInt8) :
    Option PdfObject :=
  let viaDict : Unit → Option PdfObject := fun _ => destsLookup doc limits ⟨s⟩
  let viaTree : Unit → Option PdfObject := fun _ =>
    treeLookup doc limits nameTree (destsRoot doc limits) s
  if isName then (viaDict ()).orElse viaTree else (viaTree ()).orElse viaDict

/-- The target of a named destination's value: an array, or a dictionary with `/D`. -/
def namedTarget (doc : Doc) (limits : Limits) (s : List UInt8) (v : PdfObject) :
    Target doc.pages.size :=
  let arr : PdfObject :=
    match res doc limits v with
    | .dict dd => getL doc limits dd "D"
    | o => o
  match arr with
  | .array xs =>
    match explicitDest doc (some s) xs with
    | some d => .dest d
    | none => .unresolved s
  | _ => .unresolved s

/-- Resolve a destination value (rule N4): an explicit array, or a name or string naming one. -/
def resolveDest (doc : Doc) (limits : Limits) (o : PdfObject) : Target doc.pages.size :=
  let named (isName : Bool) (s : List UInt8) : Target doc.pages.size :=
    match namedValue doc limits isName s with
    | some v => namedTarget doc limits s v
    | none => .unresolved s
  match res doc limits o with
  | .array xs =>
    match explicitDest doc none xs with
    | some d => .dest d
    | none => .none
  | .name nm => named true nm.bytes
  | .string s => named false s
  | _ => .none

/-- Resolve an action (rule N5): `GoTo` resolves its `/D`; `URI` keeps its string; other types
are kept by name. -/
def resolveAction (doc : Doc) (limits : Limits) (a : PdfObject) : Target doc.pages.size :=
  match res doc limits a with
  | .dict ad =>
    match getL doc limits ad "S" with
    | .name s =>
      if s = Name.ofString "GoTo" then resolveDest doc limits ((raw ad "D").getD .null)
      else if s = Name.ofString "URI" then
        match getL doc limits ad "URI" with
        | .string u => if u.length ≤ maxUriBytes then .uri u else .action s.bytes
        | _ => .action s.bytes
      else .action s.bytes
    | _ => .none
  | _ => .none

/-- The target of an outline item or link annotation: `/Dest`, else `/A` (rule N5). -/
def targetOf (doc : Doc) (limits : Limits) (nd : Dict) : Target doc.pages.size :=
  match raw nd "Dest" with
  | some d => resolveDest doc limits d
  | none =>
    match raw nd "A" with
    | some a => resolveAction doc limits a
    | none => .none

/-! ## Outline (rule N6) -/

/-- An outline item (§12.3.3), in a flat preorder list. -/
structure OutlineItem (n : Nat) where
  /-- Object number of the item dictionary. -/
  num : Nat
  /-- Generation of the item dictionary. -/
  gen : Nat
  /-- `/Title`, raw bytes (PDFDocEncoding or UTF-16; decoded in phase 6). -/
  title : List UInt8
  /-- Where the item leads. -/
  target : Target n
  /-- Nesting depth: 0 for top-level items. -/
  depth : Nat
  /-- `/Count`, if an integer (its sign says open or closed). -/
  count : Option Int
  deriving Repr

/-- The outline walk state. -/
structure OutlineState (n : Nat) (root : List Nat) where
  /-- Item references to visit with their depths, next first. -/
  stack : List (PdfObject × Nat)
  /-- Object numbers of visited items, newest first. -/
  visited : List Nat
  /-- An ordered set mirroring `visited ++ root` (the visited test in `O(log n)`; task 13.26:
  a list scan made a flat outline of n items quadratic). -/
  seen : VSet (visited ++ root)
  /-- Items, newest first. -/
  items : List (OutlineItem n)
  /-- Cut branches and malformed items (rule N6). -/
  warnings : Nat

/-- Pop the next fresh item reference: seen references and non-references are cut and
counted. -/
def popOutline (l : List Nat) (seen : VSet l) :
    List (PdfObject × Nat) → Nat → Option (Nat × Nat × Nat × List (PdfObject × Nat)) × Nat
  | [], w => (none, w)
  | (.ref n g, dp) :: rest, w =>
    if seen.has n then popOutline l seen rest (w + 1) else (some (n, g, dp, rest), w)
  | _ :: rest, w => popOutline l seen rest (w + 1)

/-- The item of a visited node. -/
def outlineItem (doc : Doc) (limits : Limits) (n g dp : Nat) (nd : Dict) :
    OutlineItem doc.pages.size where
  num := n
  gen := g
  title := match getL doc limits nd "Title" with
    | .string s => s
    | _ => []
  target := targetOf doc limits nd
  depth := dp
  count := match getL doc limits nd "Count" with
    | .int c => some c
    | _ => none

/-- What a visited item pushes: its `/First` (one deeper), then its `/Next`. -/
def outlineKids (nd : Dict) (dp : Nat) : List (PdfObject × Nat) :=
  ((raw nd "First").map (·, dp + 1)).toList ++ ((raw nd "Next").map (·, dp)).toList

/-- The outline loop (rule N6): `root` lists the outline root's object number (never an item). -/
def outlineLoop (doc : Doc) (limits : Limits) (root : List Nat) :
    Nat → OutlineState doc.pages.size root → OutlineState doc.pages.size root
  | 0, st => if st.stack.isEmpty then st else { st with warnings := st.warnings + 1 }
  | f + 1, st =>
    match popOutline _ st.seen st.stack st.warnings with
    | (none, w) => { st with stack := [], warnings := w }
    | (some (n, g, dp, rest), w) =>
      match fetchDict doc limits n g with
      | some nd =>
        outlineLoop doc limits root f
          { stack := outlineKids nd dp ++ rest, visited := n :: st.visited,
            seen := st.seen.insert n,
            items := outlineItem doc limits n g dp nd :: st.items, warnings := w }
      | none =>
        outlineLoop doc limits root f
          { stack := rest, visited := n :: st.visited, seen := st.seen.insert n,
            items := st.items, warnings := w + 1 }

/-- The document outline. -/
structure Outline (n : Nat) where
  /-- Items in preorder (document order), with depths. -/
  items : List (OutlineItem n)
  /-- Cut cycles, repeated nodes and malformed items (rule N6). -/
  warnings : Nat
  /-- Object numbers of the visited items (for the theorems). -/
  visited : List Nat

/-- The outline of a run of the loop. -/
def Outline.ofState {n : Nat} {root : List Nat} (st : OutlineState n root) : Outline n :=
  ⟨st.items.reverse, st.warnings, st.visited⟩

/-- The object number of the outline root, if it is a reference (it is never an item). -/
def rootNums : PdfObject → List Nat
  | .ref n _ => [n]
  | _ => []

/-- Folding inserts into a set adds exactly the folded elements. -/
theorem foldl_insert_contains (l : List Nat) :
    ∀ (init : NumSet) (x : Nat),
      (l.foldl (fun (v : NumSet) y => v.insert y) init).contains x = true ↔
        init.contains x = true ∨ x ∈ l := by
  induction l with
  | nil => intro init x; simp
  | cons y t ih =>
    intro init x
    have h1 : (compare y x == Ordering.eq) = true ↔ y = x := by simp
    rw [List.foldl_cons, ih, Std.TreeSet.contains_insert, List.mem_cons, Bool.or_eq_true, h1]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inr (Or.inl h.symm)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl h.symm)
      · exact Or.inr h

/-- The seen-set of the empty visited list: just the root. -/
def rootSeen (root : List Nat) : VSet ([] ++ root) :=
  ⟨root.foldl (fun (v : NumSet) y => v.insert y) ∅, fun x => by
    rw [foldl_insert_contains]
    simp⟩

/-- **The document outline** (rule N6); empty if there is none. -/
def outline (doc : Doc) (limits : Limits) : Outline doc.pages.size :=
  match raw doc.catalog "Outlines" with
  | none => ⟨[], 0, []⟩
  | some o =>
    match res doc limits o with
    | .dict od =>
      match raw od "First" with
      | some f =>
        Outline.ofState
          (outlineLoop doc limits (rootNums o) doc.file.objectCount ⟨[(f, 0)], [], rootSeen (rootNums o), [], 0⟩)
      | none => ⟨[], 0, []⟩
    | .null => ⟨[], 0, []⟩
    | _ => ⟨[], 1, []⟩

/-! ## Links (rule N7) -/

/-- A link annotation: its (normalized) rectangle and its target. -/
structure LinkAnnot (n : Nat) where
  /-- `/Rect`, normalized (§7.9.5). -/
  rect : Rect
  /-- Where it leads. -/
  target : Target n

/-- Whether an annotation dictionary is a `/Link` (§12.5.6.5). -/
def isLink (doc : Doc) (limits : Limits) (ad : Dict) : Bool :=
  match getL doc limits ad "Subtype" with
  | .name s => s = Name.ofString "Link"
  | _ => false

/-- The link annotation of one `/Annots` element, if it is a link with a valid rectangle. -/
def linkOf (doc : Doc) (limits : Limits) (a : PdfObject) : Option (LinkAnnot doc.pages.size) :=
  match res doc limits a with
  | .dict ad =>
    if isLink doc limits ad then
      (rectOf (getL doc limits ad "Rect")).map fun r => ⟨r, targetOf doc limits ad⟩
    else none
  | _ => none

/-- **The links of page `i`** (rule N7), in `/Annots` order. -/
def pageLinks (doc : Doc) (limits : Limits) (i : Fin doc.pages.size) :
    List (LinkAnnot doc.pages.size) :=
  let p := doc.pages[i]
  match fetchDict doc limits p.num p.gen with
  | none => []
  | some pd =>
    match getL doc limits pd "Annots" with
    | .array xs => xs.filterMap (linkOf doc limits)
    | _ => []

/-! ## Page labels (rule N8) -/

/-- Numbering styles (§12.4.2, Table 161). -/
inductive LabelStyle where
  /-- `/D`: decimal. -/
  | decimal
  /-- `/R`: upper-case roman. -/
  | romanUpper
  /-- `/r`: lower-case roman. -/
  | romanLower
  /-- `/A`: upper-case letters. -/
  | lettersUpper
  /-- `/a`: lower-case letters. -/
  | lettersLower
  /-- No `/S`: prefix only. -/
  | none
  deriving DecidableEq, Repr

/-- A labelling range: from page index `start`, style, prefix, first value. -/
structure LabelRange where
  /-- First page index of the range. -/
  start : Nat
  /-- Numbering style. -/
  style : LabelStyle
  /-- `/P`, raw bytes. -/
  pfx : List UInt8
  /-- `/St`, at least 1. -/
  first : Nat
  deriving DecidableEq, Repr

/-- The largest value formatted as roman numerals or letters (rule N8). -/
def labelCap : Nat := 3999

/-- Decimal digits of `v` as ASCII bytes. -/
def digits (v : Nat) : List UInt8 := (Nat.toDigits 10 v).map (fun c => c.toNat.toUInt8)

/-- Roman numeral symbols in decreasing value. -/
def romanTable : List (Nat × String) :=
  [(1000, "M"), (900, "CM"), (500, "D"), (400, "CD"), (100, "C"), (90, "XC"), (50, "L"),
   (40, "XL"), (10, "X"), (9, "IX"), (5, "V"), (4, "IV"), (1, "I")]

/-- Greedy roman numeral of `n` over a symbol table. -/
def romanAux : List (Nat × String) → Nat → List UInt8
  | [], _ => []
  | (v, s) :: rest, n =>
    (List.replicate (n / v) s.toUTF8.toList).flatten ++ romanAux rest (n % v)

/-- Upper-case roman numeral for `1..3999`; decimal digits otherwise (rule N8). -/
def toRoman (n : Nat) : List UInt8 :=
  if 1 ≤ n ∧ n ≤ labelCap then romanAux romanTable n else digits n

/-- ASCII lower case. -/
def lower (bs : List UInt8) : List UInt8 :=
  bs.map fun b => if 65 ≤ b ∧ b ≤ 90 then b + 32 else b

/-- Upper-case letters (A..Z, AA..ZZ, AAA..) for `1..3999`; decimal digits otherwise. -/
def toLetters (n : Nat) : List UInt8 :=
  if 1 ≤ n ∧ n ≤ labelCap then List.replicate ((n - 1) / 26 + 1) (65 + (n - 1) % 26).toUInt8
  else digits n

/-- The numeric part of a label in a style. -/
def styled : LabelStyle → Nat → List UInt8
  | .decimal, v => digits v
  | .romanUpper, v => toRoman v
  | .romanLower, v => lower (toRoman v)
  | .lettersUpper, v => toLetters v
  | .lettersLower, v => lower (toLetters v)
  | .none, _ => []

/-- The label of page `i` in range `r` (with `r.start ≤ i`). -/
def formatLabel (r : LabelRange) (i : Nat) : List UInt8 :=
  r.pfx ++ styled r.style (r.first + (i - r.start))

/-- The style of a resolved `/S` value. -/
def styleOf : PdfObject → LabelStyle
  | .name s =>
    if s = Name.ofString "D" then .decimal
    else if s = Name.ofString "R" then .romanUpper
    else if s = Name.ofString "r" then .romanLower
    else if s = Name.ofString "A" then .lettersUpper
    else if s = Name.ofString "a" then .lettersLower
    else .none
  | _ => .none

/-- The range of one number-tree entry; `none` for a negative key or a non-dictionary. -/
def rangeOf (doc : Doc) (limits : Limits) (k : Int) (v : PdfObject) : Option LabelRange :=
  if k < 0 then none
  else
    match res doc limits v with
    | .dict ld =>
      some { start := k.toNat, style := styleOf (getL doc limits ld "S"),
             pfx := (match getL doc limits ld "P" with
               | .string s => s
               | _ => []),
             first := (match getL doc limits ld "St" with
               | .int s => if 1 ≤ s then s.toNat else 1
               | _ => 1) }
    | _ => none

/-- The page-label table of a document (rule N8). -/
structure LabelTable where
  /-- The ranges in number-tree order. -/
  ranges : List LabelRange
  /-- Problems skipped (tree warnings and bad entries). -/
  warnings : Nat
  /-- Object numbers of the visited tree nodes (for the theorems). -/
  visited : List Nat

/-- The ranges of number-tree entries, and the count of bad entries. -/
def rangesOf (doc : Doc) (limits : Limits) : List (Int × PdfObject) → List LabelRange × Nat
  | [] => ([], 0)
  | (k, v) :: rest =>
    let r := rangesOf doc limits rest
    match rangeOf doc limits k v with
    | some x => (x :: r.1, r.2)
    | none => (r.1, r.2 + 1)

/-- **The page-label table** (rule N8): the `/PageLabels` number tree, enumerated once. -/
def labelTable (doc : Doc) (limits : Limits) : LabelTable :=
  match raw doc.catalog "PageLabels" with
  | none => ⟨[], 0, []⟩
  | some root =>
    let st := treeWalk doc limits numberTree none root
    let r := rangesOf doc limits st.out.reverse
    ⟨r.1, st.warnings + r.2, st.visited⟩

/-- The range for page `i`: the greatest start `≤ i`, the later one on ties. -/
def rangeFor (rs : List LabelRange) (i : Nat) : Option LabelRange :=
  rs.foldl (fun best r =>
    if r.start ≤ i then
      match best with
      | some b => if b.start ≤ r.start then some r else best
      | none => some r
    else best) none

/-- The label of page `i` from a table (decimal `i + 1` if no range applies). -/
def LabelTable.label (t : LabelTable) (i : Nat) : List UInt8 :=
  match rangeFor t.ranges i with
  | some r => formatLabel r i
  | none => digits (i + 1)

/-- **The label of page `i`** (rule N8). -/
def pageLabel (doc : Doc) (limits : Limits) (i : Nat) : List UInt8 :=
  (labelTable doc limits).label i

/-- The labels of all pages, with one tree enumeration. -/
def pageLabels (doc : Doc) (limits : Limits) : List (List UInt8) :=
  let t := labelTable doc limits
  (List.range doc.pages.size).map t.label

/-! ## Theorems -/

/-- A reference popped by `popFresh` was not visited. -/
theorem popFresh_fresh {visited : List Nat} :
    ∀ {s : List PdfObject} {w w' n g : Nat} {rest : List PdfObject},
      popFresh visited s w = (some (n, g, rest), w') → n ∉ visited
  | [], _, _, _, _, _, h => by simp [popFresh] at h
  | .ref m k :: s, w, w', n, g, rest, h => by
    unfold popFresh at h
    split at h
    · exact popFresh_fresh h
    · next hm => cases h; exact hm
  | .null :: s, _, _, _, _, _, h | .bool _ :: s, _, _, _, _, _, h
  | .int _ :: s, _, _, _, _, _, h | .real _ :: s, _, _, _, _, _, h
  | .string _ :: s, _, _, _, _, _, h | .name _ :: s, _, _, _, _, _, h
  | .array _ :: s, _, _, _, _, _, h | .dict _ :: s, _, _, _, _, _, h => by
    unfold popFresh at h; exact popFresh_fresh h

/-- Visiting a node does not change the visited list. -/
theorem visitTree_visited {K : Type} (doc : Doc) (limits : Limits) (spec : TreeSpec K)
    (want : Option K) (nd : Dict) (st : TreeState K) :
    (visitTree doc limits spec want nd st).visited = st.visited := rfl

/-- **Tree loop invariant**: the visited list stays duplicate-free and grows by at most one
node per unit of fuel. -/
theorem treeLoop_inv {K : Type} (doc : Doc) (limits : Limits) (spec : TreeSpec K)
    (want : Option K) :
    ∀ (f : Nat) (st : TreeState K), st.visited.Nodup →
      (treeLoop doc limits spec want f st).visited.Nodup ∧
      (treeLoop doc limits spec want f st).visited.length ≤ st.visited.length + f
  | 0, st, h => by
    unfold treeLoop
    split <;> exact ⟨h, by simp⟩
  | f + 1, st, h => by
    unfold treeLoop
    split
    · exact ⟨h, by omega⟩
    · split
      · exact ⟨h, by simp⟩
      · next n g rest w hp =>
        have hf := popFresh_fresh hp
        have hnd : (n :: st.visited).Nodup := List.nodup_cons.2 ⟨hf, h⟩
        split
        · next nd _ =>
          have := treeLoop_inv doc limits spec want f
            (visitTree doc limits spec want nd
              { st with stack := rest, visited := n :: st.visited, warnings := w }) hnd
          simp only [visitTree_visited, List.length_cons] at this
          exact ⟨this.1, by omega⟩
        · have := treeLoop_inv doc limits spec want f
            { st with stack := rest, visited := n :: st.visited, warnings := w + 1 } hnd
          simp only [List.length_cons] at this
          exact ⟨this.1, by omega⟩

/-- The tree loop from an empty visited list. -/
theorem treeLoop_nil {K : Type} (doc : Doc) (limits : Limits) (spec : TreeSpec K)
    (want : Option K) (f : Nat) (st : TreeState K) (h : st.visited = []) :
    (treeLoop doc limits spec want f st).visited.Nodup ∧
    (treeLoop doc limits spec want f st).visited.length ≤ f := by
  have := treeLoop_inv doc limits spec want f st (h ▸ List.nodup_nil)
  rw [h] at this
  simpa using this

/-- **Tree work bound** (Plan.md §5.2): a tree walk visits at most `objectCount` nodes. -/
theorem treeWalk_visited_le {K : Type} (doc : Doc) (limits : Limits) (spec : TreeSpec K)
    (want : Option K) (root : PdfObject) :
    (treeWalk doc limits spec want root).visited.length ≤ doc.file.objectCount := by
  unfold treeWalk
  split
  · exact (treeLoop_nil doc limits spec want _ _ rfl).2
  · exact (treeLoop_nil doc limits spec want _ _ rfl).2
  · simp [TreeState.empty]
  · simp [TreeState.empty]

/-- **No node visited twice** in a tree walk. -/
theorem treeWalk_nodup {K : Type} (doc : Doc) (limits : Limits) (spec : TreeSpec K)
    (want : Option K) (root : PdfObject) :
    (treeWalk doc limits spec want root).visited.Nodup := by
  unfold treeWalk
  split
  · exact (treeLoop_nil doc limits spec want _ _ rfl).1
  · exact (treeLoop_nil doc limits spec want _ _ rfl).1
  · exact List.nodup_nil
  · exact List.nodup_nil

/-- A named-destination lookup in the name tree visits at most `objectCount` nodes. -/
theorem destsTree_visited_le (doc : Doc) (limits : Limits) (s : List UInt8) :
    (treeWalk doc limits nameTree (some s) (destsRoot doc limits)).visited.length ≤
      doc.file.objectCount :=
  treeWalk_visited_le doc limits nameTree (some s) _

/-- A reference popped by `popOutline` was not seen. -/
theorem popOutline_fresh {l : List Nat} {seen : VSet l} :
    ∀ {s : List (PdfObject × Nat)} {w w' n g dp : Nat} {rest : List (PdfObject × Nat)},
      popOutline l seen s w = (some (n, g, dp, rest), w') → n ∉ l
  | [], _, _, _, _, _, _, h => by simp [popOutline] at h
  | (.ref m k, d) :: s, w, w', n, g, dp, rest, h => by
    unfold popOutline at h
    split at h
    · exact popOutline_fresh h
    · next hm =>
      cases h
      exact fun hmem => hm ((seen.has_iff _).2 hmem)
  | (.null, _) :: s, _, _, _, _, _, _, h | (.bool _, _) :: s, _, _, _, _, _, _, h
  | (.int _, _) :: s, _, _, _, _, _, _, h | (.real _, _) :: s, _, _, _, _, _, _, h
  | (.string _, _) :: s, _, _, _, _, _, _, h | (.name _, _) :: s, _, _, _, _, _, _, h
  | (.array _, _) :: s, _, _, _, _, _, _, h | (.dict _, _) :: s, _, _, _, _, _, _, h => by
    unfold popOutline at h; exact popOutline_fresh h

/-- **Outline loop invariant**: visited items are duplicate-free and disjoint from the root,
at most one item is visited per unit of fuel, and there are no more items than visited
nodes. -/
theorem outlineLoop_inv (doc : Doc) (limits : Limits) (root : List Nat) :
    ∀ (f : Nat) (st : OutlineState doc.pages.size root),
      st.visited.Nodup → st.items.length ≤ st.visited.length →
      (outlineLoop doc limits root f st).visited.Nodup ∧
      (outlineLoop doc limits root f st).visited.length ≤ st.visited.length + f ∧
      (outlineLoop doc limits root f st).items.length ≤
        (outlineLoop doc limits root f st).visited.length
  | 0, st, h, hi => by
    unfold outlineLoop
    split <;> exact ⟨h, by simp, hi⟩
  | f + 1, st, h, hi => by
    unfold outlineLoop
    split
    · exact ⟨h, by simp, hi⟩
    · next n g dp rest w hp =>
      have hf : n ∉ st.visited := fun hm =>
        popOutline_fresh hp (List.mem_append_left _ hm)
      have hnd : (n :: st.visited).Nodup := List.nodup_cons.2 ⟨hf, h⟩
      split
      · next nd _ =>
        have := outlineLoop_inv doc limits root f
          { stack := outlineKids nd dp ++ rest, visited := n :: st.visited,
            seen := st.seen.insert n,
            items := outlineItem doc limits n g dp nd :: st.items, warnings := w } hnd
          (by simp only [List.length_cons]; omega)
        simp only [List.length_cons] at this
        exact ⟨this.1, by omega, this.2.2⟩
      · have := outlineLoop_inv doc limits root f
          { stack := rest, visited := n :: st.visited, seen := st.seen.insert n,
            items := st.items, warnings := w + 1 } hnd
          (by simp only [List.length_cons]; omega)
        simp only [List.length_cons] at this
        exact ⟨this.1, by omega, this.2.2⟩

/-- The outline of a loop run from one root item. -/
theorem outline_ofState_inv (doc : Doc) (limits : Limits) (root : List Nat) (f : PdfObject) :
    let o := Outline.ofState
      (outlineLoop doc limits root doc.file.objectCount ⟨[(f, 0)], [], rootSeen root, [], 0⟩)
    o.visited.Nodup ∧ o.visited.length ≤ doc.file.objectCount ∧
    o.items.length ≤ o.visited.length := by
  have := outlineLoop_inv doc limits root doc.file.objectCount
    ⟨[(f, 0)], [], rootSeen root, [], 0⟩ List.nodup_nil (by simp)
  simp only [Outline.ofState, List.length_reverse, List.length_nil, Nat.zero_add] at this ⊢
  exact this

/-- The outline's visited items are duplicate-free, at most `objectCount`, and bound the items. -/
theorem outline_inv (doc : Doc) (limits : Limits) :
    (outline doc limits).visited.Nodup ∧
    (outline doc limits).visited.length ≤ doc.file.objectCount ∧
    (outline doc limits).items.length ≤ (outline doc limits).visited.length := by
  unfold outline
  split
  · simp
  · split
    · split
      · exact outline_ofState_inv doc limits _ _
      · simp
    · simp
    · simp

/-- **Outline work bound**: at most `objectCount` items are visited. -/
theorem outline_visited_le (doc : Doc) (limits : Limits) :
    (outline doc limits).visited.length ≤ doc.file.objectCount :=
  (outline_inv doc limits).2.1

/-- **No outline item visited twice** (cycles are cut). -/
theorem outline_nodup (doc : Doc) (limits : Limits) : (outline doc limits).visited.Nodup :=
  (outline_inv doc limits).1

/-- Every outline item comes from a distinct visit. -/
theorem outline_items_le_visited (doc : Doc) (limits : Limits) :
    (outline doc limits).items.length ≤ (outline doc limits).visited.length :=
  (outline_inv doc limits).2.2

/-- **Outline size bound**: at most `objectCount` items. -/
theorem outline_items_le (doc : Doc) (limits : Limits) :
    (outline doc limits).items.length ≤ doc.file.objectCount :=
  Nat.le_trans (outline_items_le_visited doc limits) (outline_visited_le doc limits)

/-- **Page-label work bound**: the label tree walk visits at most `objectCount` nodes. -/
theorem labelTable_visited_le (doc : Doc) (limits : Limits) :
    (labelTable doc limits).visited.length ≤ doc.file.objectCount := by
  unfold labelTable
  split
  · simp
  · exact treeWalk_visited_le doc limits numberTree none _

/-- No page-label tree node is visited twice. -/
theorem labelTable_nodup (doc : Doc) (limits : Limits) : (labelTable doc limits).visited.Nodup := by
  unfold labelTable
  split
  · exact List.nodup_nil
  · exact treeWalk_nodup doc limits numberTree none _

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

/-- Test helper: run a check on the opened document. -/
private def withDoc (b : ByteArray) (p : Doc → Bool) : Bool :=
  match openDoc Limits.default b with
  | .ok doc => p doc
  | .error _ => false

/-- Test helper: bytes of a string. -/
private def B (s : String) : List UInt8 := s.toUTF8.toList

/-- Test helper: a target as (page index, name, fit). -/
private def tp {n : Nat} : Target n → Option Nat × Option (List UInt8) × Option Fit
  | .dest d => (d.page.map Fin.val, d.name, some d.fit)
  | .unresolved s => (none, some s, none)
  | _ => (none, none, none)

/-- Test helper: the outline as (title, depth, page). -/
private def ol (doc : Doc) : List (List UInt8 × Nat × Option Nat) :=
  (outline doc Limits.default).items.map fun it => (it.title, it.depth, (tp it.target).1)

/-- Test helper: decimal. -/
private def Dc (i : Int) : Option Decimal := some ⟨i, 0⟩

/-- Four pages, a nested outline, `/Dests`, a two-level name tree, page labels, links. -/
private def navPdf : ByteArray := mkPdf [
  "<< /Type /Catalog /Pages 2 0 R /Outlines 7 0 R /Dests 11 0 R /Names << /Dests 12 0 R >> " ++
    "/PageLabels << /Nums [0 << /S /r >> 2 << /S /D /St 1 /P (A-) >>] >> >>",
  "<< /Type /Pages /Kids [3 0 R 4 0 R 5 0 R 6 0 R] /Count 4 /MediaBox [0 0 612 792] >>",
  "<< /Type /Page /Parent 2 0 R /Annots [16 0 R 17 0 R 18 0 R] >>",
  "<< /Type /Page /Parent 2 0 R >>",
  "<< /Type /Page /Parent 2 0 R >>",
  "<< /Type /Page /Parent 2 0 R >>",
  "<< /Type /Outlines /First 8 0 R /Last 9 0 R /Count 3 >>",
  "<< /Title (Chapter 1) /Parent 7 0 R /Next 9 0 R /First 10 0 R /Last 10 0 R " ++
    "/Dest [3 0 R /XYZ 0 792 null] /Count 1 >>",
  "<< /Title (Chapter 2) /Parent 7 0 R /Prev 8 0 R /Dest /intro >>",
  "<< /Title (Section 1.1) /Parent 8 0 R /A << /S /GoTo /D (zeta) >> >>",
  "<< /intro [5 0 R /Fit] /second << /D [4 0 R /XYZ 10 20 0] >> >>",
  "<< /Kids [13 0 R 14 0 R] >>",
  "<< /Limits [(alpha) (beta)] /Names [(alpha) [3 0 R /Fit] (beta) 15 0 R] >>",
  "<< /Limits [(gamma) (zeta)] /Names [(gamma) [5 0 R /FitR 1 2 3 4] (zeta) [6 0 R /FitV 5]] >>",
  "<< /D [4 0 R /FitB] >>",
  "<< /Type /Annot /Subtype /Link /Rect [100 30 10 10] /A << /S /GoTo /D [4 0 R /Fit] >> >>",
  "<< /Type /Annot /Subtype /Link /Rect [0 0 5 5] /A << /S /URI /URI (http://x) >> >>",
  "<< /Type /Annot /Subtype /Text /Rect [0 0 5 5] >>"]

-- Nested outline, preorder with depths; targets via explicit, name-tree and `/Dests` names.
#guard withDoc navPdf fun doc =>
  ol doc == [(B "Chapter 1", 0, some 0), (B "Section 1.1", 1, some 3), (B "Chapter 2", 0, some 2)]
  && (outline doc Limits.default).warnings == 0
  && ((outline doc Limits.default).items.map (fun it => (tp it.target).2.2)) ==
    [some (.xyz (Dc 0) (Dc 792) none), some (.fitV (Dc 5)), some .fit]
  && ((outline doc Limits.default).items.map OutlineItem.count) == [some 1, none, none]

-- Named destinations: `/Dests` dictionary (array value, `/D` dictionary value).
#guard withDoc navPdf fun doc =>
  tp (resolveDest doc Limits.default (.name (Name.ofString "intro"))) ==
    (some 2, some (B "intro"), some .fit) &&
  tp (resolveDest doc Limits.default (.name (Name.ofString "second"))) ==
    (some 1, some (B "second"), some (.xyz (Dc 10) (Dc 20) (Dc 0)))

-- Name tree, two levels with `/Limits`: lookups (array, `/D` dictionary), missing name.
#guard withDoc navPdf fun doc =>
  tp (resolveDest doc Limits.default (.string (B "alpha"))) == (some 0, some (B "alpha"), some .fit) &&
  tp (resolveDest doc Limits.default (.string (B "beta"))) == (some 1, some (B "beta"), some .fitB) &&
  tp (resolveDest doc Limits.default (.string (B "zeta"))) ==
    (some 3, some (B "zeta"), some (.fitV (Dc 5))) &&
  resolveDest doc Limits.default (.string (B "nope")) == .unresolved (B "nope") &&
  -- a name is found in the tree when `/Dests` lacks it
  (tp (resolveDest doc Limits.default (.name (Name.ofString "alpha")))).1 == some 0

-- `/Limits` pruning: looking up `alpha` stops after the first leaf; `zeta` fetches the first
-- leaf (to read its `/Limits`) but collects nothing from it; `delta` lies between the leaves.
#guard withDoc navPdf fun doc =>
  (treeWalk doc Limits.default nameTree (some (B "alpha")) (destsRoot doc Limits.default)).visited
    == [13, 12] &&
  (treeWalk doc Limits.default nameTree (some (B "zeta")) (destsRoot doc Limits.default)).out.length
    == 1 &&
  treeLookup doc Limits.default nameTree (destsRoot doc Limits.default) (B "delta") == none &&
  (treeEntries doc Limits.default nameTree (destsRoot doc Limits.default)).map Prod.fst ==
    [B "alpha", B "beta", B "gamma", B "zeta"] &&
  tp (resolveDest doc Limits.default (.string (B "gamma"))) ==
    (some 2, some (B "gamma"), some (.fitR (Dc 1) (Dc 2) (Dc 3) (Dc 4)))

-- Page labels: `/S /r`, then `/S /D /St 1 /P (A-)`.
#guard withDoc navPdf fun doc =>
  pageLabels doc Limits.default == [B "i", B "ii", B "A-1", B "A-2"] &&
  pageLabel doc Limits.default 2 == B "A-1" &&
  (labelTable doc Limits.default).warnings == 0

-- URI actions keep their string; a missing or over-long string leaves a bare action.
#guard withDoc navPdf fun doc => resolveAction doc Limits.default
    (.dict [(Name.ofString "S", .name (Name.ofString "URI")), (Name.ofString "URI", .string (B "a(b)"))]) ==
  .uri (B "a(b)")
#guard withDoc navPdf fun doc => resolveAction doc Limits.default
    (.dict [(Name.ofString "S", .name (Name.ofString "URI"))]) == .action (B "URI")
#guard withDoc navPdf fun doc => resolveAction doc Limits.default
    (.dict [(Name.ofString "S", .name (Name.ofString "URI")),
            (Name.ofString "URI", .string (List.replicate (maxUriBytes + 1) 0x61))]) == .action (B "URI")
#guard withDoc navPdf fun doc => resolveAction doc Limits.default
    (.dict [(Name.ofString "S", .name (Name.ofString "URI")),
            (Name.ofString "URI", .string (List.replicate maxUriBytes 0x61))]) ==
  .uri (List.replicate maxUriBytes 0x61)

-- Links on page 0: a GoTo link (rect normalized), a URI link kept as an action; the text
-- annotation is skipped. Page 1 has none.
#guard withDoc navPdf fun doc =>
  if h : 1 < doc.pages.size then
    (pageLinks doc Limits.default ⟨0, by omega⟩).map (fun l => (tp l.target, l.target)) ==
      [((some 1, none, some .fit), (resolveAction doc Limits.default
          (.dict [(Name.ofString "S", .name (Name.ofString "GoTo")),
                  (Name.ofString "D", .array [.ref 4 0, .name (Name.ofString "Fit")])]))),
       ((none, none, none), .uri (B "http://x"))] &&
    (pageLinks doc Limits.default ⟨0, by omega⟩).map (fun l => (l.rect.llx, l.rect.lly, l.rect.urx,
      l.rect.ury)) == [(⟨10, 0⟩, ⟨10, 0⟩, ⟨100, 0⟩, ⟨30, 0⟩), (⟨0, 0⟩, ⟨0, 0⟩, ⟨5, 0⟩, ⟨5, 0⟩)] &&
    (pageLinks doc Limits.default ⟨1, h⟩).isEmpty
  else false

/-- A two-page document with outline items `items` (objects 5 …) under root 4. -/
private def outlinePdf (items : List String) : ByteArray := mkPdf ([
  "<< /Type /Catalog /Pages 2 0 R /Outlines 4 0 R >>",
  "<< /Type /Pages /Kids [3 0 R] /Count 1 >>",
  "<< /Type /Page /Parent 2 0 R >>",
  "<< /Type /Outlines /First 5 0 R >>"] ++ items)

-- An outline `/Next` cycle: 5 → 6 → 5 is cut once.
#guard withDoc (outlinePdf [
    "<< /Title (A) /Next 6 0 R /Dest [3 0 R /Fit] >>",
    "<< /Title (B) /Next 5 0 R >>"]) fun doc =>
  ol doc == [(B "A", 0, some 0), (B "B", 0, none)] && (outline doc Limits.default).warnings == 1

-- A `/First` pointing to an ancestor (5 → 6 → 5), and one pointing to the outline root.
#guard withDoc (outlinePdf [
    "<< /Title (A) /First 6 0 R >>",
    "<< /Title (A.1) /First 5 0 R /Next 7 0 R >>",
    "<< /Title (A.2) /First 4 0 R >>"]) fun doc =>
  ol doc == [(B "A", 0, none), (B "A.1", 1, none), (B "A.2", 1, none)] &&
  (outline doc Limits.default).warnings == 2

-- A self-loop `/Next` and a dangling item reference.
#guard withDoc (outlinePdf [
    "<< /Title (A) /Next 5 0 R /First 99 0 R >>"]) fun doc =>
  ol doc == [(B "A", 0, none)] && (outline doc Limits.default).warnings == 2

-- No outline at all.
#guard withDoc (mkPdf [
    "<< /Type /Catalog /Pages 2 0 R >>",
    "<< /Type /Pages /Kids [3 0 R] /Count 1 >>",
    "<< /Type /Page /Parent 2 0 R >>"]) fun doc =>
  (outline doc Limits.default).items.isEmpty && pageLabels doc Limits.default == [B "1"]

-- A name tree whose kid points back at the root (cycle cut, counted), and a non-reference kid.
#guard withDoc (mkPdf [
    "<< /Type /Catalog /Pages 2 0 R /Names << /Dests 4 0 R >> >>",
    "<< /Type /Pages /Kids [3 0 R] /Count 1 >>",
    "<< /Type /Page /Parent 2 0 R >>",
    "<< /Kids [5 0 R 4 0 R 7] >>",
    "<< /Names [(x) [3 0 R /FitH 7] (y)] /Kids [4 0 R] >>"]) fun doc =>
  let st := treeWalk doc Limits.default nameTree none (destsRoot doc Limits.default)
  st.out.map Prod.fst == [B "x"] && st.warnings == 4 && st.visited == [5, 4] &&
  tp (resolveDest doc Limits.default (.string (B "x"))) == (some 0, some (B "x"), some (.fitH (Dc 7)))

-- Page labels with an indirect number tree (two levels), letters and a prefix-only range.
#guard withDoc (mkPdf [
    "<< /Type /Catalog /Pages 2 0 R /PageLabels 7 0 R >>",
    "<< /Type /Pages /Kids [3 0 R 4 0 R 5 0 R 6 0 R] /Count 4 >>",
    "<< /Type /Page /Parent 2 0 R >>",
    "<< /Type /Page /Parent 2 0 R >>",
    "<< /Type /Page /Parent 2 0 R >>",
    "<< /Type /Page /Parent 2 0 R >>",
    "<< /Kids [8 0 R 9 0 R] >>",
    "<< /Limits [0 1] /Nums [0 << /S /A /St 26 >>] >>",
    "<< /Limits [3 3] /Nums [3 << /P (Cover) >>] >>"]) fun doc =>
  pageLabels doc Limits.default == [B "Z", B "AA", B "BB", B "Cover"] &&
  (labelTable doc Limits.default).visited == [9, 8, 7]

-- Label formatting.
#guard toLetters 1 == B "A" && toLetters 26 == B "Z" && toLetters 27 == B "AA" &&
  toLetters 28 == B "BB" && toLetters 52 == B "ZZ" && toLetters 53 == B "AAA"
#guard lower (toLetters 27) == B "aa"
#guard toRoman 1 == B "I" && toRoman 4 == B "IV" && toRoman 9 == B "IX" && toRoman 14 == B "XIV" &&
  toRoman 40 == B "XL" && toRoman 90 == B "XC" && toRoman 400 == B "CD" &&
  toRoman 1994 == B "MCMXCIV" && toRoman 2024 == B "MMXXIV" && toRoman 3999 == B "MMMCMXCIX"
#guard lower (toRoman 3) == B "iii"
#guard toRoman 4000 == B "4000" && toRoman 0 == B "0" && toLetters 4000 == B "4000"
#guard formatLabel ⟨5, .decimal, B "p-", 10⟩ 7 == B "p-12"
#guard formatLabel ⟨0, .none, B "Cover", 1⟩ 0 == B "Cover"
#guard rangeFor [⟨0, .romanLower, [], 1⟩, ⟨2, .decimal, [], 1⟩] 1 ==
  some ⟨0, .romanLower, [], 1⟩

/-- Test helper: the value of a roman numeral (subtractive rule). -/
private def fromRoman (bs : List UInt8) : Nat :=
  let v : UInt8 → Nat := fun c =>
    if c = 73 then 1 else if c = 86 then 5 else if c = 88 then 10 else if c = 76 then 50
    else if c = 67 then 100 else if c = 68 then 500 else if c = 77 then 1000 else 0
  let rec go : List UInt8 → Int
    | [] => 0
    | [a] => v a
    | a :: b :: rest => (if v a < v b then -(v a : Int) else v a) + go (b :: rest)
  (go bs).toNat

/-- Test helper: canonical roman numerals use only `IVXLCDM` with at most three repeats. -/
private def canonicalRoman (bs : List UInt8) : Bool :=
  bs.all (fun c => c ∈ B "IVXLCDM") && !(String.fromUTF8? ⟨bs.toArray⟩ |>.map
    (fun s => ["IIII", "XXXX", "CCCC", "MMMM", "VV", "LL", "DD"].any (fun p => (s.splitOn p).length > 1))
    |>.getD true)

-- `toRoman` on all of 1..3999: canonical shape, and the value round-trips.
#guard (List.range 3999).all fun k => fromRoman (toRoman (k + 1)) == k + 1
#guard (List.range 3999).all fun k => canonicalRoman (toRoman (k + 1))

end Tests

end SafePdf.Core.Doc.Nav
