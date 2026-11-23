import SafePdf.Core.Object
import SafePdf.Core.Limits

/-!
# Optional content (task 9.r11a)

Plan.md §6 Phase 9 (the viewer: "optional content", ledger rows 9.r11a/9.r11b), §4 S2
(totality), §5.2 (bounded work: fuel or a budget on every recursion). ISO 32000-2 §8.11
(optional content): §8.11.2 (groups and membership dictionaries, visibility expressions),
§8.11.3 (making graphical content optional), §8.11.4 (configuring optional content: the
catalog's `/OCProperties`, the default configuration `/D`).

This module is the **pure model**; it does not depend on `Core.Doc` or `Core.Content`, so the
content runner (`Core.Content.Run`) can use it. Every function takes a one-level resolver
`R : σ → PdfObject → PdfObject × σ` (the runner's `Run.resolve src`, threading the source
state, e.g. the document budget).

## Model

* **Groups** are identified by their indirect reference (`Key`); an optional content group
  is always an indirect object (§8.11.2.1).
* **`Config`** (`read`): the catalog's `/OCProperties` — its `/OCGs` (at most
  `Limits.maxOCGroups`, duplicates dropped, non-references ignored) with each group's `/Name`
  and whether its `/Usage /View /ViewState` is `/OFF`; the default configuration `/D` with
  `/Name`, `/BaseState` (`ON`, `OFF`, `Unchanged`; anything else `ON`), `/ON`, `/OFF`,
  `/Order` (nested arrays with optional string labels, for the layers panel of task 9.r11b;
  `orderOf`), `/RBGroups` and `/Locked`. No `/OCProperties`, or no group in `/OCGs`: `none`.
* **`State`**: the groups known (`known`) and the set of groups that are OFF (`off`). The
  default state (`Config.initial`, `stateOf`) is the `/D` configuration: `/BaseState` for every
  group (`Unchanged` counts as `ON` in the default configuration, §8.11.4.3), then `/ON`, then
  `/OFF` (an `/OFF` entry wins over an `/ON` one), and a group whose `/Usage /View /ViewState`
  is `/OFF` starts OFF (as PDF.js's `OptionalContentGroup.visible` for display, and MuPDF). A
  later layers panel changes the state (`State.set`, `Config.setGroup` with radio-button
  groups) and renders again.
* **Visibility** (`isVisible`, `visible`): with no known group (no `/OCProperties`) everything
  is visible (`isVisible_inactive`). Otherwise:
  * a reference to a known group: visible iff it is not OFF;
  * a membership dictionary (`/Type /OCMD`, §8.11.2.2): a `/VE` visibility expression, when it
    is an array starting with `/And`, `/Or` or `/Not`, takes precedence; else `/P`
    (`AllOn`, `AnyOff`, `AllOff`, default `AnyOn`) over `/OCGs` (one reference or an array);
    entries that are not known groups are ignored, and with none left the dictionary is
    visible (§8.11.2.2: "no effect on visibility");
  * a visibility expression: `[/And e …]` (all), `[/Or e …]` (any), `[/Not e]`; operands are
    group references or nested expressions (direct or by reference); a malformed expression
    (unknown operator, no operand, `/Not` with several) is visible;
  * anything else — a reference to an object that is not a known group or a membership
    dictionary, a group not listed in `/OCGs`, a name, `null` — is **visible** (the spec's
    "treat as visible"; PDF.js warns and shows it);
  * recursion (references followed, nested expressions) is bounded by **fuel**
    `Limits.maxOCDepth`; exhausted fuel is visible, so a reference cycle terminates.

## Theorems

* `isVisible_inactive`: with no known group, everything is visible and the source state is
  untouched (the basis of "no `/OCProperties` → output unchanged", see `Core.Content.Run`).
* `State.set_known`: changing a group's state keeps the known groups.
* `orderOf_count_le`: reading `/Order` consumes at most the given item budget.
-/

set_option autoImplicit false

namespace SafePdf.Core.Doc.OptionalContent

open SafePdf

/-- A name from a string. -/
def nm (s : String) : Name := Name.ofString s

/-- An optional content group's identity: its object number and generation. -/
abbrev Key := Nat × Nat

/-- The key of a reference. -/
def refKey : PdfObject → Option Key
  | .ref n g => some (n, g)
  | _ => none

/-! ## Visibility state -/

/-- **The visibility state**: the groups of the document (`/OCProperties /OCGs`) and the set
of groups that are OFF. The default value (no groups) makes everything visible. -/
structure State where
  /-- The optional content groups of the document (`/OCGs`), in order. -/
  known : List Key := []
  /-- The groups that are OFF. -/
  off : List Key := []
  deriving Repr, Inhabited, BEq, DecidableEq

/-- Whether group `k` is ON in state `st` (an unknown group counts as ON). -/
def State.isOn (st : State) (k : Key) : Bool := !st.off.contains k

/-- Turn group `k` ON (`on = true`) or OFF. Unknown groups are left alone (they are always
visible). -/
def State.set (st : State) (k : Key) (on : Bool) : State :=
  if !st.known.contains k then st
  else if on then { st with off := st.off.filter (· != k) }
  else if st.off.contains k then st
  else { st with off := k :: st.off }

/-- Changing a group's state keeps the known groups. -/
theorem State.set_known (st : State) (k : Key) (on : Bool) : (st.set k on).known = st.known := by
  unfold State.set
  split
  · rfl
  · split
    · rfl
    · split <;> rfl

/-! ## Configuration -/

/-- `/BaseState` of a configuration (§8.11.4.3). -/
inductive BaseState where
  /-- Every group starts ON. -/
  | on
  /-- Every group starts OFF. -/
  | off
  /-- Groups keep their state (`Unchanged`; ON in the default configuration). -/
  | unchanged
  deriving Repr, Inhabited, BEq, DecidableEq

/-- One entry of `/Order` (§8.11.4.3, Table 101): a group, or a nested list with an optional
label (a text string, raw bytes). -/
inductive Order where
  /-- A group, shown at this place. -/
  | group (k : Key)
  /-- A nested list (an array; its first element, when a string, is its label). -/
  | node (label : Option (List UInt8)) (kids : List Order)
  deriving Repr, Inhabited

/-- One optional content group of `/OCGs`. -/
structure Group where
  /-- Its reference. -/
  key : Key
  /-- Its `/Name` (a text string, raw bytes; empty when absent). -/
  name : List UInt8 := []
  /-- Its `/Usage /View /ViewState` is `/OFF` (it starts OFF). -/
  viewOff : Bool := false
  deriving Repr, Inhabited, BEq

/-- The optional content of a document: its groups and the default configuration `/D`. -/
structure Config where
  /-- The groups (`/OCGs`), in order, without duplicates, at most `Limits.maxOCGroups`. -/
  groups : List Group := []
  /-- `/D /Name` (raw bytes). -/
  name : List UInt8 := []
  /-- `/D /BaseState`. -/
  baseState : BaseState := .on
  /-- `/D /ON`. -/
  onList : List Key := []
  /-- `/D /OFF`. -/
  offList : List Key := []
  /-- `/D /Order` (for the layers panel). -/
  order : List Order := []
  /-- `/D /RBGroups`: radio-button groups (at most one ON). -/
  rbGroups : List (List Key) := []
  /-- `/D /Locked`: groups the user may not change. -/
  locked : List Key := []
  deriving Repr, Inhabited

/-- Whether group `g` starts ON in the default configuration (see the module doc). -/
def Config.initialOn (c : Config) (g : Group) : Bool :=
  let base := if c.offList.contains g.key then false
    else if c.onList.contains g.key then true
    else c.baseState != .off
  base && !g.viewOff

/-- **The default visibility state** of a configuration. -/
def Config.initial (c : Config) : State :=
  { known := c.groups.map (·.key), off := (c.groups.filter (!c.initialOn ·)).map (·.key) }

/-- The default state of an optional configuration: no configuration → everything visible. -/
def stateOf : Option Config → State
  | some c => c.initial
  | none => {}

/-- Turn group `k` ON or OFF in `st` as a layers panel does: locked groups stay as they are;
turning a group ON turns OFF the other groups of every radio-button group containing it. -/
def Config.setGroup (c : Config) (st : State) (k : Key) (on : Bool) : State :=
  if c.locked.contains k then st
  else if on then
    let others := (c.rbGroups.filter (·.contains k)).flatten.filter (· != k)
    (others.foldl (fun st o => st.set o false) st).set k true
  else st.set k false

/-! ## Reading `/OCProperties` -/

section Read

variable {σ : Type} (R : σ → PdfObject → PdfObject × σ)

/-- An optional entry resolved one level (`null` when absent). -/
def get (s : σ) (d : Dict) (k : String) : PdfObject × σ :=
  match Dict.get? d (nm k) with
  | some o => R s o
  | none => (.null, s)

/-- The references of an array entry (resolved one level), as keys. -/
def keysOf (s : σ) (d : Dict) (k : String) : List Key × σ :=
  match get R s d k with
  | (.array xs, s) => (xs.filterMap refKey, s)
  | (_, s) => ([], s)

/-- Keep the first occurrence of each key. -/
def dedup (ks : List Key) : List Key :=
  (ks.foldl (fun (acc : List Key) k => if acc.contains k then acc else k :: acc) []).reverse

/-- A nested `/Order` array `ys` as a node (its first element, when a string, is the label),
its elements read by `rec` with item budget `n`. -/
def orderNode (rec : Nat → σ → List PdfObject → List Order × Nat × σ) (n : Nat) (s : σ)
    (ys : List PdfObject) : Order × Nat × σ :=
  match ys with
  | .string l :: rest =>
    let r := rec n s rest
    (Order.node (some l) r.1, r.2.1, r.2.2)
  | _ =>
    let r := rec n s ys
    (Order.node none r.1, r.2.1, r.2.2)

/-- One element of an `/Order` array (items in reverse, item budget, source state); nested
arrays are read by `rec`. Each element visited costs one item of the budget. -/
def orderStep (known : List Key) (rec : Nat → σ → List PdfObject → List Order × Nat × σ)
    (acc : List Order × Nat × σ) (x : PdfObject) : List Order × Nat × σ :=
  match acc with
  | (out, 0, s) => (out, 0, s)
  | (out, m + 1, s) =>
    match x with
    | .ref a b =>
      if known.contains (a, b) then (.group (a, b) :: out, m, s) else
      match R s x with
      | (.array ys, s) =>
        let r := orderNode rec m s ys
        (r.1 :: out, r.2.1, r.2.2)
      | (_, s) => (out, m, s)
    | .array ys =>
      let r := orderNode rec m s ys
      (r.1 :: out, r.2.1, r.2.2)
    | _ => (out, m, s)

/-- **`/Order`** (§8.11.4.3): the array's elements, with references to known groups as
groups, arrays (direct, or by reference) as nested nodes labelled by a leading string; other
elements are skipped. Nesting is bounded by `fuel` and the number of elements visited by the
item budget `n` (a shared, possibly indirect, array cannot fan out). Returns the items, the
budget left and the source state. -/
def orderOf (known : List Key) : Nat → Nat → σ → List PdfObject → List Order × Nat × σ
  | 0, n, s, _ => ([], n, s)
  | f + 1, n, s, xs =>
    let r := xs.foldl (orderStep R known (orderOf known f)) ([], n, s)
    (r.1.reverse, r.2.1, r.2.2)

/-- `orderNode` keeps a budget bound of `rec`. -/
theorem orderNode_le (rec : Nat → σ → List PdfObject → List Order × Nat × σ)
    (h : ∀ n s ys, (rec n s ys).2.1 ≤ n) (n : Nat) (s : σ) (ys : List PdfObject) :
    (orderNode rec n s ys).2.1 ≤ n := by
  unfold orderNode
  split
  · exact h _ _ _
  · exact h _ _ _

/-- `orderStep` never adds to the budget. -/
theorem orderStep_le (known : List Key) (rec : Nat → σ → List PdfObject → List Order × Nat × σ)
    (h : ∀ n s ys, (rec n s ys).2.1 ≤ n) (acc : List Order × Nat × σ) (x : PdfObject) :
    (orderStep R known rec acc x).2.1 ≤ acc.2.1 := by
  obtain ⟨out, k, s⟩ := acc
  unfold orderStep
  cases k with
  | zero => exact Nat.le_refl _
  | succ m =>
    simp only
    split
    · split
      · simp only; omega
      · split
        · exact Nat.le_succ_of_le (orderNode_le rec h _ _ _)
        · simp only; omega
    · exact Nat.le_succ_of_le (orderNode_le rec h _ _ _)
    · simp only; omega

/-- Reading `/Order` never adds to the item budget. -/
theorem orderOf_count_le (known : List Key) :
    ∀ (f n : Nat) (s : σ) (xs : List PdfObject), (orderOf R known f n s xs).2.1 ≤ n
  | 0, n, s, xs => by simp [orderOf]
  | f + 1, n, s, xs => by
    have ih := orderOf_count_le known f
    simp only [orderOf]
    have hf : ∀ (l : List PdfObject) (acc : List Order × Nat × σ),
        (l.foldl (orderStep R known (orderOf R known f)) acc).2.1 ≤ acc.2.1 := by
      intro l
      induction l with
      | nil => intro acc; exact Nat.le_refl _
      | cons x rest ihl =>
        intro acc
        simp only [List.foldl_cons]
        exact Nat.le_trans (ihl _) (orderStep_le R known _ ih acc x)
    exact hf xs ([], n, s)

/-- One group of `/OCGs`: its `/Name` and its `/Usage /View /ViewState`. -/
def groupOf (s : σ) (k : Key) : Group × σ :=
  match R s (.ref k.1 k.2) with
  | (.dict d, s) =>
    let (name, s) := match get R s d "Name" with
      | (.string b, s) => (b, s)
      | (_, s) => ([], s)
    let (vs, s) := match get R s d "Usage" with
      | (.dict u, s) =>
        match get R s u "View" with
        | (.dict v, s) =>
          match get R s v "ViewState" with
          | (.name n, s) => (decide (n = nm "OFF"), s)
          | (_, s) => (false, s)
        | (_, s) => (false, s)
      | (_, s) => (false, s)
    ({ key := k, name, viewOff := vs }, s)
  | (_, s) => ({ key := k }, s)

/-- **Read the optional content** of the catalog `cat` (see the module doc): `none` when there
is no `/OCProperties` dictionary or no group in its `/OCGs`. -/
def read (lim : Limits) (s : σ) (cat : Dict) : Option Config × σ :=
  match get R s cat "OCProperties" with
  | (.dict p, s) =>
    let (ks, s) := keysOf R s p "OCGs"
    let ks := (dedup (ks.take (4 * lim.maxOCGroups))).take lim.maxOCGroups
    if ks.isEmpty then (none, s) else
    let (groups, s) := ks.foldl (fun (acc : List Group × σ) k =>
      let (g, s) := groupOf R acc.2 k
      (g :: acc.1, s)) ([], s)
    let groups := groups.reverse
    let (d, s) := match get R s p "D" with
      | (.dict d, s) => (d, s)
      | (_, s) => ([], s)
    let (name, s) := match get R s d "Name" with
      | (.string b, s) => (b, s)
      | (_, s) => ([], s)
    let (base, s) := match get R s d "BaseState" with
      | (.name n, s) =>
        (if n = nm "OFF" then BaseState.off else if n = nm "Unchanged" then .unchanged else .on, s)
      | (_, s) => (.on, s)
    let (onL, s) := keysOf R s d "ON"
    let (offL, s) := keysOf R s d "OFF"
    let (lockedL, s) := keysOf R s d "Locked"
    let (rb, s) := match get R s d "RBGroups" with
      | (.array xs, s) => xs.foldl (fun (acc : List (List Key) × σ) x =>
          match R acc.2 x with
          | (.array ys, s) => ((ys.filterMap refKey) :: acc.1, s)
          | (_, s) => (acc.1, s)) ([], s)
      | (_, s) => ([], s)
    let (order, s) := match get R s d "Order" with
      | (.array xs, s) =>
        let r := orderOf R (groups.map (·.key)) lim.maxOCDepth lim.maxOCGroups s xs
        (r.1, r.2.2)
      | (_, s) => ([], s)
    (some { groups, name, baseState := base, onList := onL, offList := offL, order,
            rbGroups := rb.reverse, locked := lockedL }, s)
  | (_, s) => (none, s)

/-- **The default visibility state** of the catalog `cat` (`read`, then `stateOf`). -/
def defaultState (lim : Limits) (s : σ) (cat : Dict) : State × σ :=
  let (c, s) := read R lim s cat
  (stateOf c, s)

end Read

/-! ## Visibility -/

section Visible

variable {σ : Type} (R : σ → PdfObject → PdfObject × σ)

/-- The `/P` policy of a membership dictionary over the states (`true` = ON) of its groups. -/
def policy (p : Option Name) (ons : List Bool) : Bool :=
  if p = some (nm "AllOn") then ons.all id
  else if p = some (nm "AnyOff") then ons.any (!·)
  else if p = some (nm "AllOff") then ons.all (!·)
  else ons.any id

/-- Whether an object is a visibility expression array (`/And`, `/Or` or `/Not` first). -/
def isExpr : PdfObject → Bool
  | .array (.name op :: _) => op = nm "And" || op = nm "Or" || op = nm "Not"
  | _ => false

/-- **Visibility of optional content `o`** in state `st` (see the module doc), with fuel.
`ve`: `o` is an operand of a visibility expression (arrays are expressions, dictionaries are
not allowed there). -/
def visible (st : State) : Nat → Bool → σ → PdfObject → Bool × σ
  | 0, _, s, _ => (true, s)
  | f + 1, ve, s, o =>
    match o with
    | .ref n g =>
      if st.known.contains (n, g) then (st.isOn (n, g), s)
      else
        match R s o with
        | (.ref _ _, s) => (true, s)
        | (r, s) => visible st f ve s r
    | .array xs =>
      if !ve then (true, s) else
      match xs with
      | [.name op, a] =>
        if op = nm "Not" then
          let (v, s) := visible st f true s a
          (!v, s)
        else if op = nm "And" || op = nm "Or" then visible st f true s a
        else (true, s)
      | .name op :: a :: args =>
        if op = nm "And" then
          (a :: args).foldl (fun (acc : Bool × σ) x =>
            let (v, s) := visible st f true acc.2 x
            (acc.1 && v, s)) (true, s)
        else if op = nm "Or" then
          (a :: args).foldl (fun (acc : Bool × σ) x =>
            let (v, s) := visible st f true acc.2 x
            (acc.1 || v, s)) (false, s)
        else (true, s)
      | _ => (true, s)
    | .dict d =>
      if ve then (true, s) else
      match Dict.get? d (nm "Type") with
      | some (.name t) =>
        if t != nm "OCMD" then (true, s) else
        let (vexp, s) := get R s d "VE"
        if isExpr vexp then visible st f true s vexp else
        let (keys, s) := match Dict.get? d (nm "OCGs") with
          | some (.ref a b) =>
            if st.known.contains (a, b) then ([(a, b)], s) else
            match R s (.ref a b) with
            | (.array xs, s) => (xs.filterMap refKey, s)
            | (_, s) => ([], s)
          | some (.array xs) => (xs.filterMap refKey, s)
          | _ => ([], s)
        let ks := keys.filter st.known.contains
        if ks.isEmpty then (true, s) else
        let (p, s) := match get R s d "P" with
          | (.name p, s) => (some p, s)
          | (_, s) => (none, s)
        (policy p (ks.map st.isOn), s)
      | _ => (true, s)
    | _ => (true, s)

/-- **Visibility entry point**: everything is visible when no group is known (no
`/OCProperties`); else `visible` with fuel `Limits.maxOCDepth`. -/
def isVisible (lim : Limits) (st : State) (s : σ) (o : PdfObject) : Bool × σ :=
  if st.known.isEmpty then (true, s) else visible R st lim.maxOCDepth false s o

/-- **No optional content, no effect**: with no known group every object is visible and the
source state is untouched (nothing is fetched). -/
theorem isVisible_inactive (lim : Limits) (st : State) (s : σ) (o : PdfObject)
    (h : st.known = []) : isVisible R lim st s o = (true, s) := by
  simp [isVisible, h]

/-- The default state (`{}`) shows everything. -/
theorem isVisible_default (lim : Limits) (s : σ) (o : PdfObject) :
    isVisible R lim {} s o = (true, s) :=
  isVisible_inactive R lim {} s o rfl

end Visible

/-! ## Checks -/

section Checks

/-- A resolver over a fixed object table (for the checks). -/
private def tbl (objs : List (Nat × PdfObject)) : Unit → PdfObject → PdfObject × Unit
  | u, .ref n _ => ((objs.find? (·.1 == n)).map (·.2) |>.getD .null, u)
  | u, o => (o, u)

private def r (n : Nat) : PdfObject := .ref n 0
private def nmo (s : String) : PdfObject := .name (nm s)
private def ocmd (rest : List (Name × PdfObject)) : PdfObject :=
  .dict ((nm "Type", nmo "OCMD") :: rest)

-- groups 1 (ON), 2 (OFF); 3 is not a known group
private def st12 : State := { known := [(1, 0), (2, 0)], off := [(2, 0)] }
private def vis (o : PdfObject) (objs : List (Nat × PdfObject) := []) : Bool :=
  (isVisible (tbl objs) {} st12 () o).1

#guard vis (r 1) && !vis (r 2) && vis (r 3) && vis .null && vis (nmo "x")
#guard vis (ocmd [(nm "OCGs", .array [r 1, r 2])])                                -- AnyOn
#guard !vis (ocmd [(nm "OCGs", .array [r 1, r 2]), (nm "P", nmo "AllOn")])
#guard vis (ocmd [(nm "OCGs", .array [r 1, r 2]), (nm "P", nmo "AnyOff")])
#guard !vis (ocmd [(nm "OCGs", .array [r 1, r 2]), (nm "P", nmo "AllOff")])
#guard vis (ocmd [(nm "OCGs", r 2), (nm "P", nmo "AllOff")])
#guard !vis (ocmd [(nm "OCGs", r 2)])
#guard vis (ocmd [(nm "OCGs", .array [r 3])])                                     -- unknown only
-- /VE wins over /P
#guard !vis (ocmd [(nm "OCGs", r 1), (nm "VE", .array [nmo "Not", r 1])])
#guard vis (ocmd [(nm "OCGs", r 2), (nm "VE", .array [nmo "Or", r 1, r 2])])
#guard !vis (ocmd [(nm "VE", .array [nmo "And", r 1, .array [nmo "Not", r 1]])])
#guard vis (ocmd [(nm "VE", .array [nmo "And", r 1, .array [nmo "Not", r 2]])])
-- indirect OCMD and indirect nested expression; a malformed /VE falls back to /P
#guard !vis (r 9) [(9, ocmd [(nm "VE", .array [nmo "Not", r 8])]), (8, .array [nmo "Or", r 1])]
#guard !vis (ocmd [(nm "OCGs", r 2), (nm "VE", .array [nmo "Xor", r 1])])
-- a reference cycle terminates (fuel) and is visible
#guard vis (ocmd [(nm "VE", r 8)]) [(8, .array [nmo "And", r 1, r 8])]
#guard (isVisible (tbl [(9, ocmd [(nm "VE", .array [nmo "And", r 9])])]) {} st12 () (r 9)).1
-- no groups: everything visible
#guard (isVisible (tbl []) {} ({} : State) () (ocmd [(nm "VE", .array [nmo "Not", r 1])])).1

-- reading the default configuration
private def cat (props : PdfObject) : Dict := [(nm "OCProperties", props)]
private def objs0 : List (Nat × PdfObject) :=
  [(1, .dict [(nm "Type", nmo "OCG"), (nm "Name", .string [65])]),
   (2, .dict [(nm "Type", nmo "OCG")]),
   (3, .dict [(nm "Type", nmo "OCG"), (nm "Usage", .dict [(nm "View",
      .dict [(nm "ViewState", nmo "OFF")])])])]
private def rd (props : PdfObject) : Option Config := (read (tbl objs0) {} () (cat props)).1

#guard (rd .null).isNone && (rd (.dict [(nm "OCGs", .array [])])).isNone
#guard (stateOf (rd (.dict [(nm "OCGs", .array [r 1, r 2, r 3, r 1])]))) ==
  { known := [(1, 0), (2, 0), (3, 0)], off := [(3, 0)] }
#guard (stateOf (rd (.dict [(nm "OCGs", .array [r 1, r 2]),
  (nm "D", .dict [(nm "BaseState", nmo "OFF"), (nm "ON", .array [r 2])])]))).off == [(1, 0)]
#guard (stateOf (rd (.dict [(nm "OCGs", .array [r 1, r 2]),
  (nm "D", .dict [(nm "ON", .array [r 1]), (nm "OFF", .array [r 1])])]))).off == [(1, 0)]
#guard ((rd (.dict [(nm "OCGs", .array [r 1]),
  (nm "D", .dict [(nm "Name", .string [68])])])).map (·.name)) == some [68]
#guard ((rd (.dict [(nm "OCGs", .array [r 1, r 2]), (nm "D", .dict [
  (nm "Order", .array [r 1, .array [.string [76], r 2]]),
  (nm "RBGroups", .array [.array [r 1, r 2]]), (nm "Locked", .array [r 2])])])).map
    fun c => (c.order.length, c.rbGroups, c.locked, c.groups.map (·.name))) ==
  some (2, [[(1, 0), (2, 0)]], [(2, 0)], [[65], []])
-- the panel's toggle: radio buttons, locked groups
private def cfgRB : Config :=
  { groups := [{ key := (1, 0) }, { key := (2, 0) }, { key := (3, 0) }],
    rbGroups := [[(1, 0), (2, 0)]], locked := [(3, 0)] }
#guard (cfgRB.setGroup cfgRB.initial (1, 0) true).off == [(2, 0)]
#guard (cfgRB.setGroup cfgRB.initial (3, 0) false).off == []
#guard (cfgRB.initial.set (9, 0) false).off == []

end Checks

end SafePdf.Core.Doc.OptionalContent
