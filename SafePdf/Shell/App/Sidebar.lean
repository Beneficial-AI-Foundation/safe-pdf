import SafePdf.Shell.App.Links
import SafePdf.Core.Doc.OpenSettings

/-!
# Outline sidebar model after PDF.js (task 9.7; Plan.md §6 Phase 9 "Look and feel: imitate PDF.js" — *Sidebar*, §10 `SafePdf/Shell/`)

The Tk-free description of the left sidebar (unverified shell code, total, checked by
`#guard`s). Design reference: PDF.js's sidebar and outline view (Mozilla, Apache-2.0;
`web/sidebar.js`, `web/viewer.css`), re-created in Tk by `Viewer` — no PDF.js code copied.

* **When it shows** (`shownOnLoad`, `toggleVisible`): the sidebar opens on load as the
  document's `/PageMode` says (task 9.r8, `OpenSettings.outlineOpen`): without a page mode
  only when the document has an outline, never for `/UseNone` or `/FullScreen`, and never
  without an outline (its toolbar toggle is then hidden).
* **Tree** (`rows`): the outline entries (`Links.Entry`, depths already clamped so that every
  entry has its parent right before it) as rows with their parent, ancestors, whether they
  have children (only those get a disclosure triangle), and their indentation.
* **Collapsing** (`visibleRows`, `toggle`): a row is shown when all its ancestors are open;
  clicking a triangle opens/closes that row. Entries with a positive `/Count` start open
  (`Links.Entry.isOpen`), as in PDF.js.
-/

namespace SafePdf.Shell.App.Sidebar

/-- Whether the sidebar opens when a document is loaded (task 9.r8): as its page mode `mode`
says (`none`: the document sets none), and only with an outline. -/
def shownOnLoad (mode : Option SafePdf.Core.Doc.OpenSettings.PageMode) (hasOutline : Bool) :
    Bool :=
  SafePdf.Core.Doc.OpenSettings.outlineOpen mode hasOutline

/-- Whether the sidebar toggle button is shown: only with an outline. -/
def toggleVisible (hasOutline : Bool) : Bool := hasOutline

/-- The sidebar state after the toggle (button, F9, View → Outline) when it was `shown`: it
can only open when there is an outline. -/
def afterToggle (shown hasOutline : Bool) : Bool := hasOutline && !shown

/-- One row of the outline tree. -/
structure Row where
  /-- Index of the entry (text tags `oK` / `tK` of the outline tree in the viewer). -/
  index : Nat
  /-- Nesting depth. -/
  depth : Nat
  /-- Parent row, if any. -/
  parent : Option Nat
  /-- Ancestor rows, innermost first. -/
  ancestors : List Nat
  /-- Whether the row has children (and so a disclosure triangle). -/
  hasKids : Bool
  deriving DecidableEq, Repr, Inhabited

/-- Rows of the outline entries `es` (`Links.parents` gives the parents, each before its
children, so one pass computes the ancestors). Linear in the number of entries. -/
def rows (es : List Links.Entry) : List Row :=
  let ps := (Links.parents es).toArray
  let anc : Array (List Nat) := ps.foldl (fun acc p =>
    acc.push (match p with
      | some k => k :: (acc[k]?).getD []
      | none => [])) #[]
  let kids : Array Bool := ps.foldl (fun acc p =>
    match p with
    | some k => acc.modify k (fun _ => true)
    | none => acc) (Array.replicate es.length false)
  (List.range es.length).zip es |>.map fun (i, e) =>
    { index := i, depth := e.depth, parent := (ps[i]?).getD none, ancestors := (anc[i]?).getD [],
      hasKids := kids.getD i false }

/-- Initial open state of each row: entries with children that `/Count` marks open. -/
def initialOpen (es : List Links.Entry) : Array Bool :=
  ((rows es).zip es).toArray.map fun (r, e) => r.hasKids && e.isOpen

/-- Indices of the rows shown when the rows marked in `isOpen` are open: a row is shown when
every ancestor is open. -/
def visibleRows (rs : List Row) (isOpen : Array Bool) : List Nat :=
  (rs.filter fun r => r.ancestors.all fun a => isOpen.getD a false).map (·.index)

/-- Opens or closes row `i` (only a row with children changes). -/
def toggle (rs : List Row) (isOpen : Array Bool) (i : Nat) : Array Bool :=
  match rs[i]? with
  | some r => if r.hasKids then isOpen.modify i (!·) else isOpen
  | none => isOpen

/-- Disclosure triangle of a row: `▼` open, `▶` closed, nothing for a leaf (PDF.js's
`.treeItemToggler`). -/
def triangle (hasKids isOpen : Bool) : String :=
  if !hasKids then "" else if isOpen then "▼  " else "▶  "

/-- Left indentation of a row in pixels (PDF.js indents nested items by 20 px; deeper than 12
levels the indentation stops growing, so that the titles stay readable). -/
def indentPx (depth : Nat) : Nat := 8 + 20 * min depth 12

#guard indentPx 0 == 8 && indentPx 2 == 48 && indentPx 500 == indentPx 12

private def mk (d : Nat) (o : Bool) : Links.Entry := ⟨"", d, o, .none⟩

-- Tree: A, A.1, A.1.a, A.2, B, B.1 (A open, A.1 closed, B closed).
#guard (rows [mk 0 true, mk 1 false, mk 2 false, mk 1 false, mk 0 false, mk 1 false]).map
  (fun r => (r.parent, r.ancestors, r.hasKids)) ==
  [(none, [], true), (some 0, [0], true), (some 1, [1, 0], false), (some 0, [0], false),
   (none, [], true), (some 4, [4], false)]
#guard initialOpen [mk 0 true, mk 1 false, mk 2 false, mk 1 false, mk 0 false, mk 1 true] ==
  #[true, false, false, false, false, false]
#guard let es := [mk 0 true, mk 1 false, mk 2 false, mk 1 false, mk 0 false, mk 1 false]
  let rs := rows es
  let o := initialOpen es
  visibleRows rs o == [0, 1, 3, 4] &&
  visibleRows rs (toggle rs o 1) == [0, 1, 2, 3, 4] &&
  -- Closing A hides its whole subtree, also the open A.1's children.
  visibleRows rs (toggle rs (toggle rs o 1) 0) == [0, 4] &&
  visibleRows rs (toggle rs o 4) == [0, 1, 3, 4, 5] &&
  -- A leaf does not toggle.
  toggle rs o 2 == o && toggle rs o 99 == o
#guard triangle true true == "▼  " && triangle true false == "▶  " && triangle false true == ""
#guard shownOnLoad none true && !shownOnLoad none false && !toggleVisible false
#guard shownOnLoad (some .useOutlines) true && !shownOnLoad (some .useNone) true &&
  !shownOnLoad (some .useOutlines) false && !shownOnLoad (some .fullScreen) true &&
  shownOnLoad (some .useThumbs) true && !shownOnLoad (some .useAttachments) false
#guard afterToggle false true && !afterToggle true true && !afterToggle false false

end SafePdf.Shell.App.Sidebar
