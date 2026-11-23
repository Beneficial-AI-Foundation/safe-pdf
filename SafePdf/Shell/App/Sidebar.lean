import SafePdf.Shell.App.Links
import SafePdf.Core.Doc.OpenSettings

/-!
# Outline sidebar model after PDF.js (task 9.7; Plan.md §6 Phase 9 "Look and feel: imitate PDF.js" — *Sidebar*, §10 `SafePdf/Shell/`)

The Tk-free description of the left sidebar (unverified shell code, total, checked by
`#guard`s). Design reference: PDF.js's sidebar and outline view (Mozilla, Apache-2.0;
`web/sidebar.js`, `web/viewer.css`), re-created in Tk by `Viewer` — no PDF.js code copied.

* **Panels** (`Panel`, `panels`; task 9.r9): the sidebar shows one panel at a time, chosen by
  a row of small icon buttons at its top (PDF.js's sidebar view buttons "Show Thumbnails",
  "Show Document Outline", "Show Attachments", "Show Layers"). A button shows only when the
  document has that content (`Panel.available`, `buttons`): thumbnails always, the outline
  when there is one; attachments (task 9.r10) and layers (task 9.r11b) plug in through
  `Content` and their entry in `panels`.
* **When it shows** (`onLoad`, `toggleVisible`, `afterToggle`): the sidebar opens on load as
  the document's `/PageMode` says (task 9.r8): UseThumbs → thumbnails, UseOutlines → outline,
  UseNone / FullScreen → closed; without a page mode the outline when there is one, else
  closed. Thumbnails exist for every document, so the toggle shows with any document; it
  reopens the last panel chosen while that is available (`pick`).
* **Thumbnails** (`thumbSize`, `thumbLayout`, `thumbsWanted`, `thumbEvict`, `thumbStep`): one
  page image `thumbW` = 98 px wide (PDF.js's `THUMBNAIL_WIDTH`), aspect and rotation kept, with
  its page number below, in a vertical list; only the visible ones and `thumbMargin` more on
  each side are rendered, and at most `thumbBudget` images are kept (the farthest from the view
  go first).
* **Tree** (`rows`): the outline entries (`Links.Entry`, depths already clamped so that every
  entry has its parent right before it) as rows with their parent, ancestors, whether they
  have children (only those get a disclosure triangle), and their indentation.
* **Collapsing** (`visibleRows`, `toggle`): a row is shown when all its ancestors are open;
  clicking a triangle opens/closes that row. Entries with a positive `/Count` start open
  (`Links.Entry.isOpen`), as in PDF.js.
-/

namespace SafePdf.Shell.App.Sidebar

open SafePdf.Core.Doc.OpenSettings (PageMode)

/-- A sidebar panel (task 9.r9), in button order (PDF.js: thumbnails, outline, attachments,
layers). -/
inductive Panel where
  /-- Page thumbnails (task 9.r9). -/
  | thumbnails
  /-- The document outline (task 9.7). -/
  | outline
  /-- Embedded files (task 9.r10). -/
  | attachments
  /-- Optional content groups (task 9.r11b). -/
  | layers
  deriving DecidableEq, Repr, Inhabited

/-- What the open document has, which decides the panel buttons shown. -/
structure Content where
  /-- The document has an outline. -/
  hasOutline : Bool := false
  /-- The document has attachments (set by task 9.r10's panel). -/
  hasAttachments : Bool := false
  /-- The document has optional content (set by task 9.r11b's panel). -/
  hasLayers : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- How a panel appears: its switcher button (Tk path, icon name of `::safepdf::icon`,
tooltip) and the panel's heading. -/
structure PanelInfo where
  /-- The panel. -/
  panel : Panel
  /-- Short name (Tcl key, `panel KEY` event). -/
  key : String
  /-- Tk path of its switcher button. -/
  button : String
  /-- Icon (`::safepdf::icon::NAME`). -/
  icon : String
  /-- Tooltip (PDF.js's button titles). -/
  tip : String
  /-- Heading shown above the panel. -/
  title : String
  deriving Repr, Inhabited

/-- The panel list, in button order. A new panel adds its entry here, its content flag in
`Content` and `Panel.available`, and its widgets in the viewer (`docs/viewer.md`). -/
def panels : List PanelInfo :=
  [⟨.thumbnails, "thumbnails", ".ol.sw.thumbnails", "thumbs", "Show Thumbnails", "Thumbnails"⟩,
   ⟨.outline, "outline", ".ol.sw.outline", "outline", "Show Document Outline", "Document outline"⟩,
   ⟨.attachments, "attachments", ".ol.sw.attachments", "attach", "Show Attachments", "Attachments"⟩,
   ⟨.layers, "layers", ".ol.sw.layers", "layers", "Show Layers", "Layers"⟩]

/-- The entry of panel `p` in `panels`. -/
def Panel.info (p : Panel) : PanelInfo :=
  (panels.find? (·.panel == p)).getD default

/-- The panel with key `k`. -/
def Panel.ofKey (k : String) : Option Panel :=
  (panels.find? (·.key == k)).map (·.panel)

/-- Whether panel `p` has something to show for a document with content `c`. -/
def Panel.available (c : Content) : Panel → Bool
  | .thumbnails => true
  | .outline => c.hasOutline
  | .attachments => c.hasAttachments
  | .layers => c.hasLayers

/-- The switcher buttons shown for content `c`, in order. -/
def buttons (c : Content) : List PanelInfo :=
  panels.filter (·.panel.available c)

/-- The panel a page mode names (`none` for UseNone and FullScreen). -/
def Panel.ofMode : PageMode → Option Panel
  | .useThumbs => some .thumbnails
  | .useOutlines => some .outline
  | .useAttachments => some .attachments
  | .useOC => some .layers
  | .useNone | .fullScreen => none

/-- The panel the sidebar opens with when a document is loaded (task 9.r9, rule O3 of task
9.r8): the page mode's panel when the document has its content; without a page mode, or for a
panel without content, the outline when there is one; else closed (`none`). UseNone and
FullScreen keep it closed. -/
def onLoad (mode : Option PageMode) (c : Content) : Option Panel :=
  let dflt : Option Panel := if c.hasOutline then some .outline else none
  match mode with
  | none => dflt
  | some m => match Panel.ofMode m with
    | some p => if p.available c then some p else dflt
    | none => none

/-- Whether the sidebar opens when a document is loaded (`onLoad` is not `none`). -/
def shownOnLoad (mode : Option PageMode) (c : Content) : Bool :=
  (onLoad mode c).isSome

/-- A status note when the page mode asks for a panel the viewer does not offer for this
document (`OpenSettings.panelMissing`: attachments and layers until tasks 9.r10 / 9.r11b);
thumbnails always exist, so UseThumbs never gets one. -/
def missingNote (mode : Option PageMode) (c : Content) : Option String := do
  let m ← mode
  let p ← Panel.ofMode m
  if p.available c then none
  else (SafePdf.Core.Doc.OpenSettings.panelMissing (some m)).map (s!"{·} panel not available yet")

/-- Whether the sidebar toggle button is shown: with any document (thumbnails, task 9.r9). -/
def toggleVisible (hasDoc : Bool) : Bool := hasDoc

/-- The panel the toggle opens: the last one chosen (`last`) while available, else the
outline when there is one, else thumbnails. -/
def pick (last : Panel) (c : Content) : Panel :=
  if last.available c then last else if c.hasOutline then .outline else .thumbnails

/-- The sidebar after the toggle (button, F9, View → Sidebar) when it was `shown`: closed, or
open on `pick last c`. -/
def afterToggle (shown : Bool) (last : Panel) (c : Content) : Option Panel :=
  if shown then none else some (pick last c)

/-! ### Thumbnails (task 9.r9) -/

/-- Width of a thumbnail image in pixels (PDF.js `THUMBNAIL_WIDTH`). -/
def thumbW : Nat := 98

/-- Space above the first thumbnail. -/
def thumbTop : Nat := 12

/-- Height of the page-number label below a thumbnail (its gap to the image included). -/
def thumbLabelH : Nat := 20

/-- Vertical space between one thumbnail's label and the next image. -/
def thumbGap : Nat := 14

/-- Thumbnails rendered beyond the visible ones on each side. -/
def thumbMargin : Nat := 3

/-- Most thumbnail images kept (Tk photos of about 98 × 127 × 4 bytes ≈ 50 KB each: at most
about 2 MB). -/
def thumbBudget : Nat := 40

/-- Size in pixels of the thumbnail of a page whose (rotated) size in page units is
`pw × ph`: `thumbW` wide, the height keeping the aspect, between 8 and four times the width
(a degenerate page gets a square). -/
def thumbSize (pw ph : Rat) : Nat × Nat :=
  if pw ≤ 0 || ph ≤ 0 then (thumbW, thumbW)
  else
    let h := ((thumbW : Rat) * ph / pw + 1 / 2).floor.toNat
    (thumbW, max 8 (min h (4 * thumbW)))

/-- A thumbnail laid out in the panel: its page, the canvas y of the image's top and the
image's size. -/
structure ThumbSlot where
  /-- Page index. -/
  page : Nat
  /-- Canvas y of the image's top edge. -/
  y : Nat
  /-- Image width. -/
  w : Nat
  /-- Image height. -/
  h : Nat
  deriving DecidableEq, Repr, Inhabited

/-- The bottom of slot `t` with its label. -/
def ThumbSlot.bottom (t : ThumbSlot) : Nat := t.y + t.h + thumbLabelH

/-- Lays out thumbnails of the given sizes top to bottom (`thumbTop`, then image, label and
`thumbGap` each). Returns the slots and the total height. -/
def thumbLayout (sizes : List (Nat × Nat)) : Array ThumbSlot × Nat :=
  sizes.foldl (fun (acc, y) (w, h) =>
    (acc.push ⟨acc.size, y, w, h⟩, y + h + thumbLabelH + thumbGap)) (#[], thumbTop)

/-- The pages whose thumbnail (with its label) meets the band `[top, bot)` of the panel. -/
def thumbsIn (ts : Array ThumbSlot) (top bot : Nat) : List Nat :=
  (ts.toList.filter fun t => t.y < bot && top < t.bottom).map (·.page)

/-- The thumbnails to render for the band `[top, bot)`: the visible ones and `margin` more on
each side, nearest to the band's middle first (so the visible ones come first). -/
def thumbsWanted (ts : Array ThumbSlot) (top bot margin : Nat) : List Nat :=
  match thumbsIn ts top bot with
  | [] => []
  | v@(a :: _) =>
    let b := v.getLast?.getD a
    let mid := (a + b) / 2
    let d (p : Nat) : Nat := if p ≥ mid then p - mid else mid - p
    let lo := (List.range margin).filterMap fun i =>
      if i + 1 ≤ a then some (a - (i + 1)) else none
    let hi := ((List.range margin).map (b + 1 + ·)).filter (· < ts.size)
    (v ++ lo ++ hi).mergeSort fun x y => d x ≤ d y

/-- The thumbnails to drop so that at most `budget` stay of `held`: those not `wanted`,
farthest from page `center` first. -/
def thumbEvict (held wanted : List Nat) (budget center : Nat) : List Nat :=
  if held.length ≤ budget then []
  else
    let d (p : Nat) : Nat := if p ≥ center then p - center else center - p
    let cand := (held.filter (!wanted.contains ·)).mergeSort fun x y => d x ≥ d y
    cand.take (held.length - budget)

/-- The thumbnail selected by Up (`down = false`) or Down from `cur` among `n` pages (kept
inside the document). -/
def thumbStep (n cur : Nat) (down : Bool) : Nat :=
  if n == 0 then 0
  else if down then min (cur + 1) (n - 1) else min (cur - 1) (n - 1)

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
-- Panels: buttons per content, page modes, the toggle.
#guard (buttons {}).map (·.key) == ["thumbnails"] &&
  (buttons { hasOutline := true }).map (·.key) == ["thumbnails", "outline"] &&
  (buttons { hasOutline := true, hasAttachments := true, hasLayers := true }).map (·.button) ==
    [".ol.sw.thumbnails", ".ol.sw.outline", ".ol.sw.attachments", ".ol.sw.layers"]
#guard panels.all fun i => Panel.ofKey i.key == some i.panel && i.panel.info.key == i.key
#guard onLoad none { hasOutline := true } == some .outline && onLoad none {} == none &&
  onLoad (some .useNone) { hasOutline := true } == none &&
  onLoad (some .useOutlines) { hasOutline := true } == some .outline &&
  onLoad (some .useOutlines) {} == none &&
  onLoad (some .fullScreen) { hasOutline := true } == none &&
  onLoad (some .useThumbs) {} == some .thumbnails &&
  onLoad (some .useThumbs) { hasOutline := true } == some .thumbnails &&
  onLoad (some .useAttachments) { hasOutline := true } == some .outline &&
  onLoad (some .useAttachments) { hasAttachments := true } == some .attachments &&
  onLoad (some .useOC) {} == none && onLoad (some .useOC) { hasLayers := true } == some .layers
#guard shownOnLoad (some .useThumbs) {} && !shownOnLoad none {}
#guard missingNote (some .useThumbs) {} == none && missingNote none {} == none &&
  missingNote (some .useOC) {} == some "layers panel not available yet" &&
  missingNote (some .useAttachments) { hasAttachments := true } == none &&
  missingNote (some .useOutlines) {} == none
#guard toggleVisible true && !toggleVisible false
#guard afterToggle false .outline { hasOutline := true } == some .outline &&
  afterToggle false .outline {} == some .thumbnails &&
  afterToggle false .thumbnails { hasOutline := true } == some .thumbnails &&
  afterToggle false .layers { hasOutline := true } == some .outline &&
  afterToggle true .thumbnails {} == none
-- Thumbnails: sizes keep the aspect, layout, lazy band, eviction, keys.
#guard thumbSize 612 792 == (98, 127) && thumbSize 792 612 == (98, 76) &&
  thumbSize 0 5 == (98, 98) && thumbSize 1000 1 == (98, 8) && thumbSize 1 1000 == (98, 392)
#guard (thumbLayout [(98, 127), (98, 76)]) ==
  (#[⟨0, 12, 98, 127⟩, ⟨1, 12 + 127 + 20 + 14, 98, 76⟩], 12 + 127 + 34 + 76 + 34)
#guard let (ts, _) := thumbLayout (List.replicate 100 (98, 127))
  thumbsIn ts 0 400 == [0, 1, 2] &&
  thumbsWanted ts 0 400 3 == [1, 0, 2, 3, 4, 5] &&
  thumbsWanted ts 1610 2000 2 == [11, 10, 12, 9, 13, 8, 14] &&
  (thumbsWanted ts 16000 17000 3).all (· < 100) && thumbsWanted ts 99999 100000 3 == []
#guard thumbEvict [1, 2, 3] [1] 5 1 == [] && thumbEvict [0, 1, 2, 3, 9] [1, 2] 3 1 == [9, 3]
#guard thumbStep 5 0 false == 0 && thumbStep 5 0 true == 1 && thumbStep 5 4 true == 4 &&
  thumbStep 0 3 true == 0 && thumbStep 5 3 false == 2

end SafePdf.Shell.App.Sidebar
