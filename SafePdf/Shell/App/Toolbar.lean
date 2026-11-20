import SafePdf.Shell.App.Menu
import SafePdf.Shell.App.View
import SafePdf.Shell.App.Links

/-!
# Toolbar model after PDF.js (task 9.7; Plan.md §6 Phase 9 "Look and feel: imitate PDF.js", §8 native app, §10 `SafePdf/Shell/`)

The Tk-free description of the viewer's toolbar (unverified shell code, total, checked by
`#guard`s). The design reference is the toolbar of PDF.js, the viewer built into Firefox
(Mozilla, Apache-2.0; `web/viewer.html`, `web/viewer.css`, `web/toolbar.js`): layout, sizes,
colours and behaviour are re-created in Tk by `Viewer`; no PDF.js code or icon file is copied
(icons are drawn with Tk canvas primitives, `docs/viewer.md`).

* **Layout** (`layout`): left — sidebar toggle (shown only when the document has an outline),
  previous / next page arrows, the page-number field and its "of N" label; centre — zoom out,
  zoom in and the zoom drop-down; right — the annotation tools (Highlight, enabled with a
  document since task 9.4: with a selection it highlights it in the current colour, without
  one it turns the Highlight tool and its pop-over on or off, task 9.8 `Bubble.Ui.toolClick`;
  Comment, Text, Draw, Image: disabled until task 9.9 lands), Print (disabled, after M9), Save
  (task 9.5c: the command `Menu.Cmd.save`, PDF.js's download icon, enabled with unsaved marks)
  and the `»` overflow menu (`overflow`: first/last page, rotate, Find, Go to,
  Open).
* **Enabled states** (`targets`, `states`): menubar entries (`Menu.entryList`), toolbar
  buttons and overflow-menu entries all follow `Menu.Cmd.enabled`; the tool buttons follow
  `Tool.enabled`.
* **Page field** (`entryText`, `ofText`, `pageEntry`): shows the page number, or the page
  label when the document has labels (as PDF.js: "iii" and "(3 of 120)"); Enter jumps to an
  exact label, else a page number, else a label ignoring case (`Links.gotoPage`); anything
  else reverts to the current page.
* **Zoom drop-down** (`ZoomChoice`): Automatic Zoom, Actual Size, Page Fit, Page Width,
  50 %–400 %, showing the current choice; a zoom reached with − / + that is not in the list
  shows as a percentage (PDF.js's custom option). Automatic Zoom is PDF.js's `auto` scale: the
  page width for portrait pages, the whole page for landscape ones, at most 125 %.
-/

namespace SafePdf.Shell.App.Toolbar

open Menu (Cmd Ctx)

/-! ## Zoom choices -/

/-- A choice of the zoom drop-down (or a zoom reached with the − / + buttons). -/
inductive ZoomChoice where
  /-- Automatic Zoom (PDF.js `auto`): page width (portrait) or page fit (landscape), at most
  `autoMaxPct`. -/
  | auto
  /-- Actual Size (100 %). -/
  | actual
  /-- Page Fit: the whole page in the window. -/
  | pageFit
  /-- Page Width: the page width fills the window. -/
  | pageWidth
  /-- A fixed percentage of actual size. -/
  | pct (p : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Largest zoom Automatic Zoom chooses, in percent (PDF.js `MAX_AUTO_SCALE` = 1.25). -/
def autoMaxPct : Nat := 125

/-- The entries of the drop-down, top to bottom (PDF.js `#scaleSelect`). -/
def ZoomChoice.presets : List ZoomChoice :=
  [.auto, .actual, .pageFit, .pageWidth] ++ [50, 75, 100, 125, 150, 200, 300, 400].map .pct

/-- Text of the choice in the drop-down and on its button. -/
def ZoomChoice.label : ZoomChoice → String
  | .auto => "Automatic Zoom"
  | .actual => "Actual Size"
  | .pageFit => "Page Fit"
  | .pageWidth => "Page Width"
  | .pct p => s!"{p}%"

/-- The value of the choice in Tcl (the drop-down's radiobutton value and the argument of
`emit zoom choose`). -/
def ZoomChoice.key : ZoomChoice → String
  | .auto => "auto"
  | .actual => "actual"
  | .pageFit => "page-fit"
  | .pageWidth => "page-width"
  | .pct p => toString p

/-- Parses a `key`; a percentage must lie within `View.minPct`–`View.maxPct`. -/
def ZoomChoice.ofKey (s : String) : Option ZoomChoice :=
  match s with
  | "auto" => some .auto
  | "actual" => some .actual
  | "page-fit" => some .pageFit
  | "page-width" => some .pageWidth
  | _ => match s.toNat? with
    | some p => if View.minPct ≤ p ∧ p ≤ View.maxPct then some (.pct p) else none
    | none => none

/-- The value the drop-down's radio variable gets: the choice's key when it is one of the
presets, else empty (no entry checked; the button shows the percentage, as PDF.js's custom
option). -/
def ZoomChoice.selected (c : ZoomChoice) : String :=
  if ZoomChoice.presets.contains c then c.key else ""

/-- The `View.Mode` of a choice (`none` for Automatic Zoom, which depends on the page). -/
def ZoomChoice.mode : ZoomChoice → Option View.Mode
  | .auto => none
  | .actual => some (.scale 100)
  | .pageFit => some .fitPage
  | .pageWidth => some .fitWidth
  | .pct p => some (.scale p)

/-- The choice for a `View.Mode` (what the − / + buttons, the keys and the menubar set). -/
def ZoomChoice.ofMode : View.Mode → ZoomChoice
  | .fitPage => .pageFit
  | .fitWidth => .pageWidth
  | .scale p => .pct p

/-- Name of the choice for the status line. -/
def ZoomChoice.statusName : ZoomChoice → String
  | .auto => "automatic"
  | .actual => "actual size"
  | .pageFit => "fit page"
  | .pageWidth => "fit width"
  | .pct _ => "fixed"

/-- The zoom (pixels per page unit) of choice `c` for a page of `pw × ph` units (after
rotation) in a canvas of `cw × ch` pixels at `scaling` pixels per point. Automatic Zoom is
PDF.js's rule: page width for a portrait page (`pw ≤ ph`), page fit otherwise, at most
`autoMaxPct`. -/
def ZoomChoice.zoom (c : ZoomChoice) (cw ch : Nat) (scaling pw ph : Rat) : Rat :=
  match c.mode with
  | some m => View.modeZoom m cw ch scaling pw ph
  | none =>
    let fit := View.fitZoom (decide (pw ≤ ph)) cw ch pw ph
    min fit (View.pctZoom autoMaxPct scaling)

#guard ZoomChoice.presets.map ZoomChoice.label ==
  ["Automatic Zoom", "Actual Size", "Page Fit", "Page Width", "50%", "75%", "100%", "125%",
   "150%", "200%", "300%", "400%"]
#guard ZoomChoice.presets.all fun c => ZoomChoice.ofKey c.key == some c
#guard (ZoomChoice.presets.map ZoomChoice.key).eraseDups.length == ZoomChoice.presets.length
#guard ZoomChoice.ofKey "33" == some (.pct 33) && ZoomChoice.ofKey "5" == none &&
  ZoomChoice.ofKey "9000" == none && ZoomChoice.ofKey "x" == none
-- A zoom outside the list shows as a percentage and checks no entry.
#guard (ZoomChoice.pct 33).label == "33%" && (ZoomChoice.pct 33).selected == "" &&
  (ZoomChoice.pct 150).selected == "150" && ZoomChoice.auto.selected == "auto"
-- Automatic Zoom: a portrait Letter page in a wide window is capped at 125 %; in a narrow
-- window it is the page width; a landscape page fits the window.
#guard ZoomChoice.auto.zoom 1900 900 (4 / 3) 612 792 == View.pctZoom 125 (4 / 3)
#guard ZoomChoice.auto.zoom 400 900 (4 / 3) 612 792 == View.fitZoom true 400 900 612 792
#guard ZoomChoice.auto.zoom 1000 300 (4 / 3) 792 612 == View.fitZoom false 1000 300 792 612
#guard ZoomChoice.pageWidth.zoom 400 900 (4 / 3) 612 792 == View.fitZoom true 400 900 612 792

/-! ## Page field -/

/-- Whether the document has page labels other than the page numbers (PDF.js then shows the
label in the field and "(k of N)" after it). -/
def hasLabels (labels : Array String) : Bool :=
  (List.range labels.size).any fun i =>
    match labels[i]? with
    | some l => !l.isEmpty && l != toString (i + 1)
    | none => false

/-- The text of the page field on page `page` (0-based): the label when the document has
labels, else the page number. -/
def entryText (labels : Array String) (page : Nat) : String :=
  if hasLabels labels then
    match labels[page]? with
    | some l => if l.isEmpty then toString (page + 1) else l
    | none => toString (page + 1)
  else toString (page + 1)

/-- The label after the page field: `of N`, or `(k of N)` with page labels. -/
def ofText (labels : Array String) (page n : Nat) : String :=
  if hasLabels labels then s!"({page + 1} of {n})" else s!"of {n}"

/-- The page (0-based) the page field's input `input` names in a document of `n` pages: an
exact label, else a page number `1..n`, else a label ignoring ASCII case
(`Links.gotoPage`). Without a label table of the right size, page numbers only. -/
def parseEntry (labels : Array String) (n : Nat) (input : String) : Option Nat :=
  let ls := if labels.size == n then labels else (Array.range n).map (toString <| · + 1)
  Links.gotoPage ls input

/-- Enter in the page field on page `cur`: the page to show and whether the input was valid
(an invalid input reverts the field to the current page). -/
def pageEntry (labels : Array String) (n cur : Nat) (input : String) : Nat × Bool :=
  match parseEntry labels n input with
  | some p => (p, true)
  | none => (cur, false)

#guard entryText #["1", "2", "3"] 1 == "2" && ofText #["1", "2", "3"] 1 3 == "of 3"
#guard entryText #["i", "ii", "1"] 1 == "ii" && ofText #["i", "ii", "1"] 1 3 == "(2 of 3)"
#guard entryText #[] 4 == "5" && ofText #[] 4 9 == "of 9"
#guard pageEntry #["1", "2", "3"] 3 0 "3" == (2, true)
#guard pageEntry #["1", "2", "3"] 3 0 " 2 " == (1, true)
#guard pageEntry #["1", "2", "3"] 3 1 "4" == (1, false)
#guard pageEntry #["1", "2", "3"] 3 1 "0" == (1, false)
#guard pageEntry #["1", "2", "3"] 3 2 "abc" == (2, false)
#guard pageEntry #["1", "2", "3"] 3 2 "" == (2, false)
-- Labels win over numbers; labels ignore case.
#guard pageEntry #["i", "ii", "1"] 3 0 "1" == (2, true)
#guard pageEntry #["i", "ii", "1"] 3 0 "II" == (1, true)
#guard pageEntry #[] 3 0 "3" == (2, true)

/-! ## Buttons and layout -/

/-- Toolbar buttons that are not (yet) viewer commands: the annotation tools and Print (Save is
the command `Menu.Cmd.save` since task 9.5c). -/
inductive Tool where
  /-- Highlight (task 9.4; its pop-over and the selection bubble: 9.8, `Bubble`). -/
  | highlight
  /-- Add a comment / note (task 9.9). -/
  | comment
  /-- Add text (FreeText; after the annotation tasks). -/
  | text
  /-- Draw (ink; after the annotation tasks). -/
  | draw
  /-- Add an image (stamp; after M9). -/
  | image
  /-- Print (after M9). -/
  | print
  deriving DecidableEq, Repr, Inhabited

/-- Tooltip of a tool button. -/
def Tool.tip : Tool → String
  | .highlight => "Highlight"
  | .comment => "Add comment"
  | .text => "Add text"
  | .draw => "Draw"
  | .image => "Add image"
  | .print => "Print"

/-- The task that brings the tool (shown when the disabled button is asked for). -/
def Tool.task : Tool → String
  | .highlight => "9.4"
  | .comment => "9.9"
  | .text | .draw => "a later Phase 9 task"
  | .image | .print => "after M9"

/-- Whether the tool can be used: Highlight with a document (task 9.4); the others not yet
(their tasks have not landed). -/
def Tool.enabled (c : Ctx) : Tool → Bool
  | .highlight => c.hasDoc
  | _ => false

/-- What a button does. -/
inductive Act where
  /-- A viewer command (`Menu.Cmd`: script and enabled rule). -/
  | cmd (c : Cmd)
  /-- A tool (`Tool`). -/
  | tool (t : Tool)
  /-- Opens the overflow menu. -/
  | more
  deriving DecidableEq, Repr, Inhabited

/-- A toolbar button: Tk path, the icon drawn on it (a Tcl proc `::safepdf::icon::NAME`), the
tooltip and the action. -/
structure Button where
  /-- Tk path (a canvas in `.bar.l`, `.bar.m` or `.bar.r`). -/
  path : String
  /-- Icon name. -/
  icon : String
  /-- Tooltip. -/
  tip : String
  /-- Action. -/
  act : Act
  deriving DecidableEq, Repr, Inhabited

/-- The Tcl script of a button (constant: a command's script, `::safepdf::emit tool NAME`,
or the overflow menu). -/
def Button.script (b : Button) : String :=
  match b.act with
  | .cmd c => c.script
  | .tool _ => s!"::safepdf::emit tool {b.icon}"
  | .more => "::safepdf::postMore"

/-- Whether the button can be pressed in `c`. -/
def Button.enabled (c : Ctx) (b : Button) : Bool :=
  match b.act with
  | .cmd k => k.enabled c
  | .tool t => t.enabled c
  | .more => true

/-- Whether the button is shown in `c`: the sidebar toggle only when the document has an
outline (PDF.js hides the outline view without one); all others always. -/
def Button.visible (c : Ctx) (b : Button) : Bool :=
  match b.act with
  | .cmd .outline => c.hasDoc && c.hasOutline
  | _ => true

/-- An item of the toolbar. -/
inductive Item where
  /-- A button. -/
  | button (b : Button)
  /-- A vertical separator (Tk path). -/
  | sep (path : String)
  /-- The page-number field and its "of N" label. -/
  | pageField
  /-- The zoom drop-down. -/
  | zoomBox
  deriving DecidableEq, Repr, Inhabited

/-- The three groups of the toolbar: Tk path of the frame and the items, left to right. -/
def layout : List (String × List Item) :=
  [ (".bar.l",
      [.button ⟨".bar.sidebar", "sidebar", "Toggle sidebar (F9)", .cmd .outline⟩,
       .sep ".bar.s0",
       .button ⟨".bar.prev", "up", "Previous page", .cmd .prevPage⟩,
       .sep ".bar.s1",
       .button ⟨".bar.next", "down", "Next page", .cmd .nextPage⟩,
       .pageField]),
    (".bar.m",
      [.button ⟨".bar.zout", "minus", "Zoom out", .cmd .zoomOut⟩,
       .sep ".bar.s2",
       .button ⟨".bar.zin", "plus", "Zoom in", .cmd .zoomIn⟩,
       .zoomBox]),
    (".bar.r",
      [.button ⟨".bar.highlight", "highlight", Tool.tip .highlight, .tool .highlight⟩,
       .button ⟨".bar.comment", "comment", Tool.tip .comment, .tool .comment⟩,
       .button ⟨".bar.text", "text", Tool.tip .text, .tool .text⟩,
       .button ⟨".bar.draw", "draw", Tool.tip .draw, .tool .draw⟩,
       .button ⟨".bar.image", "image", Tool.tip .image, .tool .image⟩,
       .sep ".bar.s3",
       .button ⟨".bar.print", "print", Tool.tip .print, .tool .print⟩,
       .button ⟨".bar.save", "save", "Save (Ctrl+S)", .cmd .save⟩,
       .sep ".bar.s4",
       .button ⟨".bar.more", "more", "Tools", .more⟩]) ]

/-- Every button of the toolbar, left to right. -/
def buttons : List Button :=
  layout.flatMap fun (_, items) => items.filterMap fun
    | .button b => some b
    | _ => none

/-- The tool named by `emit tool NAME` (its button's icon name). -/
def toolOf (name : String) : Option Tool :=
  buttons.findSome? fun b =>
    match b.act with
    | .tool t => if b.icon == name then some t else none
    | _ => none

/-- Tk path of the overflow menu (posted by the `»` button). -/
def morePath : String := ".more"

/-- Entries of the overflow menu (`none`: separator): PDF.js's secondary toolbar items that
the viewer has (first/last page, rotate) plus Find, Go to and Open, which no longer have
toolbar buttons. Document properties are not available yet. -/
def overflow : List (Option Cmd) :=
  [some .openFile, none, some .find, some .gotoPage, none, some .firstPage, some .lastPage,
   none, some .rotateCw, some .rotateCcw]

/-- The command entries of the overflow menu with their Tk menu indices. -/
def overflowEntries : List (Nat × Cmd) :=
  ((List.range overflow.length).zip overflow).filterMap fun (i, e) => e.map (i, ·)

/-! ## Enabled states -/

/-- A widget whose enabled state follows the rules: a menu entry (menu path and index) or a
toolbar button. -/
inductive Target where
  /-- Entry `index` of menu `menu`. -/
  | entry (menu : String) (index : Nat)
  /-- A toolbar button. -/
  | button (path : String)
  deriving DecidableEq, Repr, Inhabited

/-- Every target: the menubar entries, the overflow-menu entries, the toolbar buttons. -/
def targets : List Target :=
  Menu.entryList.map (fun (p, i, _) => .entry p i) ++
  overflowEntries.map (fun (i, _) => .entry morePath i) ++
  buttons.map (fun b => .button b.path)

/-- The enabled state of every target in `c` (`targets` order). -/
def states (c : Ctx) : List Bool :=
  Menu.entryStates c ++ overflowEntries.map (fun (_, k) => k.enabled c) ++
  buttons.map (·.enabled c)

-- Paths are unique; the tool names map back to their tools.
#guard (buttons.map (·.path)).eraseDups.length == buttons.length
#guard buttons.length == 13
#guard [Tool.highlight, .comment, .text, .draw, .image, .print].all fun t =>
  buttons.any fun b => b.act == .tool t && toolOf b.icon == some t
#guard targets.length == (states {}).length
#guard targets.eraseDups.length == targets.length
-- Without a document only Open, Quit and the overflow button work; the sidebar toggle hides.
#guard (buttons.filter (·.enabled {})).map (·.path) == [".bar.more"]
#guard (buttons.filter (·.visible {})).length == buttons.length - 1
-- First page of three with an outline: prev disabled, next enabled, of the tools only
-- Highlight.
#guard let c : Ctx := { hasDoc := true, page := 0, pages := 3, hasOutline := true }
  (buttons.filter (·.enabled c)).map (·.path) ==
    [".bar.sidebar", ".bar.next", ".bar.zout", ".bar.zin", ".bar.highlight", ".bar.more"] &&
  buttons.all (·.visible c)
-- No outline: the toggle is hidden.
#guard let c : Ctx := { hasDoc := true, page := 1, pages := 3 }
  (buttons.filter (!·.visible c)).map (·.path) == [".bar.sidebar"]
-- Save follows the unsaved marks.
#guard let c : Ctx := { hasDoc := true, page := 0, pages := 1 }
  !(buttons.filter (·.enabled c)).any (·.path == ".bar.save") &&
  (buttons.filter (·.enabled { c with dirty := true })).any (·.path == ".bar.save")
#guard (overflowEntries.map (·.2.label)) ==
  ["Open...", "Find...", "Go to page...", "First page", "Last page", "Rotate right",
   "Rotate left"]
#guard overflowEntries.map (·.1) == [0, 2, 3, 5, 6, 8, 9]
-- Every overflow command is also in the menubar (one vocabulary).
#guard overflowEntries.all fun (_, k) => (Menu.locate k).isSome

end SafePdf.Shell.App.Toolbar
