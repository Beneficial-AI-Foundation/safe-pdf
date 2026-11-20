/-!
# Viewer commands and the menubar model (task 9.1; Plan.md §6 Phase 9 "Menu bar", §8 native app, §10 `SafePdf/Shell/`)

The Tk-free description of the viewer's user commands (unverified shell code, total and
checked by `#guard`s). One `Cmd` per action the user can trigger from the menubar, the
toolbar, the context menu or a key; each has a label, the accelerator shown in menus, the
constant Tcl script that runs it (`::safepdf::emit …` back into Lean, or a constant UI proc),
and an enabled rule over a small view of the viewer state (`Ctx`).

* **Menubar** (`menubar`): File (Open…, Close, Quit), Edit (Copy, Select all, Highlight
  selection, the Highlight colour cascade, Add note…, Delete mark, Find…; marks: task 9.4), View
  (Outline, zoom in/out, actual size, fit page/width, rotate), Go (previous/next/first/last
  page, Go to page…, Back, Forward). The viewer builds the Tk menus from this list
  (`Viewer.buildMenus`) and keeps every entry's `-state` in step with `Cmd.enabled`
  (`entryStates`, applied only where it changed).
* **Toolbar** (`Toolbar.layout`, task 9.7, rebuilt after PDF.js): its buttons and its
  overflow menu reuse `Cmd` (label, script, rule) so that menubar, toolbar and keys stay one
  vocabulary.
* **Keys stay**: the accelerators shown here are the key bindings of `Viewer.setupScript`
  (Ctrl+O, Ctrl+W, Ctrl+Q, Ctrl+C, Ctrl+A, Ctrl+F, F9, `+`, `-`, `0`, `f`, `w`, `r`, `R`,
  PageUp/PageDown, Home/End, Ctrl+G, Alt+Left/Right, `h`, Delete); a menu accelerator is only a
  label in Tk.
* **Context menu** (right button): Copy, Select all, Find…, then the mark entries
  `popupMarks` — Highlight (colour cascade), Add note… (at the clicked point, `Cmd.popScript`),
  Delete mark (task 9.4).

Scripts are constants (no data in script text, `docs/viewer.md`): they are passed to Tk as
one `Tcl.quote`d word of `-command` and evaluated by Tk when the entry is invoked.
-/

namespace SafePdf.Shell.App.Menu

/-- A user command of the viewer. -/
inductive Cmd where
  /-- Open a file (dialog). -/
  | openFile
  /-- Close the document (the window stays). -/
  | close
  /-- Quit the viewer. -/
  | quit
  /-- Copy the selection to the clipboard. -/
  | copy
  /-- Select all text of the page. -/
  | selectAll
  /-- Open the find bar. -/
  | find
  /-- Highlight the selection in the current colour (task 9.4). -/
  | highlight
  /-- Add a note to the selection, or at a page point (task 9.4). -/
  | addNote
  /-- Delete the selected mark (task 9.4). -/
  | deleteMark
  /-- Show/hide the outline panel. -/
  | outline
  /-- Zoom in one step. -/
  | zoomIn
  /-- Zoom out one step. -/
  | zoomOut
  /-- Actual size (100 %). -/
  | actualSize
  /-- Fit the page into the window. -/
  | fitPage
  /-- Fit the page width into the window. -/
  | fitWidth
  /-- Rotate the view 90° clockwise. -/
  | rotateCw
  /-- Rotate the view 90° counter-clockwise. -/
  | rotateCcw
  /-- Previous page. -/
  | prevPage
  /-- Next page. -/
  | nextPage
  /-- First page. -/
  | firstPage
  /-- Last page. -/
  | lastPage
  /-- Open the go-to-page bar. -/
  | gotoPage
  /-- Back in the jump history. -/
  | back
  /-- Forward in the jump history. -/
  | forward
  deriving DecidableEq, Repr, Inhabited

/-- Every command, in menubar order. -/
def Cmd.all : List Cmd :=
  [.openFile, .close, .quit, .copy, .selectAll, .highlight, .addNote, .deleteMark, .find, .outline, .zoomIn, .zoomOut,
   .actualSize, .fitPage, .fitWidth, .rotateCw, .rotateCcw, .prevPage, .nextPage, .firstPage,
   .lastPage, .gotoPage, .back, .forward]

/-- Menu label. -/
def Cmd.label : Cmd → String
  | .openFile => "Open..."
  | .close => "Close"
  | .quit => "Quit"
  | .copy => "Copy"
  | .selectAll => "Select all"
  | .find => "Find..."
  | .highlight => "Highlight selection"
  | .addNote => "Add note..."
  | .deleteMark => "Delete mark"
  | .outline => "Outline"
  | .zoomIn => "Zoom in"
  | .zoomOut => "Zoom out"
  | .actualSize => "Actual size"
  | .fitPage => "Fit page"
  | .fitWidth => "Fit width"
  | .rotateCw => "Rotate right"
  | .rotateCcw => "Rotate left"
  | .prevPage => "Previous page"
  | .nextPage => "Next page"
  | .firstPage => "First page"
  | .lastPage => "Last page"
  | .gotoPage => "Go to page..."
  | .back => "Back"
  | .forward => "Forward"

/-- Accelerator text shown in the menu (the key binding itself lives in the setup script). -/
def Cmd.accel : Cmd → String
  | .openFile => "Ctrl+O"
  | .close => "Ctrl+W"
  | .quit => "Ctrl+Q"
  | .copy => "Ctrl+C"
  | .selectAll => "Ctrl+A"
  | .find => "Ctrl+F"
  | .highlight => "H"
  | .addNote => ""
  | .deleteMark => "Delete"
  | .outline => "F9"
  | .zoomIn => "+"
  | .zoomOut => "-"
  | .actualSize => "0"
  | .fitPage => "F"
  | .fitWidth => "W"
  | .rotateCw => "R"
  | .rotateCcw => "Shift+R"
  | .prevPage => "PageUp"
  | .nextPage => "PageDown"
  | .firstPage => "Home"
  | .lastPage => "End"
  | .gotoPage => "Ctrl+G"
  | .back => "Alt+Left"
  | .forward => "Alt+Right"

/-- Index of the underlined (mnemonic) character of the label. -/
def Cmd.underline : Cmd → Nat
  | .openFile => 0
  | .close => 0
  | .quit => 0
  | .copy => 0
  | .selectAll => 7
  | .find => 0
  | .highlight => 0
  | .addNote => 4
  | .deleteMark => 0
  | .outline => 0
  | .zoomIn => 5
  | .zoomOut => 5
  | .actualSize => 0
  | .fitPage => 4
  | .fitWidth => 4
  | .rotateCw => 7
  | .rotateCcw => 7
  | .prevPage => 0
  | .nextPage => 0
  | .firstPage => 0
  | .lastPage => 0
  | .gotoPage => 0
  | .back => 0
  | .forward => 0

/-- The constant Tcl script that runs the command. `next`/`prev` move a whole page (the
menu's Previous page lands on the top of the page, as the toolbar button does). -/
def Cmd.script : Cmd → String
  | .openFile => "::safepdf::emit open"
  | .close => "::safepdf::emit close"
  | .quit => "destroy ."
  | .copy => "::safepdf::emit copy"
  | .selectAll => "::safepdf::emit selectall"
  | .find => "::safepdf::showFind"
  | .highlight => "::safepdf::emit highlight"
  | .addNote => "::safepdf::emit note"
  | .deleteMark => "::safepdf::emit markDelete"
  | .outline => "::safepdf::emit outlineToggle"
  | .zoomIn => "::safepdf::emit zoom in"
  | .zoomOut => "::safepdf::emit zoom out"
  | .actualSize => "::safepdf::emit zoom actual"
  | .fitPage => "::safepdf::emit zoom fitpage"
  | .fitWidth => "::safepdf::emit zoom fitwidth"
  | .rotateCw => "::safepdf::emit rotate cw"
  | .rotateCcw => "::safepdf::emit rotate ccw"
  | .prevPage => "::safepdf::emit prev"
  | .nextPage => "::safepdf::emit next"
  | .firstPage => "::safepdf::emit first"
  | .lastPage => "::safepdf::emit last"
  | .gotoPage => "::safepdf::showGoto"
  | .back => "::safepdf::emit back"
  | .forward => "::safepdf::emit forward"

/-- What the enabled rules look at. -/
structure Ctx where
  /-- A document with at least one page is open. -/
  hasDoc : Bool := false
  /-- Current page (0-based). -/
  page : Nat := 0
  /-- Number of pages. -/
  pages : Nat := 0
  /-- Some text is selected. -/
  hasSel : Bool := false
  /-- The document has an outline. -/
  hasOutline : Bool := false
  /-- A mark (highlight or note) is selected (task 9.4). -/
  hasMark : Bool := false
  /-- The back stack is not empty. -/
  canBack : Bool := false
  /-- The forward stack is not empty. -/
  canForward : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- Whether the command can run in `c` (menu entries and toolbar buttons are disabled
otherwise; the handlers check again, so a key on a disabled command does nothing). -/
def Cmd.enabled (c : Ctx) : Cmd → Bool
  | .openFile | .quit => true
  | .copy | .highlight => c.hasDoc && c.hasSel
  | .deleteMark => c.hasDoc && c.hasMark
  | .outline => c.hasDoc && c.hasOutline
  | .prevPage | .firstPage => c.hasDoc && c.page > 0
  | .nextPage | .lastPage => c.hasDoc && c.page + 1 < c.pages
  | .back => c.hasDoc && c.canBack
  | .forward => c.hasDoc && c.canForward
  | .close | .selectAll | .find | .addNote | .zoomIn | .zoomOut | .actualSize | .fitPage | .fitWidth
  | .rotateCw | .rotateCcw | .gotoPage => c.hasDoc

/-- A menu entry. -/
inductive Entry where
  /-- A command entry. -/
  | cmd (c : Cmd)
  /-- A check entry bound to the Tcl variable `var` (the viewer keeps it in step). -/
  | check (c : Cmd) (var : String)
  /-- The highlight-colour cascade `path` (radio entries of `Marks.Color.all`, task 9.4). -/
  | colors (path : String)
  /-- A separator. -/
  | sep
  deriving DecidableEq, Repr, Inhabited

/-- The command of an entry. -/
def Entry.cmd? : Entry → Option Cmd
  | .cmd c | .check c _ => some c
  | .colors _ | .sep => none

/-- One cascade of the menubar. -/
structure Menu where
  /-- Tk path of the menu widget (a child of `.menubar`). -/
  path : String
  /-- Cascade label. -/
  label : String
  /-- Underlined character of the label. -/
  underline : Nat
  /-- Entries, top to bottom. -/
  entries : List Entry
  deriving Repr, Inhabited

/-- Tk path of the menubar. -/
def barPath : String := ".menubar"

/-- Tcl variable that mirrors whether the outline panel is shown (View → Outline check). -/
def outlineVar : String := "::safepdf::outlineOn"

/-- The menubar: File / Edit / View / Go. -/
def menubar : List Menu :=
  [ ⟨".menubar.file", "File", 0, [.cmd .openFile, .cmd .close, .sep, .cmd .quit]⟩,
    ⟨".menubar.edit", "Edit", 0,
      [.cmd .copy, .cmd .selectAll, .sep, .cmd .highlight, .colors ".menubar.edit.hl",
       .cmd .addNote, .cmd .deleteMark, .sep, .cmd .find]⟩,
    ⟨".menubar.view", "View", 0,
      [.check .outline outlineVar, .sep, .cmd .zoomIn, .cmd .zoomOut, .cmd .actualSize,
       .cmd .fitPage, .cmd .fitWidth, .sep, .cmd .rotateCw, .cmd .rotateCcw]⟩,
    ⟨".menubar.go", "Go", 0,
      [.cmd .prevPage, .cmd .nextPage, .cmd .firstPage, .cmd .lastPage, .sep, .cmd .gotoPage,
       .sep, .cmd .back, .cmd .forward]⟩ ]

/-- Label of the highlight-colour cascades (Edit menu, context menu). -/
def colorsLabel : String := "Highlight colour"

/-- Label of the highlight-colour cascade in the context menu (Plan: "Highlight (color
submenu)"). -/
def popColorsLabel : String := "Highlight"

/-- Tcl variable holding the current highlight colour (`Marks.Color.name`), shared by the
radio entries of every colour menu. -/
def colorVar : String := "::safepdf::hlColor"

/-- Script of a colour entry: highlight the selection in the chosen colour, or recolour the
selected mark, or just make it the current colour (`Viewer.highlight`). -/
def colorScript : String := "::safepdf::emit highlight $::safepdf::hlColor"

/-- The context-menu variant of a command's script: Add note… takes the point that was
right-clicked (`::safepdf::popX`/`popY`, window coordinates set when the menu opens). -/
def Cmd.popScript : Cmd → String
  | .addNote => "::safepdf::emit note $::safepdf::popX $::safepdf::popY"
  | c => c.script

/-- Tk path of the context menu. -/
def popPath : String := ".pop"

/-- Index in the context menu of the first mark entry (after Copy, Select all, Find…). -/
def popFirst : Nat := 3

/-- The mark entries of the context menu, appended after Copy / Select all / Find…: a
separator, the Highlight colour cascade (`.pop.hl`), Add note…, Delete mark. -/
def popupMarks : List Entry :=
  [.sep, .colors ".pop.hl", .cmd .addNote, .cmd .deleteMark]

/-- Every command entry of the menubar as (menu path, entry index, command); the index counts
separators, as Tk's menu indices do (menus have no tear-off entry). -/
def entryList : List (String × Nat × Cmd) :=
  menubar.flatMap fun m =>
    (List.range m.entries.length).zip m.entries |>.filterMap fun (i, e) =>
      e.cmd?.map fun c => (m.path, i, c)

/-- The enabled state of every menubar entry (`entryList` order) in `c` (the toolbar adds its
buttons and the overflow menu: `Toolbar.states`). -/
def entryStates (c : Ctx) : List Bool :=
  entryList.map (fun (_, _, k) => k.enabled c)

/-- Where `cmd` sits in the menubar: menu path and entry index. -/
def locate (cmd : Cmd) : Option (String × Nat) :=
  (entryList.find? (·.2.2 == cmd)).map fun (p, i, _) => (p, i)

-- Every command is in the menubar exactly once.
#guard Cmd.all.all fun c => (entryList.filter (·.2.2 == c)).length == 1
#guard entryList.length == Cmd.all.length
-- Labels are unique (Tk's `invoke {Label}` finds entries by label).
#guard (Cmd.all.map Cmd.label).eraseDups.length == Cmd.all.length
-- Mnemonics point into the label.
#guard Cmd.all.all fun c => c.underline < c.label.length
#guard menubar.map (·.label) == ["File", "Edit", "View", "Go"]
-- Separators count in Tk indices.
#guard locate .quit == some (".menubar.file", 3)
#guard locate .back == some (".menubar.go", 7)
#guard locate .zoomIn == some (".menubar.view", 2)
#guard locate .highlight == some (".menubar.edit", 3)
#guard locate .deleteMark == some (".menubar.edit", 6)
#guard locate .find == some (".menubar.edit", 8)
#guard Cmd.addNote.popScript != Cmd.addNote.script && Cmd.copy.popScript == Cmd.copy.script
-- Enabled rules.
#guard (Cmd.all.filter (Cmd.enabled {})) == [.openFile, .quit]
#guard let c : Ctx := { hasDoc := true, page := 0, pages := 3 }
  !Cmd.prevPage.enabled c && !Cmd.firstPage.enabled c && Cmd.nextPage.enabled c &&
  Cmd.lastPage.enabled c && !Cmd.copy.enabled c && !Cmd.outline.enabled c &&
  !Cmd.back.enabled c && Cmd.zoomIn.enabled c && !Cmd.highlight.enabled c &&
  Cmd.addNote.enabled c && !Cmd.deleteMark.enabled c
#guard let c : Ctx :=
    { hasDoc := true, page := 2, pages := 3, hasSel := true, hasOutline := true, canBack := true }
  Cmd.prevPage.enabled c && !Cmd.nextPage.enabled c && !Cmd.lastPage.enabled c &&
  Cmd.copy.enabled c && Cmd.outline.enabled c && Cmd.back.enabled c && !Cmd.forward.enabled c &&
  Cmd.highlight.enabled c
#guard Cmd.deleteMark.enabled { hasDoc := true, pages := 1, hasMark := true }
-- A one-page document: no paging either way.
#guard let c : Ctx := { hasDoc := true, page := 0, pages := 1 }
  !Cmd.prevPage.enabled c && !Cmd.nextPage.enabled c
#guard (entryStates {}).length == entryList.length

end SafePdf.Shell.App.Menu
