import SafePdf.Shell.App.Tcl

/-!
# Viewer commands and the menubar model (task 9.1; Plan.md §6 Phase 9 "Menu bar", §8 native app, §10 `SafePdf/Shell/`)

The Tk-free description of the viewer's user commands (unverified shell code, total and
checked by `#guard`s). One `Cmd` per action the user can trigger from the menubar, the
toolbar, the context menu or a key; each has a label, the accelerator shown in menus, the
constant Tcl script that runs it (`::safepdf::emit …` back into Lean, or a constant UI proc),
and an enabled rule over a small view of the viewer state (`Ctx`).

* **Menubar** (`menubar`): File (Open…, Save, Save As… — task 9.5c, Save only with unsaved
  marks —, Import annotations… / Export annotations… — XFDF, task 9.11 —, Close, Quit; Quit goes through the viewer, which asks about unsaved marks), Edit (Copy, Select all, Highlight
  selection, the Highlight colour cascade, Add note…, Delete mark; marks: task 9.4; the check
  entries Highlight tool and Show all highlights: task 9.8; Find…), View
  (Sidebar, zoom in/out, actual size, fit page/width, rotate, and the view modes of task 9.3 as
  two radio groups after PDF.js: Page / Vertical Scrolling, No / Odd / Even Spreads), Go (previous/next/first/last
  page, Go to page…, Back, Forward). The viewer builds the Tk menus from this list
  (`Viewer.buildMenus`) and keeps every entry's `-state` in step with `Cmd.enabled`
  (`entryStates`, applied only where it changed).
* **Toolbar** (`Toolbar.layout`, task 9.7, rebuilt after PDF.js): its buttons and its
  overflow menu reuse `Cmd` (label, script, rule) so that menubar, toolbar and keys stay one
  vocabulary.
* **Keys stay**: the accelerators shown here are the key bindings of `Viewer.setupScript`
  (Ctrl+O, Ctrl+S, Ctrl+Shift+S, Ctrl+W, Ctrl+Q, Ctrl+C, Ctrl+A, Ctrl+F, F9, `+`, `-`, `0`, `f`, `w`, `r`, `R`,
  PageUp/PageDown, Home/End, Ctrl+G, Alt+Left/Right, `h`, Delete); a menu accelerator is only a
  label in Tk.
* **Platform keys** (task 9.r3, `Platform`, `Key`, `platformScript`): on macOS every Ctrl
  binding gets its Command twin and the labels read `Command-S` (drawn ⌘S); on X11/Windows
  nothing changes. Task 10.9 (macOS key conventions, after Preview and the HIG): the Command
  keys of a command are its own list (`Cmd.macKeys`), so a few differ from the Ctrl key —
  ⌥⌘G Go to page (⌘G / ⇧⌘G are Find next / previous, `Action`), ⌘[ / ⌘] Back / Forward,
  ⌘↑ / ⌘↓ first / last page, ⌃⌘S Sidebar, ⌃⌘H Highlight, ⌘R / ⌘L rotate, ⌘9 fit page — and
  ⌘. cancels the viewer's dialogs (`::safepdf::cancelBind`). `keyTable` lists every key of
  the main window per platform, checked for conflicts by `#guard`s.
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
  /-- Save the unsaved marks into the opened PDF file, which is overwritten after a
  confirmation (task 9.r2; task 9.5c wrote `FILE-annotated.pdf`). -/
  | save
  /-- Save the document with its marks to a chosen file (task 9.5c). -/
  | saveAs
  /-- Import marks from an XFDF file (task 9.11; dialog). -/
  | importXfdf
  /-- Export the marks to an XFDF file (task 9.11; dialog, `STEM.xfdf` proposed). -/
  | exportXfdf
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
  /-- Turn the Highlight tool on or off (task 9.8: with it on, selecting text highlights it;
  its pop-over opens with it). -/
  | hlTool
  /-- Show or hide all highlights (task 9.8, the pop-over's "Show all"). -/
  | showAll
  /-- Show/hide the sidebar (outline, thumbnails, …; task 9.r9: every document has
  thumbnails, so it works without an outline too). -/
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
  /-- Scroll mode Page: one page (or spread) at a time (task 9.3, PDF.js "Page Scrolling"). -/
  | scrollPage
  /-- Scroll mode Vertical: all pages stacked, scrolled continuously (task 9.3). -/
  | scrollVertical
  /-- Spread mode None: one page per row (task 9.3). -/
  | spreadNone
  /-- Spread mode Odd: pages 1|2, 3|4, … side by side (task 9.3). -/
  | spreadOdd
  /-- Spread mode Even: page 1 alone, then 2|3, 4|5, … (task 9.3). -/
  | spreadEven
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
  [.openFile, .save, .saveAs, .importXfdf, .exportXfdf, .close, .quit, .copy, .selectAll, .highlight, .addNote, .deleteMark, .hlTool,
   .showAll, .find, .outline, .zoomIn, .zoomOut,
   .actualSize, .fitPage, .fitWidth, .rotateCw, .rotateCcw, .scrollPage, .scrollVertical,
   .spreadNone, .spreadOdd, .spreadEven, .prevPage, .nextPage, .firstPage,
   .lastPage, .gotoPage, .back, .forward]

/-- Menu label. -/
def Cmd.label : Cmd → String
  | .openFile => "Open..."
  | .save => "Save"
  | .saveAs => "Save As..."
  | .importXfdf => "Import annotations..."
  | .exportXfdf => "Export annotations..."
  | .close => "Close"
  | .quit => "Quit"
  | .copy => "Copy"
  | .selectAll => "Select all"
  | .find => "Find..."
  | .highlight => "Highlight selection"
  | .addNote => "Add note..."
  | .deleteMark => "Delete mark"
  | .hlTool => "Highlight tool"
  | .showAll => "Show all highlights"
  | .outline => "Sidebar"
  | .zoomIn => "Zoom in"
  | .zoomOut => "Zoom out"
  | .actualSize => "Actual size"
  | .fitPage => "Fit page"
  | .fitWidth => "Fit width"
  | .rotateCw => "Rotate right"
  | .rotateCcw => "Rotate left"
  | .scrollPage => "Page Scrolling"
  | .scrollVertical => "Vertical Scrolling"
  | .spreadNone => "No Spreads"
  | .spreadOdd => "Odd Spreads"
  | .spreadEven => "Even Spreads"
  | .prevPage => "Previous page"
  | .nextPage => "Next page"
  | .firstPage => "First page"
  | .lastPage => "Last page"
  | .gotoPage => "Go to page..."
  | .back => "Back"
  | .forward => "Forward"

/-! ## Keys per platform (task 9.r3)

On macOS (Tk's `aqua` windowing system) every accelerator uses the Command key: each
binding with the primary modifier (Control) gets its Command twin, and menu labels take
Tk's aqua accelerator syntax (`Command-S`, `Command-Shift-S`, `Option-Left`), which Tk's
aqua menus draw as ⌘S, ⇧⌘S, ⌥←. Elsewhere (X11, Windows) nothing changes: Control
bindings and `Ctrl+S` labels. A Tk menu's accelerator is only a label on every platform
(on aqua Tk ignores the key equivalents of its own menus and leaves the keys to the
bindings, `tkMacOSXMenu.c` `tkMenuItemInvoke:`), so the bindings below are what makes the
keys work. -/

/-- The windowing system the key mapping is for (`tk windowingsystem`). -/
inductive Platform where
  /-- macOS (`aqua`): Command is the accelerator modifier. -/
  | aqua
  /-- X11 or Windows (`x11`, `win32`): Control. -/
  | other
  deriving DecidableEq, Repr, Inhabited

/-- The platform of a `tk windowingsystem` answer. -/
def Platform.ofWindowingSystem (ws : String) : Platform :=
  if ws.trimAscii.toString == "aqua" then .aqua else .other

/-- Tk modifier names that act as the primary accelerator modifier: Control everywhere,
and Command too on aqua (the Control bindings stay, so nothing a user typed before breaks). -/
def Platform.primaryMods : Platform → List String
  | .aqua => ["Control", "Command"]
  | .other => ["Control"]

/-- A key as the user presses it: modifiers, the Tk keysym and the key's name in labels. -/
structure Key where
  /-- With the primary modifier (Ctrl, ⌘ on macOS). -/
  primary : Bool := false
  /-- With Shift. -/
  shift : Bool := false
  /-- With Alt (Option on macOS). -/
  alt : Bool := false
  /-- With the Control key itself beside the primary modifier: only in macOS keys (⌃⌘S;
  task 10.9), where the primary modifier is Command. -/
  ctrl : Bool := false
  /-- Tk keysym; a letter in lower case. -/
  sym : String
  /-- The key's name in accelerator labels (`O`, `+`, `F9`, `PageUp`, `Left`). -/
  shown : String
  deriving DecidableEq, Repr, Inhabited

/-- A one-letter keysym. -/
def isLetterSym (s : String) : Bool :=
  s.length == 1 && s.all Char.isAlpha

/-- The accelerator label of a key: `Ctrl+Shift+S`, `Alt+Left` on X11/Windows (as before
task 9.r3); `Command-Shift-S`, `Option-Left` on aqua (Tk's aqua accelerator modifier
names, drawn as ⌘ ⇧ ⌥ glyphs). -/
def Key.label (p : Platform) (k : Key) : String :=
  match p with
  | .other =>
    (if k.primary || k.ctrl then "Ctrl+" else "") ++ (if k.shift then "Shift+" else "") ++
      (if k.alt then "Alt+" else "") ++ k.shown
  | .aqua =>
    (if k.ctrl then "Control-" else "") ++ (if k.primary then "Command-" else "") ++
      (if k.shift then "Shift-" else "") ++ (if k.alt then "Option-" else "") ++ k.shown

/-- The Tk event sequences of a key with the primary modifier (none for other keys: their
bindings do not depend on the platform). A shifted letter is bound by its upper-case keysym
(`<Control-Key-S>`, as before); its Command twin also as `<Shift-Command-Key-s>`, in case
Tk reports the unshifted keysym with Command held. Tk runs at most one binding per tag for
an event, so overlapping sequences never run a command twice. -/
def Key.sequences (p : Platform) (k : Key) : List String :=
  if !k.primary then [] else
  let alt := if k.alt then "Alt-" else ""
  p.primaryMods.flatMap fun m =>
    if k.shift && isLetterSym k.sym then
      s!"<{alt}{m}-Key-{k.sym.toUpper}>" ::
        (if m == "Command" then [s!"<Shift-{alt}{m}-Key-{k.sym}>"] else [])
    else if k.shift then [s!"<Shift-{alt}{m}-Key-{k.sym}>"]
    else [s!"<{alt}{m}-Key-{k.sym}>"]

/-- The Tk event sequences of any key with `m` as its primary modifier (`Control` for the
X11 keys, `Command` for the macOS keys) and `alt` the Tk name of its Alt key (`Alt`;
`Option` on aqua, the name Tk's own aqua bindings use). Shifted letters as in
`Key.sequences` (task 10.9; equal to it on the primary keys, `#guard`). -/
def Key.seqs (m alt : String) (k : Key) : List String :=
  let mods := (if k.ctrl then "Control-" else "") ++ (if k.alt then alt ++ "-" else "") ++
    (if k.primary then m ++ "-" else "")
  if k.shift && isLetterSym k.sym then
    s!"<{mods}Key-{k.sym.toUpper}>" ::
      (if m == "Command" && k.primary then [s!"<Shift-{mods}Key-{k.sym}>"] else [])
  else if k.shift then [s!"<Shift-{mods}Key-{k.sym}>"]
  else [s!"<{mods}Key-{k.sym}>"]

/-- The sequences of an X11 key (Control, Alt). -/
def Key.x11Seqs (k : Key) : List String := k.seqs "Control" "Alt"

/-- The sequences of a macOS key (Command, Option). -/
def Key.macSeqs (k : Key) : List String := k.seqs "Command" "Option"

/-- A key with the primary modifier. -/
def primaryKey (sym shown : String) (shift : Bool := false) : Key :=
  { primary := true, shift, sym, shown }

/-- A key without modifiers. -/
def plainKey (sym shown : String) : Key :=
  { sym, shown }

/-- The key shown as the command's accelerator on X11/Windows (the bindings of the plain
keys live in `Viewer.setupScript`; a menu accelerator is only a label in Tk). -/
def Cmd.key : Cmd → Option Key
  | .openFile => some (primaryKey "o" "O")
  | .save => some (primaryKey "s" "S")
  | .saveAs => some (primaryKey "s" "S" (shift := true))
  | .close => some (primaryKey "w" "W")
  | .quit => some (primaryKey "q" "Q")
  | .copy => some (primaryKey "c" "C")
  | .selectAll => some (primaryKey "a" "A")
  | .find => some (primaryKey "f" "F")
  | .gotoPage => some (primaryKey "g" "G")
  | .highlight => some (plainKey "h" "H")
  | .deleteMark => some (plainKey "Delete" "Delete")
  | .outline => some (plainKey "F9" "F9")
  | .zoomIn => some (plainKey "plus" "+")
  | .zoomOut => some (plainKey "minus" "-")
  | .actualSize => some (plainKey "0" "0")
  | .fitPage => some (plainKey "f" "F")
  | .fitWidth => some (plainKey "w" "W")
  | .rotateCw => some (plainKey "r" "R")
  | .rotateCcw => some { shift := true, sym := "R", shown := "R" }
  | .prevPage => some (plainKey "Prior" "PageUp")
  | .nextPage => some (plainKey "Next" "PageDown")
  | .firstPage => some (plainKey "Home" "Home")
  | .lastPage => some (plainKey "End" "End")
  | .back => some { alt := true, sym := "Left", shown := "Left" }
  | .forward => some { alt := true, sym := "Right", shown := "Right" }
  | .importXfdf | .exportXfdf | .addNote | .hlTool | .showAll | .scrollPage
  | .scrollVertical | .spreadNone | .spreadOdd | .spreadEven => none

/-- Every primary-modifier key that runs the command from the main window (bound on the
toplevel `.`): its accelerator plus alternatives (`=` and keypad `+` zoom in too). -/
def Cmd.primaryKeys : Cmd → List Key
  | .zoomIn => [primaryKey "plus" "+", primaryKey "equal" "=", primaryKey "KP_Add" "+"]
  | .zoomOut => [primaryKey "minus" "-", primaryKey "KP_Subtract" "-"]
  | .actualSize => [primaryKey "0" "0"]
  | c => match c.key with
    | some k => if k.primary then [k] else []
    | none => []

/-- The Command keys of the command on macOS (task 10.9; `primary` = Command, bound on `.`
by `platformScript` on aqua only, beside the X11 keys, which stay). The first is the menu
accelerator there. By default the Command twins of `primaryKeys` (⌘O, ⌘S, ⇧⌘S, ⌘W, ⌘Q,
⌘C, ⌘A, ⌘F, ⌘+ / ⌘= / ⌘−, ⌘0). Where macOS has its own convention (Preview, HIG) it wins:
Go to page ⌥⌘G (⌘G is Find next, `Action.findNext`), Back / Forward ⌘[ / ⌘], First / Last
page ⌘↑ / ⌘↓, Sidebar ⌃⌘S (the HIG's Show Sidebar), Highlight ⌃⌘H, Rotate right / left
⌘R / ⌘L, Fit page ⌘9 (Preview's Zoom to Fit). The plain keys (`h`, `F9`, `r`, `Home`, …)
work on both platforms. -/
def Cmd.macKeys : Cmd → List Key
  | .gotoPage => [{ primary := true, alt := true, sym := "g", shown := "G" }]
  | .back => [primaryKey "bracketleft" "["]
  | .forward => [primaryKey "bracketright" "]"]
  | .firstPage => [primaryKey "Up" "Up"]
  | .lastPage => [primaryKey "Down" "Down"]
  | .outline => [{ primary := true, ctrl := true, sym := "s", shown := "S" }]
  | .highlight => [{ primary := true, ctrl := true, sym := "h", shown := "H" }]
  | .rotateCw => [primaryKey "r" "R"]
  | .rotateCcw => [primaryKey "l" "L"]
  | .fitPage => [primaryKey "9" "9"]
  | c => c.primaryKeys

/-- The key shown on platform `p`: on aqua the first macOS key (⌘+, ⌘−, ⌘0 for the zoom
commands, the macOS convention, and the keys of `Cmd.macKeys`), else the X11 key (plain keys
such as PageUp or `w` are the same on both). -/
def Cmd.keyOn (p : Platform) (c : Cmd) : Option Key :=
  match p with
  | .aqua => c.macKeys.head?.orElse fun _ => c.key
  | .other => c.key

/-- Accelerator text shown in the menus on platform `p` (empty: none). -/
def Cmd.accelOn (p : Platform) (c : Cmd) : String :=
  ((c.keyOn p).map (Key.label p)).getD ""

/-- Accelerator text on X11/Windows (`accelOn .other`). -/
def Cmd.accel (c : Cmd) : String :=
  c.accelOn .other

/-- Key actions of the main window that are not menubar commands (task 10.9). -/
inductive Action where
  /-- Find the next hit of the find bar's query. -/
  | findNext
  /-- Find the previous hit. -/
  | findPrev
  deriving DecidableEq, Repr, Inhabited

/-- Every key action. -/
def Action.all : List Action := [.findNext, .findPrev]

/-- What the action does (the key table of `docs/viewer.md`). -/
def Action.name : Action → String
  | .findNext => "Find next"
  | .findPrev => "Find previous"

/-- The constant script of the action on `.` (as the find bar's buttons). -/
def Action.script : Action → String
  | .findNext => "::safepdf::emit find next $::safepdf::query"
  | .findPrev => "::safepdf::emit find prev $::safepdf::query"

/-- The X11 keys (plain, bound in `Viewer.setupScript` on `.` and the find bar): F3 /
Shift+F3 (Ctrl+G is Go to page on X11, as before). -/
def Action.x11Keys : Action → List Key
  | .findNext => [plainKey "F3" "F3"]
  | .findPrev => [{ shift := true, sym := "F3", shown := "F3" }]

/-- The macOS Command keys (bound by `platformScript` on aqua, on `.` and in the find bar):
⌘G / ⇧⌘G, the macOS Find Next / Find Previous. F3 stays. -/
def Action.macKeys : Action → List Key
  | .findNext => [primaryKey "g" "G"]
  | .findPrev => [primaryKey "g" "G" (shift := true)]

/-- The quit key, bound also on the text fields that have their own bind tags (the page
field, the find and go-to bars, the FreeText editor), so that it works while typing. -/
def quitKey : Key := primaryKey "q" "Q"

/-- Entry widgets of `Viewer.setupScript` with their own bind tags that get the quit key. -/
def quitEntries : List String := [".bar.pg.e", ".find.e", ".goto.e"]

/-- The fixed entries of the context menu (created in `Viewer.setupScript` with the X11
labels) whose accelerators follow the platform. -/
def popAccelCmds : List Cmd := [.copy, .selectAll, .find, .outline, .back, .forward, .gotoPage]

/-- Index of the underlined (mnemonic) character of the label. -/
def Cmd.underline : Cmd → Nat
  | .openFile => 0
  | .save => 0
  | .saveAs => 5
  | .importXfdf => 0
  | .exportXfdf => 0
  | .close => 0
  | .quit => 0
  | .copy => 0
  | .selectAll => 7
  | .find => 0
  | .highlight => 0
  | .addNote => 4
  | .deleteMark => 0
  | .hlTool => 10
  | .showAll => 0
  | .outline => 0
  | .zoomIn => 5
  | .zoomOut => 5
  | .actualSize => 0
  | .fitPage => 4
  | .fitWidth => 4
  | .rotateCw => 7
  | .rotateCcw => 7
  | .scrollPage => 5
  | .scrollVertical => 0
  | .spreadNone => 0
  | .spreadOdd => 1
  | .spreadEven => 0
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
  | .save => "::safepdf::emit save"
  | .saveAs => "::safepdf::emit saveAs"
  | .importXfdf => "::safepdf::emit importXfdf"
  | .exportXfdf => "::safepdf::emit exportXfdf"
  | .close => "::safepdf::emit close"
  | .quit => "::safepdf::emit quit"
  | .copy => "::safepdf::emit copy"
  | .selectAll => "::safepdf::emit selectall"
  | .find => "::safepdf::showFind"
  | .highlight => "::safepdf::emit highlight"
  | .addNote => "::safepdf::emit note"
  | .deleteMark => "::safepdf::emit markDelete"
  | .hlTool => "::safepdf::emit hlTool"
  | .showAll => "::safepdf::emit showAll"
  | .outline => "::safepdf::emit outlineToggle"
  | .zoomIn => "::safepdf::emit zoom in"
  | .zoomOut => "::safepdf::emit zoom out"
  | .actualSize => "::safepdf::emit zoom actual"
  | .fitPage => "::safepdf::emit zoom fitpage"
  | .fitWidth => "::safepdf::emit zoom fitwidth"
  | .rotateCw => "::safepdf::emit rotate cw"
  | .rotateCcw => "::safepdf::emit rotate ccw"
  | .scrollPage => "::safepdf::emit viewMode scroll page"
  | .scrollVertical => "::safepdf::emit viewMode scroll vertical"
  | .spreadNone => "::safepdf::emit viewMode spread none"
  | .spreadOdd => "::safepdf::emit viewMode spread odd"
  | .spreadEven => "::safepdf::emit viewMode spread even"
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
  /-- There are marks not saved into the file yet (task 9.5c). -/
  dirty : Bool := false
  /-- The current page is in the first spread (task 9.3: Previous has nowhere to go in the
  facing modes even when `page > 0`). -/
  onFirst : Bool := false
  /-- The current page is in the last spread (task 9.3). -/
  onLast : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- Whether the command can run in `c` (menu entries and toolbar buttons are disabled
otherwise; the handlers check again, so a key on a disabled command does nothing). -/
def Cmd.enabled (c : Ctx) : Cmd → Bool
  | .openFile | .quit => true
  | .copy | .highlight => c.hasDoc && c.hasSel
  | .deleteMark => c.hasDoc && c.hasMark
  | .save => c.hasDoc && c.dirty
  | .outline => c.hasDoc
  | .prevPage | .firstPage => c.hasDoc && c.page > 0 && !c.onFirst
  | .nextPage | .lastPage => c.hasDoc && c.page + 1 < c.pages && !c.onLast
  | .back => c.hasDoc && c.canBack
  | .forward => c.hasDoc && c.canForward
  | .saveAs | .importXfdf | .exportXfdf | .close | .selectAll | .find | .addNote | .hlTool | .showAll | .zoomIn | .zoomOut | .actualSize | .fitPage | .fitWidth
  | .rotateCw | .rotateCcw | .gotoPage | .scrollPage | .scrollVertical | .spreadNone
  | .spreadOdd | .spreadEven => c.hasDoc

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

/-- Tcl variable that mirrors whether the sidebar is shown (View → Sidebar check). -/
def outlineVar : String := "::safepdf::outlineOn"

/-- Tcl variable holding the scroll mode (`View.ScrollMode.key`; the View menu's and the
overflow menu's radio entries, task 9.3). -/
def scrollVar : String := "::safepdf::scrollMode"

/-- Tcl variable holding the spread mode (`View.SpreadMode.key`, task 9.3). -/
def spreadVar : String := "::safepdf::spreadMode"

/-- The radio variable and value of a view-mode command (task 9.3): the menus show these
commands as radio entries, checked while the mode is on. -/
def Cmd.radio? : Cmd → Option (String × String)
  | .scrollPage => some (scrollVar, "page")
  | .scrollVertical => some (scrollVar, "vertical")
  | .spreadNone => some (spreadVar, "none")
  | .spreadOdd => some (spreadVar, "odd")
  | .spreadEven => some (spreadVar, "even")
  | _ => none

/-- Tcl variable that mirrors whether the Highlight tool is on (Edit → Highlight tool). -/
def hlToolVar : String := "::safepdf::hlTool"

/-- Tcl variable that mirrors "Show all" (Edit → Show all highlights, the pop-over switch). -/
def showAllVar : String := "::safepdf::showAll"

/-- The menubar: File / Edit / View / Go. -/
def menubar : List Menu :=
  [ ⟨".menubar.file", "File", 0, [.cmd .openFile, .cmd .save, .cmd .saveAs, .sep, .cmd .importXfdf,
      .cmd .exportXfdf, .sep, .cmd .close, .sep, .cmd .quit]⟩,
    ⟨".menubar.edit", "Edit", 0,
      [.cmd .copy, .cmd .selectAll, .sep, .cmd .highlight, .colors ".menubar.edit.hl",
       .cmd .addNote, .cmd .deleteMark, .sep, .check .hlTool hlToolVar,
       .check .showAll showAllVar, .sep, .cmd .find]⟩,
    ⟨".menubar.view", "View", 0,
      [.check .outline outlineVar, .sep, .cmd .zoomIn, .cmd .zoomOut, .cmd .actualSize,
       .cmd .fitPage, .cmd .fitWidth, .sep, .cmd .rotateCw, .cmd .rotateCcw, .sep,
       .cmd .scrollPage, .cmd .scrollVertical, .sep, .cmd .spreadNone, .cmd .spreadOdd,
       .cmd .spreadEven]⟩,
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

/-- Every key bound on the main window's tag `.` on platform `p`, as (Tk sequence, script):
the X11 keys of every command (plain and Ctrl, on both platforms: the Control bindings stay
on aqua), the actions' X11 keys and, on aqua, the macOS keys of commands and actions. The
`#guard`s below check that no sequence runs two different scripts. -/
def keyTable (p : Platform) : List (String × String) :=
  let x11 := Cmd.all.flatMap (fun c =>
      ((c.key.toList.filter (!·.primary)) ++ c.primaryKeys).flatMap fun k =>
        k.x11Seqs.map (·, c.script)) ++
    Action.all.flatMap fun a => (a.x11Keys.flatMap Key.x11Seqs).map (·, a.script)
  let mac := match p with
    | .aqua => Cmd.all.flatMap (fun c => (c.macKeys.flatMap Key.macSeqs).map (·, c.script)) ++
        Action.all.flatMap fun a => (a.macKeys.flatMap Key.macSeqs).map (·, a.script)
    | .other => []
  x11 ++ mac

/-- Whether no Tk sequence in the list is bound to two different scripts. -/
def conflictFree (t : List (String × String)) : Bool :=
  t.all fun (q, s) => t.all fun (q', s') => q != q' || s == s'

/-- The Tcl script that installs the platform's primary-modifier bindings (run once after
`Viewer.setupScript`; every word through `Tcl.quote`): for every command its `primaryKeys`
on `.`, the quit key on `quitEntries`, the context menu's accelerator labels, the proc
`::safepdf::primaryBind W KEYSYM SCRIPT` used by widgets created later (FreeText editor,
note popup), and on aqua Command+wheel zoom and `::tk::mac::Quit` (the hook Tk calls for
the application menu's Quit item, a quit from the Dock or at logout) running File → Quit's
script. On X11/Windows the bindings repeat the Control bindings `setupScript` makes. -/
def platformScript (p : Platform) : String :=
  let bindAll (tag : String) (k : Key) (script : String) : List (List String) :=
    (k.sequences p).map fun seq => ["bind", tag, seq, script]
  let cmds := Cmd.all.flatMap fun c =>
    c.primaryKeys.flatMap fun k => k.x11Seqs.map fun q => ["bind", ".", q, c.script]
  -- macOS keys (task 10.9): the commands' and actions' Command keys on `.`, the find actions
  -- also in the find bar (own bind tags; `break` keeps the entry's class bindings out).
  let macs : List (List String) := match p with
    | .aqua =>
      (Cmd.all.flatMap fun c => (c.macKeys.flatMap Key.macSeqs).map fun q => ["bind", ".", q, c.script]) ++
      (Action.all.flatMap fun a => (a.macKeys.flatMap Key.macSeqs).flatMap fun q =>
        [["bind", ".", q, a.script], ["bind", ".find.e", q, a.script ++ "; break"]])
    | .other => []
  let quits := quitEntries.flatMap fun w => bindAll w quitKey Cmd.quit.script
  let pops := popAccelCmds.map fun c =>
    [popPath, "entryconfigure", c.label, "-accelerator", c.accelOn p]
  let aqua : List (List String) := match p with
    | .aqua =>
      [["bind", ".c", "<Command-MouseWheel>", "::safepdf::wheelZoom %D %x %y; break"],
       ["namespace", "eval", "::tk::mac", ""],
       ["proc", "::tk::mac::Quit", "", Cmd.quit.script]]
    | .other => []
  let proc := ["proc", "::safepdf::primaryBind", "w key script",
    "foreach m " ++ Tcl.quote (Tcl.Word.renderList (p.primaryMods.map .lit)) ++
      " { bind $w <$m-Key-$key> $script }"]
  -- ⌘. cancels a dialog on macOS (task 10.9): the viewer's own dialogs call
  -- `::safepdf::cancelBind W SCRIPT` beside their Escape binding; a no-op elsewhere.
  let cancel := ["proc", "::safepdf::cancelBind", "w script", match p with
    | .aqua => "bind $w <Command-Key-period> $script"
    | .other => ""]
  Tcl.Script.render (Tcl.Script.ofStrings (cmds ++ macs ++ quits ++ pops ++ aqua ++ [proc, cancel]))

/-- A display text naming keys the X11 way (status messages, tooltips: `Ctrl+O`) in the
platform's form: on aqua the macOS glyphs (`⌘O`, `⇧⌘S`, `⌥`). -/
def Platform.keyText (p : Platform) (s : String) : String :=
  match p with
  | .other => s
  | .aqua => (((s.replace "Ctrl+Shift+" "⇧⌘").replace "Ctrl+" "⌘").replace "Alt+" "⌥").replace
      "(F9)" "(⌃⌘S)"

-- Every command is in the menubar exactly once.
#guard Cmd.all.all fun c => (entryList.filter (·.2.2 == c)).length == 1
#guard entryList.length == Cmd.all.length
-- Labels are unique (Tk's `invoke {Label}` finds entries by label).
#guard (Cmd.all.map Cmd.label).eraseDups.length == Cmd.all.length
-- Mnemonics point into the label.
#guard Cmd.all.all fun c => c.underline < c.label.length
#guard menubar.map (·.label) == ["File", "Edit", "View", "Go"]
-- Separators count in Tk indices.
#guard locate .quit == some (".menubar.file", 9)
#guard locate .importXfdf == some (".menubar.file", 4) && locate .exportXfdf == some (".menubar.file", 5)
#guard locate .save == some (".menubar.file", 1) && locate .saveAs == some (".menubar.file", 2)
#guard locate .back == some (".menubar.go", 7)
#guard locate .zoomIn == some (".menubar.view", 2)
#guard locate .highlight == some (".menubar.edit", 3)
#guard locate .deleteMark == some (".menubar.edit", 6)
#guard locate .hlTool == some (".menubar.edit", 8)
#guard locate .showAll == some (".menubar.edit", 9)
#guard locate .find == some (".menubar.edit", 11)
#guard Cmd.addNote.popScript != Cmd.addNote.script && Cmd.copy.popScript == Cmd.copy.script
-- Enabled rules.
#guard (Cmd.all.filter (Cmd.enabled {})) == [.openFile, .quit]
#guard let c : Ctx := { hasDoc := true, page := 0, pages := 3 }
  !Cmd.prevPage.enabled c && !Cmd.firstPage.enabled c && Cmd.nextPage.enabled c &&
  Cmd.lastPage.enabled c && !Cmd.copy.enabled c && Cmd.outline.enabled c &&
  !Cmd.back.enabled c && Cmd.zoomIn.enabled c && !Cmd.highlight.enabled c &&
  Cmd.addNote.enabled c && !Cmd.deleteMark.enabled c && Cmd.hlTool.enabled c &&
  Cmd.showAll.enabled c
#guard let c : Ctx :=
    { hasDoc := true, page := 2, pages := 3, hasSel := true, hasOutline := true, canBack := true }
  Cmd.prevPage.enabled c && !Cmd.nextPage.enabled c && !Cmd.lastPage.enabled c &&
  Cmd.copy.enabled c && Cmd.outline.enabled c && Cmd.back.enabled c && !Cmd.forward.enabled c &&
  Cmd.highlight.enabled c
#guard Cmd.deleteMark.enabled { hasDoc := true, pages := 1, hasMark := true }
-- Save needs unsaved marks; Save As only a document.
#guard !Cmd.save.enabled { hasDoc := true, pages := 1 } && Cmd.saveAs.enabled { hasDoc := true, pages := 1 } &&
  Cmd.save.enabled { hasDoc := true, pages := 1, dirty := true } && !Cmd.saveAs.enabled {}
-- XFDF import/export (task 9.11) need a document only.
#guard Cmd.importXfdf.enabled { hasDoc := true, pages := 1 } && Cmd.exportXfdf.enabled { hasDoc := true, pages := 1 } &&
  !Cmd.importXfdf.enabled {} && !Cmd.exportXfdf.enabled {}
-- A one-page document: no paging either way.
#guard let c : Ctx := { hasDoc := true, page := 0, pages := 1 }
  !Cmd.prevPage.enabled c && !Cmd.nextPage.enabled c
#guard (entryStates {}).length == entryList.length
-- View modes (task 9.3): radio entries at the end of the View menu, two groups.
#guard locate .scrollVertical == some (".menubar.view", 12) && locate .spreadEven == some (".menubar.view", 16)
#guard (Cmd.all.filter (·.radio?.isSome)).map (·.radio?.map Prod.fst) ==
  [some scrollVar, some scrollVar, some spreadVar, some spreadVar, some spreadVar]
-- In the facing modes Previous/Next follow the spreads, not only the page number.
#guard let c : Ctx := { hasDoc := true, page := 1, pages := 4, onFirst := true }
  !Cmd.prevPage.enabled c && !Cmd.firstPage.enabled c && Cmd.nextPage.enabled c
#guard let c : Ctx := { hasDoc := true, page := 2, pages := 4, onLast := true }
  !Cmd.nextPage.enabled c && !Cmd.lastPage.enabled c && Cmd.prevPage.enabled c

-- Keys per platform (task 9.r3). The X11/Windows labels are the ones before 9.r3.
#guard Cmd.all.map Cmd.accel ==
  ["Ctrl+O", "Ctrl+S", "Ctrl+Shift+S", "", "", "Ctrl+W", "Ctrl+Q", "Ctrl+C", "Ctrl+A", "H", "",
   "Delete", "", "", "Ctrl+F", "F9", "+", "-", "0", "F", "W", "R", "Shift+R", "", "", "", "",
   "", "PageUp", "PageDown", "Home", "End", "Ctrl+G", "Alt+Left", "Alt+Right"]
-- aqua: Command labels (Tk draws them as ⌘S, ⇧⌘S, ⌥←).
#guard Cmd.save.accelOn .aqua == "Command-S" && Cmd.saveAs.accelOn .aqua == "Command-Shift-S" &&
  Cmd.openFile.accelOn .aqua == "Command-O" && Cmd.find.accelOn .aqua == "Command-F" &&
  Cmd.copy.accelOn .aqua == "Command-C" && Cmd.selectAll.accelOn .aqua == "Command-A" &&
  Cmd.quit.accelOn .aqua == "Command-Q" && Cmd.close.accelOn .aqua == "Command-W" &&
  Cmd.gotoPage.accelOn .aqua == "Command-Option-G"
#guard Cmd.zoomIn.accelOn .aqua == "Command-+" && Cmd.zoomOut.accelOn .aqua == "Command--" &&
  Cmd.actualSize.accelOn .aqua == "Command-0"
-- macOS conventions (task 10.9; Preview, HIG).
#guard Cmd.back.accelOn .aqua == "Command-[" && Cmd.forward.accelOn .aqua == "Command-]" &&
  Cmd.rotateCw.accelOn .aqua == "Command-R" && Cmd.rotateCcw.accelOn .aqua == "Command-L" &&
  Cmd.outline.accelOn .aqua == "Control-Command-S" &&
  Cmd.highlight.accelOn .aqua == "Control-Command-H" &&
  Cmd.firstPage.accelOn .aqua == "Command-Up" && Cmd.lastPage.accelOn .aqua == "Command-Down" &&
  Cmd.fitPage.accelOn .aqua == "Command-9" && Cmd.fitWidth.accelOn .aqua == "W" &&
  Cmd.prevPage.accelOn .aqua == "PageUp" && Cmd.deleteMark.accelOn .aqua == "Delete"
-- Every command with a key on X11 has one on macOS, and the reverse.
#guard Cmd.all.all fun c => (c.keyOn .aqua).isSome == c.key.isSome
-- No Ctrl label on aqua, no Command label elsewhere.
#guard Cmd.all.all fun c => !((c.accelOn .aqua).startsWith "Ctrl") &&
  !((c.accelOn .other).startsWith "Command")
-- Exactly the commands with Control bindings on `.` in `Viewer.setupScript`.
#guard (Cmd.all.filter (!·.primaryKeys.isEmpty)) ==
  [.openFile, .save, .saveAs, .close, .quit, .copy, .selectAll, .find, .zoomIn, .zoomOut,
   .actualSize, .gotoPage]
#guard Cmd.all.all fun c => c.primaryKeys.all (·.primary)
-- Every Control binding stays on aqua and gets a Command twin; none elsewhere.
#guard Cmd.all.all fun c => c.primaryKeys.all fun k =>
  (k.sequences .other).all (fun q => (k.sequences .aqua).contains q) &&
  (k.sequences .aqua).any (fun q => (q.splitOn "Command-").length == 2) &&
  (k.sequences .other).all (fun q => (q.splitOn "Command").length == 1)
#guard Cmd.save.primaryKeys.flatMap (Key.sequences .other) == ["<Control-Key-s>"]
#guard Cmd.save.primaryKeys.flatMap (Key.sequences .aqua) == ["<Control-Key-s>", "<Command-Key-s>"]
#guard Cmd.saveAs.primaryKeys.flatMap (Key.sequences .other) == ["<Control-Key-S>"]
#guard Cmd.saveAs.primaryKeys.flatMap (Key.sequences .aqua) ==
  ["<Control-Key-S>", "<Command-Key-S>", "<Shift-Command-Key-s>"]
#guard Cmd.zoomIn.primaryKeys.flatMap (Key.sequences .aqua) ==
  ["<Control-Key-plus>", "<Command-Key-plus>", "<Control-Key-equal>", "<Command-Key-equal>",
   "<Control-Key-KP_Add>", "<Command-Key-KP_Add>"]
#guard Cmd.back.primaryKeys.isEmpty && (Cmd.highlight.key.map (Key.sequences .aqua)) == some []
-- Task 10.9: every command with a Ctrl key has Command keys on macOS (its twin, or the macOS
-- convention), and every macOS key uses Command.
#guard Cmd.all.all fun c => c.primaryKeys.isEmpty || !c.macKeys.isEmpty
#guard Cmd.all.all fun c => c.macKeys.all (·.primary)
#guard Action.all.all fun a => a.macKeys.all (·.primary) && a.x11Keys.all (!·.primary)
-- `Key.seqs` agrees with `Key.sequences` on the primary keys.
#guard Cmd.all.all fun c => c.primaryKeys.all fun k =>
  k.sequences .other == k.x11Seqs && k.sequences .aqua == k.x11Seqs ++ k.macSeqs
#guard (Cmd.all.filter fun c => c.macKeys != c.primaryKeys) ==
  [.highlight, .outline, .fitPage, .rotateCw, .rotateCcw, .firstPage, .lastPage, .gotoPage,
   .back, .forward]
#guard Cmd.gotoPage.macKeys.flatMap Key.macSeqs == ["<Option-Command-Key-g>"] &&
  Cmd.outline.macKeys.flatMap Key.macSeqs == ["<Control-Command-Key-s>"] &&
  Cmd.back.macKeys.flatMap Key.macSeqs == ["<Command-Key-bracketleft>"] &&
  Cmd.firstPage.macKeys.flatMap Key.macSeqs == ["<Command-Key-Up>"] &&
  Action.findPrev.macKeys.flatMap Key.macSeqs == ["<Command-Key-G>", "<Shift-Command-Key-g>"]
#guard Cmd.back.key.map Key.x11Seqs == some ["<Alt-Key-Left>"] &&
  Cmd.rotateCcw.key.map Key.x11Seqs == some ["<Key-R>"] &&
  Action.findPrev.x11Keys.flatMap Key.x11Seqs == ["<Shift-Key-F3>"]
-- No key runs two different scripts, on either platform; the macOS table extends the X11 one
-- (the Control bindings stay on aqua) and only by Command sequences.
#guard conflictFree (keyTable .other) && conflictFree (keyTable .aqua)
#guard (keyTable .other).all fun e => (keyTable .aqua).contains e
#guard (keyTable .aqua).all fun e => (keyTable .other).contains e ||
  (e.1.splitOn "Command-").length == 2
#guard (keyTable .other).all fun e => (e.1.splitOn "Command").length == 1
#guard (keyTable .aqua).contains ("<Command-Key-g>", Action.findNext.script) &&
  (keyTable .aqua).contains ("<Control-Key-g>", Cmd.gotoPage.script) &&
  (keyTable .aqua).contains ("<Option-Command-Key-g>", Cmd.gotoPage.script)
-- The script binds each command's own script; aqua adds Command+wheel and the Quit hook.
#guard ((platformScript .other).splitOn "Command").length == 1
#guard ((platformScript .aqua).splitOn "bind . {<Command-Key-s>} {::safepdf::emit save}").length == 2
#guard ((platformScript .aqua).splitOn "bind . {<Command-Key-S>} {::safepdf::emit saveAs}").length == 2
#guard ((platformScript .aqua).splitOn "bind . {<Command-Key-q>} {::safepdf::emit quit}").length == 2
#guard ((platformScript .aqua).splitOn "bind .find.e {<Command-Key-q>} {::safepdf::emit quit}").length == 2
#guard ((platformScript .aqua).splitOn "proc ::tk::mac::Quit {} {::safepdf::emit quit}").length == 2
-- Task 10.9 bindings: find next/previous on `.` and in the find bar, Go to page, ⌘. in dialogs.
#guard ((platformScript .aqua).splitOn "bind . {<Command-Key-g>} {::safepdf::emit find next $::safepdf::query}").length == 2
#guard ((platformScript .aqua).splitOn "bind .find.e {<Command-Key-G>} {::safepdf::emit find prev $::safepdf::query; break}").length == 2
#guard ((platformScript .aqua).splitOn "bind . {<Option-Command-Key-g>} ::safepdf::showGoto").length == 2
#guard ((platformScript .aqua).splitOn "bind . {<Command-Key-bracketleft>} {::safepdf::emit back}").length == 2
#guard ((platformScript .aqua).splitOn "proc ::safepdf::cancelBind {w script} {bind $w <Command-Key-period> $script}").length == 2
#guard ((platformScript .other).splitOn "proc ::safepdf::cancelBind {w script} {}").length == 2
#guard ((platformScript .aqua).splitOn (".pop entryconfigure Back -accelerator " ++ Tcl.quote "Command-[")).length == 2
#guard ((platformScript .aqua).splitOn ".pop entryconfigure Copy -accelerator Command-C").length == 2
#guard ((platformScript .other).splitOn ".pop entryconfigure Copy -accelerator Ctrl+C").length == 2
#guard ((platformScript .other).splitOn "{foreach m Control { bind $w").length == 2 &&
  ((platformScript .aqua).splitOn "{foreach m {Control Command} { bind $w").length == 2
#guard Platform.ofWindowingSystem "aqua\n" == .aqua && Platform.ofWindowingSystem "x11" == .other &&
  Platform.ofWindowingSystem "win32" == .other
#guard Platform.aqua.keyText "Save (Ctrl+S)" == "Save (⌘S)" &&
  Platform.aqua.keyText "Press Ctrl+Shift+S" == "Press ⇧⌘S" &&
  Platform.other.keyText "Save (Ctrl+S)" == "Save (Ctrl+S)"
#guard Platform.aqua.keyText "Toggle sidebar (F9)" == "Toggle sidebar (⌃⌘S)" &&
  Platform.other.keyText "Toggle sidebar (F9)" == "Toggle sidebar (F9)"

end SafePdf.Shell.App.Menu
