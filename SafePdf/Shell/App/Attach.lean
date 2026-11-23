import SafePdf.Core.Doc.Attachments
import SafePdf.Shell.App.Links

/-!
# Attachments panel model (task 9.r10; Plan.md §6 Phase 9 "Look and feel: imitate PDF.js" — *Sidebar*, §10 `SafePdf/Shell/`)

The Tk-free part of the sidebar's attachments panel (unverified shell code, total, checked by
`#guard`s). The data comes from the verified `Core.Doc.Attachments` (names already
sanitized, sizes, problems); `Viewer` draws it as a list after PDF.js's attachments view
(`web/pdf_attachment_viewer.js`: one row per file, double-click saves it).

* **Rows** (`sizeColumn`, `tooltip`): the name, a size column (`/Params /Size`, else the
  decoded length; `—` for an entry without a stream, `error` when it does not decode), and a
  tooltip with the description, MIME type, dates, the page of its annotation and the problem
  or decoding error (one line each).
* **Saving** (`targetProblem`): "Save attachment as…" writes the decoded bytes to a file the
  user chose (`tk_getSaveFile`, starting with `Attachment.fileName`). Refused: a folder, the
  opened PDF itself, a read-only file, a folder that is not writable (the same rules as task
  9.r6's Save As and Export). The viewer **never opens, launches or executes** an attachment;
  there is no "open with" action.
* **Icons** (`iconAt`): a click on a file attachment annotation's rectangle selects its row
  (the topmost icon, last in `/Annots` order, wins).
-/

namespace SafePdf.Shell.App.Attach

open SafePdf.Core.Doc.Attachments (Attachment Icon sizeText)
open SafePdf.Core.Raster.Geom (Pt Box)

/-- What decoding an entry gave: its decoded size, or the error text. -/
abbrev Status := Except String Nat

/-- The size column of a row. -/
def sizeColumn (a : Attachment) (st : Status) : String :=
  match a.size, st with
  | some n, _ => sizeText n
  | none, .ok n => sizeText n
  | none, .error _ => if a.stream.isNone then "—" else "error"

/-- The tooltip of a row: description, type, dates, page, problem or error; one line each.
Empty when there is nothing to say. -/
def tooltip (a : Attachment) (st : Status) : String :=
  let ls : List String :=
    (a.desc.toList) ++
    (a.mime.toList.map (s!"Type: {·}")) ++
    (a.created.toList.map (s!"Created: {·}")) ++
    (a.modified.toList.map (s!"Modified: {·}")) ++
    (a.page.toList.map (s!"Attached on page {· + 1}")) ++
    (match a.problem, st with
      | some p, _ => [p.message]
      | none, .error e => [s!"Cannot be decoded: {e}"]
      | none, .ok _ => [])
  "\n".intercalate ls

/-- Why a chosen file cannot take the attachment (task 9.r6's rules for save dialogs), or
`none`. -/
def targetProblem (name : String) (isDir «exists» fileWritable dirWritable opened : Bool) :
    Option String :=
  if isDir then some s!"{name} is a folder; choose a file name"
  else if opened then some s!"{name} is the opened document; choose another name"
  else if «exists» && !fileWritable then some s!"{name} is read-only; choose another name"
  else if !dirWritable then some s!"the folder of {name} is not writable; choose another folder"
  else none

/-- The row of the topmost icon on page `pg` containing page point `p`. -/
def iconAt (icons : List Icon) (pg : Nat) (p : Pt) : Option Nat :=
  icons.foldl (fun acc i =>
    if i.page == pg && Links.Box.contains (Box.ofRect i.rect) p then some i.entry else acc) none

/-- The status line text of a selected row. -/
def selectedText (a : Attachment) (st : Status) : String :=
  let what := match a.problem, st with
    | some p, _ => p.message
    | none, .error e => s!"cannot be decoded: {e}"
    | none, .ok _ => "double-click or right-click → Save attachment as… to save it"
  s!"attachment {a.name} ({sizeColumn a st}): {what}"

#guard sizeColumn { name := "a", fileName := "a", size := some 1500 } (.ok 3) == "1.5 KB"
#guard sizeColumn { name := "a", fileName := "a" } (.ok 3) == "3 B"
#guard sizeColumn { name := "a", fileName := "a" } (.error "x") == "—"
#guard sizeColumn { name := "a", fileName := "a", stream := some (4, 0) } (.error "x") == "error"
#guard tooltip { name := "a", fileName := "a", desc := some "D", mime := some "text/plain", page := some 2 }
    (.ok 1) == "D\nType: text/plain\nAttached on page 3"
#guard tooltip { name := "a", fileName := "a", stream := some (4, 0) } (.error "limit") ==
  "Cannot be decoded: limit"
#guard tooltip { name := "a", fileName := "a" } (.ok 0) == ""
#guard targetProblem "x" false true false true false == some "x is read-only; choose another name"
#guard targetProblem "x" false false false true true == some "x is the opened document; choose another name"
#guard targetProblem "x" true false false true false == some "x is a folder; choose a file name"
#guard targetProblem "x" false false false false false ==
  some "the folder of x is not writable; choose another folder"
#guard targetProblem "x" false true true true false == none

end SafePdf.Shell.App.Attach
