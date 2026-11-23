import SafePdf.Core.Doc.Attachments
import SafePdf.Shell.App.Links

/-!
# Attachments panel model (task 9.r10; Plan.md §6 Phase 9 "Look and feel: imitate PDF.js" — *Sidebar*, §10 `SafePdf/Shell/`)

The Tk-free part of the sidebar's attachments panel (unverified shell code, total, checked by
`#guard`s). The data comes from the verified `Core.Doc.Attachments` (names already
sanitized, sizes, problems); `Viewer` draws it as a list after PDF.js's attachments view
(`web/pdf_attachment_viewer.js`: one row per file, double-click saves it).

* **Lazy decoding** (`Probe`): listing decodes nothing. The size column shows the size known
  without decoding (`Attachments.listedSize`: `/Params /Size`, `/DL`, or the stored length of
  an unfiltered stream), else `?` until the file is decoded; `—` for an entry without a
  stream. A file is decoded only when it is saved, or probed when its tooltip opens — under
  the viewer's limits with the per-stream cap lowered to `probeLimit` (16 MB), so hovering
  never decodes more than that (a larger file is `Probe.large` and decoded only when saved).
  A probe's or a save's result is kept per row.
* **Rows** (`sizeColumn`, `tooltip`): the name, the size column, and a tooltip with the
  description, MIME type, dates, the page of its annotation, the stored size of a compressed
  file whose size is not known yet, and the problem or decoding error (one line each).
* **Saving** (`targetProblem`): "Save attachment as…" writes the decoded bytes to a file the
  user chose (`tk_getSaveFile`, starting with `Attachment.fileName`). Refused: a folder, the
  opened PDF itself, a read-only file, a folder that is not writable (the same rules as task
  9.r6's Save As and Export). The viewer **never opens, launches or executes** an attachment;
  there is no "open with" action.
* **Icons** (`iconAt`): a click on a file attachment annotation's rectangle selects its row
  (the topmost icon, last in `/Annots` order, wins).
-/

namespace SafePdf.Shell.App.Attach

open SafePdf.Core.Doc.Attachments (Attachment Icon sizeText listedSize)
open SafePdf.Core.Raster.Geom (Pt Box)

/-- The per-stream decoding cap of a tooltip probe (16 MB). -/
def probeLimit : Nat := 16 <<< 20

/-- What decoding an attachment gave. -/
inductive Probe where
  /-- Decoded: its size. -/
  | decoded (n : Nat)
  /-- Does not decode: the error text. -/
  | failed (msg : String)
  /-- Larger than `probeLimit` (a probe only; decoded when saved). -/
  | large
  deriving DecidableEq, Repr, Inhabited

/-- The size column of a row (`none`: not decoded yet). -/
def sizeColumn (a : Attachment) (pr : Option Probe) : String :=
  match listedSize a, pr with
  | some n, _ => sizeText n
  | none, some (.decoded n) => sizeText n
  | none, some (.failed _) => "error"
  | none, some .large => "> 16 MB"
  | none, none => if a.stream.isNone then "—" else "?"

/-- The tooltip of a row: description, type, dates, page, stored size, problem or error; one
line each. Empty when there is nothing to say. -/
def tooltip (a : Attachment) (pr : Option Probe) : String :=
  let stored : List String :=
    match listedSize a, pr, a.stored with
    | none, none, some n => [s!"Stored: {sizeText n} (compressed)"]
    | _, _, _ => []
  let ls : List String :=
    (a.desc.toList) ++
    (a.mime.toList.map (s!"Type: {·}")) ++
    (a.created.toList.map (s!"Created: {·}")) ++
    (a.modified.toList.map (s!"Modified: {·}")) ++
    (a.page.toList.map (s!"Attached on page {· + 1}")) ++ stored ++
    (match a.problem, pr with
      | some p, _ => [p.message]
      | none, some (.failed e) => [s!"Cannot be decoded: {e}"]
      | none, some .large => ["Larger than 16 MB: decoded when saved"]
      | none, _ => [])
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
def selectedText (a : Attachment) (pr : Option Probe) : String :=
  let what := match a.problem, pr with
    | some p, _ => p.message
    | none, some (.failed e) => s!"cannot be decoded: {e}"
    | none, _ => "double-click or right-click → Save attachment as… to save it"
  s!"attachment {a.name} ({sizeColumn a pr}): {what}"

#guard sizeColumn { name := "a", fileName := "a", size := some 1500 } (some (.decoded 3)) == "1.5 KB"
#guard sizeColumn { name := "a", fileName := "a", stream := some (4, 0), filtered := true } (some (.decoded 3)) == "3 B"
#guard sizeColumn { name := "a", fileName := "a", stream := some (4, 0), filtered := true, stored := some 9 } none == "?"
#guard sizeColumn { name := "a", fileName := "a", stream := some (4, 0), stored := some 9 } none == "9 B"
#guard sizeColumn { name := "a", fileName := "a", stream := some (4, 0), filtered := true, dl := some 7 } none == "7 B"
#guard sizeColumn { name := "a", fileName := "a" } none == "—"
#guard sizeColumn { name := "a", fileName := "a", stream := some (4, 0), filtered := true } (some (.failed "x")) == "error"
#guard tooltip { name := "a", fileName := "a", desc := some "D", mime := some "text/plain", page := some 2 }
    (some (.decoded 1)) == "D\nType: text/plain\nAttached on page 3"
#guard tooltip { name := "a", fileName := "a", stream := some (4, 0), filtered := true, stored := some 2048 } none ==
  "Stored: 2.0 KB (compressed)"
#guard tooltip { name := "a", fileName := "a", stream := some (4, 0) } (some (.failed "limit")) ==
  "Cannot be decoded: limit"
#guard tooltip { name := "a", fileName := "a" } (some (.decoded 0)) == ""
#guard targetProblem "x" false true false true false == some "x is read-only; choose another name"
#guard targetProblem "x" false false false true true == some "x is the opened document; choose another name"
#guard targetProblem "x" true false false true false == some "x is a folder; choose a file name"
#guard targetProblem "x" false false false false false ==
  some "the folder of x is not writable; choose another folder"
#guard targetProblem "x" false true true true false == none

end SafePdf.Shell.App.Attach
