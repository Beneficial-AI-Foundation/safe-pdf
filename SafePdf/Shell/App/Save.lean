import SafePdf.Shell.App.Marks
import SafePdf.Shell.Views.Common
import SafePdf.Core.Write.Annots
import SafePdf.Core.Doc.Nav
import SafePdf.Api
import Std.Time.DateTime.Timestamp

/-!
# Saving marks into the PDF (task 9.5c; Plan.md §4 S8/C7, §6 Phase 9 "Persistence — annotations inside the PDF", §10 `SafePdf/Shell/`)

The Tk-free save flow of the viewer (unverified shell code; the pure parts are checked by
`#guard`s). The viewer (`Viewer.save`) asks the questions; this module converts, writes,
checks and stores.

* **Conversion** (`toCore`): a `Marks.Mark` becomes a `Core.Write.Annots.Mark` — quads
  (`Quad.ofBox` of each page-space box), `/Rect` (a note's icon box `Mark.iconBox` inside the
  page's CropBox, as the viewer draws it; a highlight's is the union of its quads, computed by
  the writer), `/C` (`Color.unit`), opacity 1, `/Contents` (a note's text), the id (`/NM` =
  `safepdf-mark-ID`) and the date. A highlight's comment (the note anchored to its quads with
  a text, `Marks.Store.commentOf`, task 9.8) is written **into the highlight** as pdf.js does:
  `/Contents` + a `/Popup` annotation (rule A3 of 9.5b) whose `/NM`
  `safepdf-mark-ID-popup-CID` carries the comment note's id (rule A11, task 9.5g). Other
  notes are `/Text` annotations with `/QuadPoints` for their anchor (rule A2). Files saved by
  older builds (9.5c: the comment as a separate `/Text`) are still read; their comment note is
  moved into the highlight on the next save (its `/Text` reference removed).
* **Date** (`pdfDate`): the current UTC time as `D:YYYYMMDDHHmmSSZ` (§7.9.4), from
  `Std.Time.Timestamp.now` (wall clock) and the civil-from-days conversion `civil`.
  **Author**: none — no `/T` is written, so a saved file does not carry the login name.
* **One update with additions, supersessions and removals** (`edits`, task 9.5g; writer rule
  W11, `Annots.writeEdits`): the file's own marks are scanned (`scan`: object reference,
  popup, comment, `/CreationDate` of each of our annotations) and compared with the store.
  A mark not in the file is **added**; a mark in the file whose colour, text or comment
  differs is **superseded** (its annotation re-emitted under its own object number with a new
  dictionary and appearance stream, `/CreationDate` kept); an annotation of ours whose mark
  is gone (deleted, or a comment now written into its highlight) is **removed** from its
  page's `/Annots` together with its popup. Unchanged marks are not written again. Marks
  stored as direct dictionaries in `/Annots` (not written by us) cannot be changed: Save
  refuses with a message.
* **Preview** (`preview`): while saved marks are edited, the viewer renders the document as
  the next save would write it with only those edits (no additions — new marks are drawn
  by the viewer itself), built in memory by the same writer and reopened strictly, so a
  recoloured or deleted saved mark shows at once.
* **Check before writing** (`write`): the writer's output must start with the original bytes
  (S8; the writer guarantees it, C7, and it is checked again here), must reopen through the
  **strict** parser (`Api.openBytes` with `allowRepair := false`), and reading the marks back
  (`readMarks`) must give every mark of the store (`sameMark`: page, kind, colour, text, quads
  and icon box within 1/500 of a unit — the writer rounds coordinates to 1/1000; a comment
  note takes its highlight's colour), each written id exactly once, and no deleted id. Only
  then is the file written.
* **Atomic write** (`writeAtomic`): the bytes go into a new temporary file in the target's
  directory (`.NAME.safepdf-N.tmp`, created exclusively), which is then renamed over the
  target; on any error the temporary file is removed and the target is untouched. A file is
  never truncated in place.
* **Default target** (`defaultTarget`): `DIR/STEM-annotated.pdf` next to the opened file;
  for a file whose stem already ends in `-annotated` the file itself (a further revision of
  it). The viewer asks before writing over the opened file unless it wrote it itself in this
  session, and before replacing another existing file.
* **Reading marks back** (`readMarks`): the annotations of every page's own `/Annots`
  (resolved one level, at most `Annot.maxAnnots` per page) whose `/NM` is
  `safepdf-mark-ID` (`Marks.idOfNm`; our popups `safepdf-mark-ID-popup[-CID]` and everybody
  else's annotations are left to the renderer): `/Subtype /Highlight` → a highlight over the
  boxes of its `/QuadPoints`, and when it has a non-empty `/Contents` also its comment: a note
  with that text anchored to the same quads, in the highlight's colour, with the id `CID`
  from its popup's `/NM` (a popup without one — files written by Core directly — gets a
  fresh id after every other id of the file, in scan order); `/Subtype /Text` → a note with
  `/Contents`, anchored to its `/QuadPoints` when it has any (rule A2 of 9.5b), else to the
  upper-left corner of its `/Rect`; the colour is the palette colour nearest to `/C`
  (`nearestColor`).
-/

namespace SafePdf.Shell.App.Save

open SafePdf.Core
open SafePdf.Core.Raster.Geom (Pt Box)
open SafePdf.Shell.App.Marks (Mark Color Store)

/-! ## Dates -/

/-- `(year, month, day)` of the day `days` after 1970-01-01 (proleptic Gregorian; Howard
Hinnant's `civil_from_days`). -/
def civil (days : Int) : Int × Nat × Nat :=
  let z := days + 719468
  let era := (if z ≥ 0 then z else z - 146096) / 146097
  let doe := z - era * 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let d := doy - (153 * mp + 2) / 5 + 1
  let m := if mp < 10 then mp + 3 else mp - 9
  let y := yoe + era * 400 + (if m ≤ 2 then 1 else 0)
  (y, m.toNat, d.toNat)

/-- `n` with at least `w` digits (zero-padded). -/
def pad (w : Nat) (n : Nat) : String :=
  let s := toString n
  String.ofList (List.replicate (w - s.length) '0') ++ s

/-- **The PDF date** (§7.9.4) of `secs` seconds after the Unix epoch, in UTC:
`D:YYYYMMDDHHmmSSZ`. -/
def pdfDate (secs : Int) : String :=
  let days := if secs ≥ 0 then secs / 86400 else -((-secs + 86399) / 86400)
  let rem := (secs - days * 86400).toNat
  let (y, mo, d) := civil days
  s!"D:{pad 4 y.toNat}{pad 2 mo}{pad 2 d}{pad 2 (rem / 3600)}{pad 2 (rem / 60 % 60)}{pad 2 (rem % 60)}Z"

#guard pdfDate 0 == "D:19700101000000Z"
#guard pdfDate 951782400 == "D:20000229000000Z"
#guard pdfDate 1795185854 == "D:20261120144414Z"
#guard pdfDate (1795185854 + 41 * 86400 + 15 * 3600) == "D:20270101054414Z"
#guard pdfDate (-1) == "D:19691231235959Z"

/-- The current time as a PDF date (UTC). -/
def nowDate : IO String := do
  let t ← Std.Time.Timestamp.now
  return pdfDate t.toSecondsSinceUnixEpoch.val

/-! ## Marks → Core mark records -/

/-- A page-space box as a writer quad (upper-left, upper-right, lower-left, lower-right). -/
def quadOf (b : Box) : Write.Annots.Quad := Write.Annots.Quad.ofBox b.llx b.lly b.urx b.ury

/-- **The Core record of a mark** on a page with CropBox `pb`, dated `date`, without author;
`none` for a highlight without quads or a note without an icon box. A highlight's
`comment` (the comment note, `Store.commentOf`) becomes its `/Contents` and popup (rule A3,
with the note's id, rule A11). -/
def toCore (pb : Box) (date : String) (m : Mark) (comment : Option Mark := none) :
    Option Write.Annots.Mark :=
  match m.kind with
  | .highlight qs =>
    if qs.isEmpty then none
    else some { page := m.page, kind := .highlight, quads := qs.map quadOf,
                rect := ⟨0, 0, 0, 0⟩, color := m.color.unit, id := m.id, date,
                contents := (comment.map (·.text)).getD "",
                commentId := comment.map (·.id) }
  | .note t _ =>
    (m.iconBox pb).map fun ib =>
      { page := m.page, kind := .note, quads := m.quads.map quadOf,
        rect := ⟨ib.llx, ib.lly, ib.urx, ib.ury⟩, color := m.color.unit, contents := t,
        id := m.id, date }

/-- The CropBox of page `i` (the box the viewer places note icons in). -/
def pageBox (doc : Doc.Doc) (i : Nat) : Option Box :=
  doc.pages[i]?.map fun p => Box.ofRect p.cropBox

/-! ## Reading marks back -/

/-- The palette colour nearest to `/C` components `cs` (yellow when `/C` is not three
numbers). -/
def nearestColor (cs : List Rat) : Color :=
  match cs with
  | [r, g, b] =>
    let dist (c : Color) : Rat :=
      let (r', g', b') := c.unit
      (r - r') * (r - r') + (g - g') * (g - g') + (b - b') * (b - b')
    Color.all.foldl (fun best c => if dist c < dist best then c else best) .yellow
  | _ => .yellow

#guard Color.all.all fun c => let (r, g, b) := c.unit; nearestColor [r, g, b] == c
#guard nearestColor [1, 1, 5961 / 10000] == .yellow && nearestColor [1, 0, 0] == .red &&
  nearestColor [] == .yellow

/-- The page-space boxes of `/QuadPoints` (8 numbers per quad; the bounding box of each
quad's four points; a trailing partial quad is ignored). -/
def boxesOf : List Rat → List Box
  | x1 :: y1 :: x2 :: y2 :: x3 :: y3 :: x4 :: y4 :: rest =>
    ⟨min (min x1 x2) (min x3 x4), min (min y1 y2) (min y3 y4),
     max (max x1 x2) (max x3 x4), max (max y1 y2) (max y3 y4)⟩ :: boxesOf rest
  | _ => []

#guard boxesOf [100, 708, 166, 708, 100, 698, 166, 698, 1, 2] == [⟨100, 698, 166, 708⟩]

/-- The text of a text-string value (empty when it is not a string). -/
def textOf (o : PdfObject) : String :=
  match o with
  | .string bs => Api.textString bs
  | _ => ""

/-- The mark of one annotation dictionary `ad` on page `page`, when it is one of ours. -/
def markOf (doc : Doc.Doc) (limits : Limits) (page : Nat) (ad : Dict) : Option Mark := do
  let get := Doc.Nav.getL doc limits ad
  let nmStr ← match get "NM" with
    | .string bs => some (Api.textString bs)
    | _ => none
  let id ← Marks.idOfNm nmStr
  let nums (o : PdfObject) : List Rat := match o with
    | .array xs => xs.filterMap fun x => (Doc.numOf x).map Raster.Geom.decimalToRat
    | _ => []
  let quads := boxesOf (nums (get "QuadPoints"))
  let color := nearestColor (nums (get "C"))
  match get "Subtype" with
  | .name n =>
    if n == Name.ofString "Highlight" then
      if quads.isEmpty then none else some ⟨id, page, color, .highlight quads⟩
    else if n == Name.ofString "Text" then
      let text := textOf (get "Contents")
      if quads.isEmpty then
        let r ← Doc.rectOf (get "Rect")
        let b := Box.ofRect r
        some ⟨id, page, color, .note text (.point ⟨b.llx, b.ury⟩)⟩
      else some ⟨id, page, color, .note text (.quads quads)⟩
    else none
  | _ => none

/-- One of our annotations in the file (task 9.5g). -/
structure Entry where
  /-- The mark as read (a highlight, or a `/Text` note). -/
  mark : Mark
  /-- Its object, when `/Annots` refers to it indirectly (else it cannot be changed). -/
  ref : Option (Nat × Nat)
  /-- A highlight's `/Popup` object. -/
  popup : Option (Nat × Nat) := none
  /-- A highlight's comment text (`/Contents`, empty for none). -/
  comment : String := ""
  /-- The comment note's id from the popup's `/NM` (rule A11). -/
  commentId : Option Nat := none
  /-- `/CreationDate`, kept when the annotation is superseded. -/
  created : String := ""
  deriving Inhabited

/-- The comment id in a popup `/NM` `safepdf-mark-ID-popup-CID` (rule A11). -/
def commentIdOf (id : Nat) (popupNm : String) : Option Nat :=
  let pre := Marks.nmPrefix ++ toString id ++ "-popup-"
  if popupNm.startsWith pre then (popupNm.drop pre.length).toString.toNat? else none

#guard commentIdOf 4 "safepdf-mark-4-popup-9" == some 9 &&
  commentIdOf 4 "safepdf-mark-4-popup" == none && commentIdOf 4 "safepdf-mark-5-popup-9" == none

/-- The entry of `/Annots` element `a` on page `page`, when it is one of ours. -/
def entryOf (doc : Doc.Doc) (limits : Limits) (page : Nat) (a : PdfObject) : Option Entry := do
  let .dict ad := Doc.Nav.res doc limits a | none
  let m ← markOf doc limits page ad
  let ref := match a with
    | .ref n g => some (n, g)
    | _ => none
  let created := match Doc.Nav.getL doc limits ad "CreationDate" with
    | .string bs => String.fromUTF8? ⟨bs.toArray⟩ |>.getD ""
    | _ => ""
  if m.isNote then return { mark := m, ref, created }
  let popup := match Doc.Nav.raw ad "Popup" with
    | some (.ref n g) => some (n, g)
    | _ => none
  let popNm := match Doc.Nav.raw ad "Popup" with
    | some o => match Doc.Nav.res doc limits o with
      | .dict pd => textOf (Doc.Nav.getL doc limits pd "NM")
      | _ => ""
    | none => ""
  return { mark := m, ref, popup, comment := textOf (Doc.Nav.getL doc limits ad "Contents"),
           commentId := commentIdOf m.id popNm, created }

/-- **Our annotations in `doc`**, page by page in `/Annots` order (see the module doc). -/
def scan (doc : Doc.Doc) (limits : Limits) : List Entry :=
  (List.range doc.pages.size).flatMap fun i =>
    match doc.pages[i]? with
    | none => []
    | some p =>
      match Doc.Nav.fetchDict doc limits p.num p.gen with
      | none => []
      | some pd =>
        match Doc.Nav.getL doc limits pd "Annots" with
        | .array xs => (xs.take Annot.maxAnnots).filterMap (entryOf doc limits i)
        | _ => []

/-- The marks of scanned entries: each highlight followed by its comment note (rule A11;
comments without an id get fresh ids after every other id, in order). -/
def marksOf (es : List Entry) : List Mark :=
  let top := es.foldl (fun t e => max t (max e.mark.id (e.commentId.getD 0))) 0
  let step (acc : List Mark × Nat) (e : Entry) : List Mark × Nat :=
    let (ms, next) := acc
    if e.mark.isNote || e.comment.isEmpty then (ms ++ [e.mark], next)
    else
      let (cid, next) := match e.commentId with
        | some c => (c, next)
        | none => (next, next + 1)
      (ms ++ [e.mark, ⟨cid, e.mark.page, e.mark.color, .note e.comment (.quads e.mark.quads)⟩],
        next)
  (es.foldl step ([], top + 1)).1

/-- **Our marks in `doc`**, page by page in `/Annots` order (see the module doc). -/
def readMarks (doc : Doc.Doc) (limits : Limits) : List Mark := marksOf (scan doc limits)

/-! ## Checks -/

/-- Tolerance of the read-back comparison (the writer rounds to 1/1000). -/
def tol : Rat := 1 / 500

/-- Two lists of numbers agree within `tol`. -/
def close (a b : List Rat) : Bool :=
  a.length == b.length && (a.zip b).all fun (x, y) => x - y ≤ tol && y - x ≤ tol

/-- A box as four numbers. -/
def boxNums (b : Box) : List Rat := [b.llx, b.lly, b.urx, b.ury]

/-- Whether `got` (read back) is the mark `m` (page box `pb`): id, page, colour, kind, text,
quads and note icon box. -/
def sameMark (pb : Box) (m got : Mark) : Bool :=
  m.id == got.id && m.page == got.page && m.color == got.color && m.isNote == got.isNote &&
  m.text == got.text && close m.quadPoints got.quadPoints &&
  close ((m.iconBox pb).map boxNums |>.getD []) ((got.iconBox pb).map boxNums |>.getD [])

/-- The first problem of a read-back: `got` must contain every mark of `want` (`sameMark`),
the ones in `fresh` (the ids just written) exactly once, and none of `gone` (the ids just
deleted). `none` when all is well. -/
def verify (box : Nat → Option Box) (want : List Mark) (fresh : List Nat) (got : List Mark)
    (gone : List Nat := []) : Option String :=
  (gone.findSome? fun id =>
    if got.any (·.id == id) then some s!"deleted mark {id} is still in the written file"
    else none) <|>
  want.findSome? fun m =>
    let found := got.filter (·.id == m.id)
    match found with
    | [] => some s!"mark {m.id} is missing after the write"
    | g :: _ =>
      if fresh.contains m.id && found.length != 1 then
        some s!"mark {m.id} is in the written file {found.length} times"
      else if sameMark ((box m.page).getD ⟨0, 0, 612, 792⟩) m g then none
      else some s!"mark {m.id} reads back differently"

/-! ## Paths and the atomic write -/

/-- The default file Save writes (see the module doc). -/
def defaultTarget (path : String) : String :=
  let fp : System.FilePath := path
  let stem := fp.fileStem.getD "document"
  if stem.endsWith "-annotated" then path
  else
    let name := stem ++ "-annotated.pdf"
    match fp.parent with
    | some d => if d.toString.isEmpty then name else (d / name).toString
    | none => name

#guard defaultTarget "/tmp/x/paper.pdf" == "/tmp/x/paper-annotated.pdf"
#guard defaultTarget "paper.PDF" == "paper-annotated.pdf"
#guard defaultTarget "a/b.c.pdf" == "a/b.c-annotated.pdf"
#guard defaultTarget "/tmp/x/paper-annotated.pdf" == "/tmp/x/paper-annotated.pdf"

/-- Writes `bytes` to `path` through a new temporary file in the same directory and a rename
(never truncating the target in place); the temporary file is removed on failure. -/
def writeAtomic (path : String) (bytes : ByteArray) : IO Unit := do
  let fp : System.FilePath := path
  let dir : System.FilePath := match fp.parent with
    | some d => if d.toString.isEmpty then "." else d
    | none => "."
  let base := fp.fileName.getD "document.pdf"
  let tmp := dir / s!".{base}.safepdf-{← IO.monoNanosNow}.tmp"
  try
    let h ← IO.FS.Handle.mk tmp .writeNew
    h.write bytes
    h.flush
    IO.FS.rename tmp fp
  catch e =>
    try IO.FS.removeFile tmp catch _ => pure ()
    throw e

/-! ## Saving -/

/-- What a save did. -/
structure Outcome where
  /-- The file written. -/
  path : String
  /-- Number of marks written (added or changed) or deleted in this update. -/
  marks : Nat
  /-- Bytes appended to the original (0: a plain copy, nothing new). -/
  appended : Nat
  /-- Size of the written file. -/
  size : Nat
  /-- All marks the written file holds (read back). -/
  total : Nat

/-- Whether `pre` is a prefix of `bs`. -/
def isPrefix (pre bs : ByteArray) : Bool :=
  pre.size ≤ bs.size && (bs.extract 0 pre.size).data == pre.data

/-- The store as Save writes it: a comment note takes its highlight's colour (the popup
form has none of its own). -/
def normalize (store : Store) : List Mark :=
  let hs := store.marks.toList.filter (!·.isNote)
  store.marks.toList.map fun m =>
    match hs.find? fun h => h.page == m.page && ((store.commentOf h).map (·.id)) == some m.id with
    | some h => { m with color := h.color }
    | none => m

/-- What one save does (task 9.5g): the Core edit set, the ids it writes (added or
superseded marks and comments) and the ids it deletes. -/
structure Plan where
  /-- The Core edit set. -/
  edits : Write.Annots.EditSet := {}
  /-- Ids written. -/
  written : List Nat := []
  /-- Ids deleted. -/
  gone : List Nat := []

/-- **The edits that bring the file `doc` (its entries `file`) to the store** (see the module
doc); with `adds := false` only the changes of saved marks (the preview). -/
def edits (doc : Doc.Doc) (file : List Entry) (store : Store) (date : String)
    (adds : Bool := true) : Except String Plan := do
  let ms := store.marks.toList
  let comments := ms.filterMap fun m => if m.isNote then none else store.commentOf m
  let folded (n : Mark) : Bool := comments.any (·.id == n.id)
  let fileOf (m : Mark) : Option Entry :=
    file.find? fun e => e.mark.id == m.id && e.mark.isNote == m.isNote
  let mut plan : Plan := {}
  for m in ms do
    if m.isNote && folded m then continue
    let some pb := pageBox doc m.page
      | throw s!"mark {m.id}: page {m.page + 1} is not in the document"
    let comment := if m.isNote then none else store.commentOf m
    let some c := toCore pb date m comment
      | throw s!"mark {m.id} cannot be written (no quads or icon)"
    let cids := (comment.map (·.id)).toList
    match fileOf m with
    | none =>
      if adds then
        plan := { plan with edits := { plan.edits with adds := plan.edits.adds ++ [c] },
                            written := plan.written ++ m.id :: cids }
    | some e =>
      let fileComment := if e.comment.isEmpty then none else some (e.commentId, e.comment)
      let wantComment := comment.map fun n => (some n.id, n.text)
      let same := e.mark.color == m.color && e.mark.text == m.text &&
        (m.isNote || fileComment == wantComment)
      if !same then
        let some ref := e.ref
          | throw s!"mark {m.id} is stored directly in the page's /Annots and cannot be changed"
        let sm : Write.Annots.SupMark := ⟨{ c with created := e.created }, ref, e.popup⟩
        plan := { plan with edits := { plan.edits with sups := plan.edits.sups ++ [sm] },
                            written := plan.written ++ m.id :: cids }
  -- Our annotations whose mark is gone (deleted, or a comment now in its highlight).
  for e in file do
    let keep := ms.any fun m => m.id == e.mark.id && m.isNote == e.mark.isNote &&
      !(m.isNote && folded m)
    if !keep then
      let some ref := e.ref
        | throw s!"mark {e.mark.id} is stored directly in the page's /Annots and cannot be deleted"
      let gone := if ms.any (·.id == e.mark.id) then [] else [e.mark.id]
      let goneC := match e.commentId with
        | some c => if ms.any (·.id == c) then [] else [c]
        | none => []
      plan := { plan with
        edits := { plan.edits with
          removes := plan.edits.removes ++ Write.Annots.removeMark e.mark.page ref e.popup },
        gone := plan.gone ++ gone ++ goneC }
  return plan

/-- Whether an edit set changes nothing. -/
def Plan.isEmpty (p : Plan) : Bool :=
  p.edits.adds.isEmpty && p.edits.sups.isEmpty && p.edits.removes.isEmpty

/-- The bytes Save would write for the store's changes (`bytes` unchanged when there are
none), checked as described in the module doc; an error message otherwise. Also returns the
marks read back and the number of marks written or deleted. -/
def build (limits : Limits) (doc : Doc.Doc) (store : Store) (date : String) :
    Except String (ByteArray × List Mark × Nat) := do
  let plan ← edits doc (scan doc limits) store date
  let orig := doc.file.bytes
  let out ← if plan.isEmpty then pure orig
    else match Write.Annots.writeEdits limits doc plan.edits with
      | .ok b => pure b
      | .error e => throw (renderError e)
  if !isPrefix orig out then throw "internal: the original bytes are not a prefix of the result"
  let d ← match Api.openBytes out { limits, allowRepair := false } with
    | .ok d => pure d
    | .error e => throw s!"the result does not reopen strictly: {e.message}"
  let got := readMarks d.doc limits
  match verify (pageBox d.doc) (normalize store) plan.written got plan.gone with
  | some msg => throw msg
  | none => return (out, got, plan.written.length + plan.gone.length)

/-- **The preview** (task 9.5g): `doc` with only the changes of saved marks applied (an
in-memory incremental update, reopened strictly); `none` when there are none. -/
def preview (limits : Limits) (doc : Doc.Doc) (store : Store) (date : String) :
    Except String (Option Doc.Doc) := do
  let plan ← edits doc (scan doc limits) store date (adds := false)
  if plan.isEmpty then return none
  let out ← match Write.Annots.writeEdits limits doc plan.edits with
    | .ok b => pure b
    | .error e => throw (renderError e)
  match Api.openBytes out { limits, allowRepair := false } with
  | .ok d => return some d.doc
  | .error e => throw s!"the preview does not reopen strictly: {e.message}"

/-- **Save**: builds and checks the bytes for the store's changes (`build`), then writes
them to `target` atomically. -/
def write (limits : Limits) (doc : Doc.Doc) (store : Store) (target : String) :
    IO (Except String Outcome) := do
  let date ← nowDate
  match build limits doc store date with
  | .error e => return .error e
  | .ok (bytes, got, n) =>
    try
      writeAtomic target bytes
      return .ok { path := target, marks := n,
                   appended := bytes.size - doc.file.bytes.size, size := bytes.size,
                   total := got.length }
    catch e => return .error s!"cannot write {target}: {e}"

end SafePdf.Shell.App.Save
