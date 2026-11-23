import SafePdf.Shell.App.Marks
import SafePdf.Shell.Views.Common
import SafePdf.Core.Write.Annots
import SafePdf.Core.Doc.Nav
import SafePdf.Api
import SafePdf.Shell.Read
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
* **Free text and ink** (task 9.9): free text becomes `/FreeText` (rules A12/A13: `/Contents`,
  `/DA` with the font size and colour, the box `Core.Write.Annots.freeTextBox` at its
  upper-left corner, a Helvetica appearance), ink becomes `/Ink` (rules A14/A15: `/InkList`
  one array per stroke, `/BS /W`, `/C`, `/CA` from the opacity percentage). Read back: the
  text from `/Contents`, size and colour from `/DA` (`Core.Annot.parseDA`, size and bytes
  rounded), the position from `/Rect`'s upper-left corner; the strokes from `/InkList`, the
  thickness from `/BS /W`, colour from `/C`, opacity from `/CA` (1 when absent). Moving,
  editing the text or changing size/colour supersedes the annotation (W11) like a recolour.
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
* **Fresh AES IVs** (task 12.4, `Core.Write.Encrypt` rule E3'): every save of an encrypted
  document takes fresh bytes from the operating system (`freshSeed`: 32 bytes of
  `/dev/urandom` followed by 32 bytes of Lean's `IO.getRandomBytes` — libuv's `uv_random`,
  `getentropy` on macOS; a source that fails is left out, and an encrypted document is not
  saved when both fail) and passes them to the pure writer as its IV seed (`build … ivSeed`,
  `buildNow`, `seedFor`). Saving the same marks twice thus gives different ciphertexts. The
  preview (never written) uses the empty seed.
* **Protection policy** (task 12.4; `protection`, `notes`, `refusal`): what Save says or does
  about the document's encryption and signatures.
  - *AES-128 / AES-256* (`/AESV2`, `/AESV3`): written with the document's own handler and
    fresh IVs; nothing to say.
  - *Legacy RC4* (`/V 1`, `/V 2`, or a `/V 4` crypt filter with `/CFM /V2`): **written, with a
    note** (`rc4Note`). An incremental update must use the document's own handler (the
    original revision is kept byte for byte and readers apply one `/Encrypt` to the whole
    file), so the alternatives are refusing or writing a decrypted copy — and a decrypted
    copy would silently drop the protection the author chose. Since only files that open
    with the empty user password are supported, RC4 here protects nothing against anyone
    holding the file; the note says so.
  - *Signed* (`/AcroForm /SigFlags` bit 1, or a signature field whose `/V` is a signature
    dictionary): **written, with a note** (`signedNote`): the signature still covers the
    original revision, which stays byte for byte at the start of the file; the annotations
    are a later revision outside it, which signature checkers list as changes after signing.
  - *Certified with no annotation changes permitted* (`/Perms /DocMDP` whose signature's
    `/Reference` has a `/DocMDP` transform with `/P` 1 or 2, default 2, ISO 32000-2
    §12.8.2.2): **refused** (`certifiedRefusal`): adding annotations would invalidate the
    certification; the marks can still be exported as XFDF. `/P 3` (annotations permitted)
    is written with the signed note.
* **Atomic write** (`writeAtomic`): the bytes go into a new temporary file in the target's
  directory (`.NAME.safepdf-N.tmp`, `tmpName`: `NAME` cut to 100 bytes, created
  exclusively), are read back and compared, get the
  caller's preparation (the viewer copies the replaced file's permissions onto it), and the
  temporary file is then renamed over the target; on any error the temporary file is removed
  and the target is untouched. A file is never truncated in place.
* **Save overwrites the opened file** (task 9.r2, Decision 2026-11-23, Plan.md S8 amended):
  the pure decisions of the viewer's Save and close paths are here — `route` (library,
  Save As…, or overwrite with or without the first-overwrite question), `diskState` (the file
  on disk still holds the bytes we opened, else Save refuses and offers Save As…; read through
  the shared capped read by `diskStateAt`, task 12.1),
  `writeProblem` (read-only file or folder: refused before anything is written), the dialog
  texts (`overwriteQuestion`, `changedQuestion`, `unsavedQuestion`), the button orders
  (`overwriteButtons`, `unsavedButtons`, `changedButtons`: on aqua the macOS order, the
  default button rightmost and Don't Save / Save As… leftmost) and what a close does with
  the answer (`onUnsavedAnswer`, `closeGoesOn`).
* **The file dialogs** (task 9.r6): `withExt` (a chosen name gets `.pdf`/`.xfdf` unless it
  already ends so — Tk on X11 adds `-defaultextension` only to names without any dot;
  `replaceQuestion` when that names an existing file), `targetProblem` (Save As… / Export
  refuse a folder, a read-only file, an unwritable folder and — Export — the opened
  document itself), `saveDialogOptions` (no `-filetypes` on aqua: Tk 9's "Format:" pop-up
  overflows the save panel), `dialogDir` (the opened file's folder, else home), `oneLine`.
* **Save As… proposal** (`defaultTarget`): `DIR/STEM-annotated.pdf` next to the opened file;
  for a file whose stem already ends in `-annotated` the file itself.
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
  | .freeText t p sz c =>
    some { page := m.page, kind := .freeText, quads := [], rect := ⟨p.x, p.y, p.x, p.y⟩,
           color := Marks.rgbUnit c, contents := t, fontSize := sz, id := m.id, date }
  | .ink ss w o c =>
    if ss.isEmpty || ss.any List.isEmpty then none
    else some { page := m.page, kind := .ink, quads := [], rect := ⟨0, 0, 0, 0⟩,
                color := Marks.rgbUnit c, opacity := (o : Rat) / 100,
                strokes := ss.map (·.map Marks.ptPair), lineWidth := w, id := m.id, date }

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

/-- A number rounded to the nearest natural number (negative: 0). -/
def roundNat (q : Rat) : Nat := (q + 1 / 2).floor.toNat

/-- Colour components in `[0, 1]` as bytes (black when not three numbers). -/
def rgbOf (cs : List Rat) : Marks.Rgb :=
  let b (q : Rat) : Nat := min 255 (roundNat (q * 255))
  match cs with
  | [r, g, bl] => (b r, b g, b bl)
  | _ => (0, 0, 0)

#guard rgbOf [1, 0, 5961 / 10000] == (255, 0, 152) && rgbOf [] == (0, 0, 0)
#guard (List.range 256).all fun n => rgbOf [Raster.Geom.decimalToRat (Core.Write.Annots.decRound 4 ((n : Rat) / 255)), 0, 0] == (n, 0, 0)

/-- The points of a flat number list `x1 y1 x2 y2 …` (a trailing odd number is ignored). -/
def pointsOf : List Rat → List Pt
  | x :: y :: rest => ⟨x, y⟩ :: pointsOf rest
  | _ => []

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
    else if n == Name.ofString "FreeText" then
      let r ← Doc.rectOf (get "Rect")
      let b := Box.ofRect r
      let da := match get "DA" with
        | .string bs => Annot.parseDA bs
        | _ => {}
      some ⟨id, page, .yellow, .freeText (textOf (get "Contents")) ⟨b.llx, b.ury⟩
        (max 1 (roundNat da.size)) (rgbOf da.color)⟩
    else if n == Name.ofString "Ink" then
      let strokes := match get "InkList" with
        | .array xs => xs.map fun x => pointsOf (nums (Doc.Nav.res doc limits x))
        | _ => []
      if strokes.isEmpty || strokes.any List.isEmpty then none
      let w := match get "BS" with
        | .dict bs => match (Doc.numOf (Doc.Nav.getL doc limits bs "W")) with
          | some d => roundNat (Raster.Geom.decimalToRat d)
          | none => 1
        | _ => 1
      let o := match Doc.numOf (get "CA") with
        | some d => min 100 (roundNat (Raster.Geom.decimalToRat d * 100))
        | none => 100
      some ⟨id, page, .yellow, .ink strokes w o (rgbOf (nums (get "C")))⟩
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
  if !m.isHighlight then return { mark := m, ref, created }
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

/-- The numbers of free text or ink that the writer rounds (position; stroke points), and
those it keeps exactly (size, thickness, opacity, colour bytes). -/
def editorNums (k : Marks.Kind) : List Rat × List Nat :=
  match k with
  | .freeText _ p z (r, g, b) => ([p.x, p.y], [0, z, r, g, b])
  | .ink ss w o (r, g, b) =>
    (ss.flatMap (·.flatMap fun p => [p.x, p.y]), [1, w, o, r, g, b] ++ ss.map List.length)
  | _ => ([], [])

/-- Whether `got` (read back) is the mark `m` (page box `pb`): id, page, colour, kind, text,
quads and note icon box; free text and ink: position and points within `tol`, the rest
exactly. -/
def sameMark (pb : Box) (m got : Mark) : Bool :=
  m.id == got.id && m.page == got.page && m.color == got.color && m.isNote == got.isNote &&
  m.isEditor == got.isEditor &&
  m.text == got.text && close m.quadPoints got.quadPoints &&
  close ((m.iconBox pb).map boxNums |>.getD []) ((got.iconBox pb).map boxNums |>.getD []) &&
  close (editorNums m.kind).1 (editorNums got.kind).1 &&
  (editorNums m.kind).2 == (editorNums got.kind).2

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

/-- The file Save As… proposes (see the module doc). -/
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

/-- The name of the temporary file of a save of `base` (task 9.r6): `.BASE.safepdf-STAMP.tmp`,
where `BASE` is cut to its first 100 UTF-8 bytes (whole characters) so that the temporary name
stays within the 255-byte file-name limit of common file systems even when the target's own
name nearly fills it (a 240-byte name used to fail with "name too long"). -/
def tmpName (base : String) (stamp : Nat) : String :=
  s!".{String.ofList (cutBytes 100 base.toList)}.safepdf-{stamp}.tmp"
where
  /-- The longest prefix of `cs` of at most `n` UTF-8 bytes. -/
  cutBytes (n : Nat) : List Char → List Char
    | [] => []
    | c :: cs => if c.utf8Size ≤ n then c :: cutBytes (n - c.utf8Size) cs else []

#guard tmpName "a.pdf" 7 == ".a.pdf.safepdf-7.tmp"
#guard (tmpName (String.ofList (List.replicate 250 'L') ++ ".pdf") 12345678901234).utf8ByteSize ≤ 255
#guard (tmpName (String.ofList (List.replicate 99 'x') ++ "üü") 1).startsWith
  (".".append (String.ofList (List.replicate 99 'x') ++ ".safepdf-"))

/-- Writes `bytes` to `path` through a new temporary file in the same directory and a rename
(never truncating the target in place): the temporary file is written, closed, read back and
compared with `bytes`, then `prepare` runs on it (the viewer copies the replaced file's
permissions), then it is renamed over `path`. The temporary file is removed on failure. -/
def writeAtomic (path : String) (bytes : ByteArray)
    (prepare : System.FilePath → IO Unit := fun _ => pure ()) : IO Unit := do
  let fp : System.FilePath := path
  let dir : System.FilePath := match fp.parent with
    | some d => if d.toString.isEmpty then "." else d
    | none => "."
  let base := fp.fileName.getD "document.pdf"
  let tmp := dir / tmpName base (← IO.monoNanosNow)
  try
    IO.FS.withFile tmp .writeNew fun h => do
      h.write bytes
      h.flush
    -- Capped read-back (task 12.1): more than `bytes.size` bytes is already a mismatch.
    let back ← match ← Shell.Read.readFile tmp bytes.size .inputBytes with
      | .ok b => pure b
      | .error _ => pure ByteArray.empty
    if back.size != bytes.size || back.data != bytes.data then
      throw (IO.userError s!"the temporary file {tmp} does not read back as written")
    prepare tmp
    IO.FS.rename tmp fp
  catch e =>
    try IO.FS.removeFile tmp catch _ => pure ()
    throw e

/-! ## Save overwrites the opened file (task 9.r2) -/

/-- What Save does (`route`). -/
inductive Route where
  /-- Nothing unsaved: nothing to do. -/
  | nothing
  /-- The document belongs to a library (bib-lean): Save to library (`PUT`). -/
  | library
  /-- Opened from memory without a library: no file to write into, Save As…. -/
  | saveAs
  /-- Write into the opened file; `ask`: first ask Overwrite / Save As… / Cancel. -/
  | overwrite (ask : Bool)
  deriving BEq, Repr

/-- **Save's route**: `dirty` (unsaved marks), `library`, `inMemory`, `confirmed` (this
session already wrote the opened file, or the user agreed to write into it in the
unsaved-changes prompt, whose text says so). -/
def route (dirty library inMemory confirmed : Bool) : Route :=
  if !dirty then .nothing
  else if library then .library
  else if inMemory then .saveAs
  else .overwrite (!confirmed)

#guard route false true true false == .nothing
#guard route true true false false == .library
#guard route true false true false == .saveAs
#guard route true false false false == .overwrite true
#guard route true false false true == .overwrite false

/-- The opened file on disk compared with the bytes the document was opened from. -/
inductive DiskState where
  /-- Still the same bytes. -/
  | same
  /-- Different bytes (another program wrote it). -/
  | changed
  /-- Gone, or unreadable. -/
  | missing
  deriving BEq, Repr

/-- **Whether the file on disk still holds the bytes we opened** (`onDisk`: its content, `none`
when it cannot be read): sizes first, then a full comparison. -/
def diskState (opened : ByteArray) (onDisk : Option ByteArray) : DiskState :=
  match onDisk with
  | none => .missing
  | some d => if d.size == opened.size && d.data == opened.data then .same else .changed

/-- **The overwrite comparison on disk** (task 12.1): `diskState` of the file `path` against
the `opened` bytes, read through the shared capped read (`Shell.Read.readFile`) with the cap
`opened.size`, so a file that grew on disk (even one that keeps growing) is read only up to
`opened.size + 1` bytes and reported `.changed`; `.missing` when it cannot be read. -/
def diskStateAt (opened : ByteArray) (path : System.FilePath) : IO DiskState := do
  try
    match ← Shell.Read.readFile path opened.size .inputBytes with
    | .ok b => return diskState opened (some b)
    | .error _ => return .changed
  catch _ => return .missing

#guard diskState "abc".toUTF8 (some "abc".toUTF8) == .same
#guard diskState "abc".toUTF8 (some "abd".toUTF8) == .changed
#guard diskState "abc".toUTF8 (some "abc\n".toUTF8) == .changed
#guard diskState "abc".toUTF8 none == .missing

/-- **Why the opened file `name` cannot be overwritten** (`fileWritable`: the file,
`dirWritable`: its folder, where the temporary file goes): `none` when it can. Checked before
anything is written (the rename would otherwise replace a read-only file). -/
def writeProblem (name : String) (fileWritable dirWritable : Bool) : Option String :=
  if !fileWritable then some s!"{name} is read-only; use Save As… to write a new file"
  else if !dirWritable then
    some s!"the folder of {name} is not writable (the new revision is written next to it \
      first); use Save As… to write elsewhere"
  else none

#guard writeProblem "a.pdf" true true == none
#guard (writeProblem "a.pdf" false true).isSome && (writeProblem "a.pdf" true false).isSome

/-- The first-overwrite question (Overwrite / Save As… / Cancel) for the opened file `name`
with `n` new or changed marks. -/
def overwriteQuestion (name : String) (n : Nat) : String :=
  s!"Save {n} new or changed mark(s) into {name}?\n\nThe marks are added to {name} itself. \
    Its present content is kept unchanged inside the file as its first revision (its bytes \
    stay at the start of the file). Save As… writes a new file instead and leaves {name} \
    as it is."

/-- The question when the opened file `name` changed on disk (`st`; Save As… / Cancel). -/
def changedQuestion (name : String) (st : DiskState) : String :=
  let what := if st == .missing then s!"{name} is no longer there (moved, deleted or unreadable)"
    else s!"{name} was changed on disk by another program since it was opened"
  s!"{what}. Saving into it would lose that change, so nothing was written.\n\nSave As… \
    writes the document as opened, with your marks, to a new file."

/-- The unsaved-changes question before `what` (closing, quitting, opening another file) with
`n` unsaved marks on `name`; `library`: Save goes to the library; `inMemory`: Save asks for a
file; `into`: Save writes into the opened file for the first time this session (the text says
so, and no second question follows). -/
def unsavedQuestion (name what : String) (n : Nat) (library inMemory into : Bool) : String :=
  let head := s!"{n} mark(s) on {name} are not saved. Save them before {what}?"
  let tail := if library then
      "Save sends the annotated file to the library (its annotation list has the marks \
      already); Don't Save leaves the library's file as it is."
    else if inMemory then "Save asks for a file; Don't Save discards them."
    else if into then
      s!"Save writes them into {name} (its present content is kept inside it as the first \
        revision); Don't Save discards them and leaves {name} untouched."
    else s!"Save writes them into {name}; Don't Save discards them and leaves {name} untouched."
  head ++ "\n\n" ++ tail

#guard (unsavedQuestion "t.pdf" "quitting" 2 false false true).startsWith
  "2 mark(s) on t.pdf are not saved. Save them before quitting?"

/-- Dialog buttons in display order, left to right (key, label): on aqua the macOS order (the
default action `dflt` rightmost, the alternative `alt` leftmost, Cancel next to the default),
elsewhere the default first and Cancel last. -/
def buttons (aqua : Bool) (dflt alt : String × String) : List (String × String) :=
  let cancel := ("cancel", "Cancel")
  if aqua then [alt, cancel, dflt] else [dflt, alt, cancel]

/-- The unsaved-changes buttons: Save / Don't Save / Cancel (aqua: Don't Save, Cancel, Save). -/
def unsavedButtons (aqua : Bool) : List (String × String) :=
  buttons aqua ("save", "Save") ("dontsave", "Don't Save")

/-- The first-overwrite buttons: Overwrite / Save As… / Cancel (aqua: Save As…, Cancel,
Overwrite). -/
def overwriteButtons (aqua : Bool) : List (String × String) :=
  buttons aqua ("overwrite", "Overwrite") ("saveas", "Save As…")

/-- The changed-on-disk buttons: Save As… / Cancel (aqua: Cancel, Save As…). -/
def changedButtons (aqua : Bool) : List (String × String) :=
  if aqua then [("cancel", "Cancel"), ("saveas", "Save As…")]
  else [("saveas", "Save As…"), ("cancel", "Cancel")]

#guard (unsavedButtons false).map (·.2) == ["Save", "Don't Save", "Cancel"]
#guard (unsavedButtons true).map (·.2) == ["Don't Save", "Cancel", "Save"]
#guard (overwriteButtons false).map (·.1) == ["overwrite", "saveas", "cancel"]
#guard (overwriteButtons true).map (·.1) == ["saveas", "cancel", "overwrite"]

/-- What closing does with the unsaved-changes answer (a key of `unsavedButtons`; anything
else, e.g. the dialog's own close button, counts as Cancel): `some true` save first,
`some false` go on without saving, `none` abort the close. -/
def onUnsavedAnswer (answer : String) : Option Bool :=
  if answer == "save" then some true
  else if answer == "dontsave" then some false
  else none

#guard onUnsavedAnswer "save" == some true && onUnsavedAnswer "dontsave" == some false &&
  onUnsavedAnswer "cancel" == none && onUnsavedAnswer "" == none

/-- Whether a close goes on: no unsaved marks (`dirty` false), Don't Save, or a Save that
succeeded (`saved`); Cancel and a failed Save abort it. -/
def closeGoesOn (dirty : Bool) (answer : Option Bool) (saved : Bool) : Bool :=
  !dirty || answer == some false || (answer == some true && saved)

#guard closeGoesOn false none false && closeGoesOn true (some false) false &&
  closeGoesOn true (some true) true && !closeGoesOn true (some true) false &&
  !closeGoesOn true none true

/-! ## The file dialogs (task 9.r6) -/

/-- **The chosen name with the file type's extension** `ext` (`pdf`, `xfdf`; task 9.r6): the
name itself when it already ends in `.ext` (any case), else `name.ext`. Tk's X11 dialog appends
`-defaultextension` only to a name without any extension, so a dotted name like
`3453483.3454032-final` (arXiv/ACM file names) came back without `.pdf`. -/
def withExt (name ext : String) : String :=
  if name.toLower.endsWith ("." ++ ext.toLower) then name else s!"{name}.{ext}"

#guard withExt "/d/3453483.3454032-final" "pdf" == "/d/3453483.3454032-final.pdf"
#guard withExt "/d/a.PDF" "pdf" == "/d/a.PDF" && withExt "a.pdf" "pdf" == "a.pdf"
#guard withExt "notes.XFDF" "xfdf" == "notes.XFDF" && withExt "notes" "xfdf" == "notes.xfdf"
#guard withExt "a.pdf" "xfdf" == "a.pdf.xfdf"

/-- **Why the chosen file `name` cannot be written** by Save As… or Export (task 9.r6;
`isDir`: it is a folder; `exists`/`fileWritable`: an existing file and whether it is
writable; `dirWritable`: its folder; `opened`: it is the opened document, which an export
must never replace): `none` when it can. A rename would replace a read-only file (9.r2
gotcha), so that is refused here as Save does for the opened file. -/
def targetProblem (name : String) (isDir «exists» fileWritable dirWritable opened : Bool) :
    Option String :=
  if isDir then some s!"{name} is a folder; choose a file name"
  else if opened then
    some s!"{name} is the opened document; annotations are exported to a separate .xfdf file"
  else if «exists» && !fileWritable then some s!"{name} is read-only; choose another name"
  else if !dirWritable then some s!"the folder of {name} is not writable; choose another folder"
  else none

#guard targetProblem "a.pdf" false true true true false == none
#guard targetProblem "a.pdf" false false false true false == none
#guard (targetProblem "a" true false false true false).isSome &&
  (targetProblem "a.pdf" false true false true false).isSome &&
  (targetProblem "a.pdf" false false false false false).isSome &&
  (targetProblem "a.pdf" false true true true true).isSome

/-- The question when adding the extension (`withExt`) named an existing file `name` that the
file dialog did not confirm. -/
def replaceQuestion (name : String) : String :=
  s!"{name} already exists. Replace it?"

/-- **The options of a save dialog** (task 9.r6) for files of type `label` with extension
`ext`, besides `-parent`/`-title`/`-initialdir`/`-initialfile`: `-defaultextension .ext`,
`-confirmoverwrite 1`, and on X11/Windows `-filetypes` (the type, then all files). **Not on
aqua**: Tk 9's `tk_getSaveFile` builds its "Format:" accessory view from `-filetypes` with a
pop-up button 340 pt wide placed at x = 50 inside a 300 pt view (`macosx/tkMacOSXDialog.c`,
`Tk_GetSaveFileObjCmd`, unchanged up to Tk 9.1), so the pop-up always runs past the panel's
right edge whatever the labels. Without `-filetypes` Tk shows no accessory view and still
restricts the panel to `ext` from `-defaultextension` (allowing other types on request). -/
def saveDialogOptions (aqua : Bool) (label ext : String) : List String :=
  let base := ["-defaultextension", s!".{ext}", "-confirmoverwrite", "1"]
  if aqua then base
  else base ++ ["-filetypes", s!"\{\{{label}} \{.{ext} .{ext.toUpper}}} \{\{All files} *}"]

#guard saveDialogOptions true "PDF files" "pdf" ==
  ["-defaultextension", ".pdf", "-confirmoverwrite", "1"]
#guard saveDialogOptions false "PDF files" "pdf" == ["-defaultextension", ".pdf",
  "-confirmoverwrite", "1", "-filetypes", "{{PDF files} {.pdf .PDF}} {{All files} *}"]
#guard !(saveDialogOptions true "XFDF" "xfdf").contains "-filetypes"

/-- **The folder a file dialog starts in** (task 9.r6): `dir` (the opened file's folder) when
`usable` (an existing, writable folder of a file on disk), else the home folder, else `.`. A
document from memory (bib-lean) has no folder of its own: its "path" is the library's name,
which said `.` — the viewer process's working directory. -/
def dialogDir (dir : String) (usable : Bool) (home : Option String) : String :=
  if usable then dir else (home.filter (!·.isEmpty)).getD "."

#guard dialogDir "/d" true (some "/h") == "/d" && dialogDir "/d" false (some "/h") == "/h"
#guard dialogDir "." false none == "." && dialogDir "." false (some "") == "."

/-- A message on one line (task 9.r6): an `IO` error's text (`…\n  file: …`) would make the
one-line status bar two lines tall and shift the page. -/
def oneLine (s : String) : String :=
  " ".intercalate ((s.splitOn "\n").map (·.trimAscii.toString) |>.filter (!·.isEmpty))

#guard oneLine "cannot write x: name too long\n  file: /a/b" ==
  "cannot write x: name too long file: /a/b"

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
  /-- What the user should know about the written file's protection (task 12.4, `notes`). -/
  notes : List String := []

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
      let same := if m.isEditor then e.mark.kind.same m.kind
        else e.mark.color == m.color && e.mark.text == m.text &&
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

/-! ## Protection policy (task 12.4) -/

/-- The signature state of a document (ISO 32000-2 §12.8). -/
inductive SigState where
  /-- No signature found. -/
  | unsigned
  /-- Signed (approval signatures), not certified. -/
  | signed
  /-- Certified with `/DocMDP` permission level `p` (1: no changes, 2: form filling and
  signing, 3: also annotations; §12.8.2.2). -/
  | certified (p : Nat)
  deriving DecidableEq, Repr

/-- What Save knows about the document's protection. -/
structure Protection where
  /-- The string and stream methods (`/StrF`, `/StmF`), when encrypted. -/
  methods : Option (Crypt.Method × Crypt.Method) := none
  /-- The signature state. -/
  sig : SigState := .unsigned
  deriving Repr

/-- A value of `d` resolved one level; `null` on an error or when absent. -/
def keyOr (doc : Doc.Doc) (limits : Limits) (d : Dict) (k : String) : PdfObject :=
  match Doc.key doc.file limits d k with
  | .ok o => o
  | .error _ => .null

/-- At most this many `/AcroForm /Fields` entries are inspected for a signature value. -/
def maxSigFields : Nat := 1000

/-- Whether the document carries a signature: `/AcroForm /SigFlags` bit 1
(`SignaturesExist`), or a top-level field with `/FT /Sig` whose `/V` is a signature
dictionary (the first `maxSigFields` fields; kids are not walked). -/
def isSigned (doc : Doc.Doc) (limits : Limits) : Bool :=
  match keyOr doc limits doc.catalog "AcroForm" with
  | .dict af =>
    let flags := match keyOr doc limits af "SigFlags" with
      | .int i => i.toNat % 2 == 1
      | _ => false
    let fields := match keyOr doc limits af "Fields" with
      | .array xs => xs.take maxSigFields
      | _ => []
    flags || fields.any fun f =>
      match Doc.resolve doc.file limits f with
      | .ok (.dict fd) =>
        Dict.get? fd (Name.ofString "FT") == some (.name (Name.ofString "Sig")) &&
        (match keyOr doc limits fd "V" with
          | .dict v => Crypt.isSigDict v
          | _ => false)
      | _ => false
  | _ => false

/-- The `/DocMDP` permission level of the certification signature, if any: catalog
`/Perms /DocMDP` → signature dictionary → the first of its (at most 16) `/Reference` entries
with `/TransformMethod /DocMDP` → `/TransformParams /P` (1 or 3; 2 when absent or other,
the ISO default). A `/DocMDP` signature without such an entry counts as level 2. -/
def docMdp (doc : Doc.Doc) (limits : Limits) : Option Nat :=
  match keyOr doc limits doc.catalog "Perms" with
  | .dict perms =>
    match keyOr doc limits perms "DocMDP" with
    | .dict sig =>
      let refs := match keyOr doc limits sig "Reference" with
        | .array xs => xs.take 16
        | _ => []
      let level (r : PdfObject) : Option Nat :=
        match Doc.resolve doc.file limits r with
        | .ok (.dict rd) =>
          if Dict.get? rd (Name.ofString "TransformMethod") ==
              some (.name (Name.ofString "DocMDP")) then
            match keyOr doc limits rd "TransformParams" with
            | .dict tp =>
              match keyOr doc limits tp "P" with
              | .int 1 => some 1
              | .int 3 => some 3
              | _ => some 2
            | _ => some 2
          else none
        | _ => none
      some ((refs.findSome? level).getD 2)
    | _ => none
  | _ => none

/-- **The document's protection** (task 12.4). -/
def protection (doc : Doc.Doc) (limits : Limits) : Protection :=
  { methods := doc.file.crypt.map fun st => (st.handler.strF, st.handler.stmF)
    sig := match docMdp doc limits with
      | some p => .certified p
      | none => if isSigned doc limits then .signed else .unsigned }

/-- The note for a document encrypted with RC4 (task 12.4). -/
def rc4Note : String :=
  "this file uses the legacy RC4 encryption: the new annotations are encrypted with it, as \
  the file requires (it opens without a password, so its encryption keeps nothing \
  confidential)"

/-- The note for a signed document (task 12.4). -/
def signedNote : String :=
  "this file is digitally signed: the signature still covers the original revision, which \
  is kept byte for byte; the annotations are a later revision outside it, which signature \
  checkers list as changes made after signing"

/-- The refusal for a certified document that permits no annotation changes (task 12.4). -/
def certifiedRefusal (p : Nat) : String :=
  s!"this document is certified and its certification (/DocMDP /P {p}) permits no \
  annotation changes: saving would invalidate it. Export the marks as XFDF instead"

/-- **The refusal**, if Save must not write into a document with protection `pr`. -/
def refusal (pr : Protection) : Option String :=
  match pr.sig with
  | .certified p => if p ≤ 2 then some (certifiedRefusal p) else none
  | _ => none

/-- **The notes** Save shows after writing into a document with protection `pr`. -/
def notes (pr : Protection) : List String :=
  let isRc4 : Bool := match pr.methods with
    | some (a, b) => a == .rc4 || b == .rc4
    | none => false
  let signed := match pr.sig with
    | .unsigned => false
    | _ => true
  (if isRc4 then [rc4Note] else []) ++ (if signed then [signedNote] else [])

/-- The notes after a save into `doc` that wrote or deleted `n` marks (none when `n = 0`:
nothing was written into the file's protection). -/
def notesFor (limits : Limits) (doc : Doc.Doc) (n : Nat) : List String :=
  if n == 0 then [] else notes (protection doc limits)

/-- The notes as one status-line suffix (`""` when there are none). -/
def notesText (ns : List String) : String :=
  String.join (ns.map fun n => s!"; {n}")

#guard notes {} == []
#guard refusal {} == none
#guard notes { methods := some (.rc4, .rc4) } == [rc4Note]
#guard notes { methods := some (.aesv2, .rc4) } == [rc4Note]
#guard notes { methods := some (.aesv2, .aesv2) } == []
#guard notes { methods := some (.aesv3, .aesv3), sig := .signed } == [signedNote]
#guard refusal { sig := .signed } == none
#guard refusal { sig := .certified 1 } == some (certifiedRefusal 1)
#guard refusal { sig := .certified 2 } == some (certifiedRefusal 2)
#guard refusal { sig := .certified 3 } == none
#guard notes { sig := .certified 3 } == [signedNote]
#guard notesText [] == ""

/-! ## Fresh IV seeds (task 12.4) -/

/-- The size of one randomness source's contribution to an IV seed, in bytes. -/
def seedSize : Nat := 32

/-- **Fresh randomness from the operating system** for the writer's AES IVs (task 12.4):
`seedSize` bytes of `/dev/urandom` followed by `seedSize` bytes of `IO.getRandomBytes`
(libuv `uv_random`: `getentropy` on macOS, `getrandom` on Linux); a source that fails or
delivers fewer bytes is left out, and an error is raised when both are. -/
def freshSeed : IO ByteArray := do
  let dev ← try
      some <$> IO.FS.withFile "/dev/urandom" .read fun h => h.read seedSize.toUSize
    catch _ => pure none
  let rt ← try some <$> IO.getRandomBytes seedSize.toUSize catch _ => pure none
  let parts := [dev, rt].filterMap fun o => o.filter (·.size == seedSize)
  if parts.isEmpty then
    throw (IO.userError "no randomness from the operating system")
  return parts.foldl (· ++ ·) ByteArray.empty

/-- The IV seed for saving `doc`: fresh randomness (`freshSeed`) when it is encrypted, empty
otherwise (nothing uses it); an error when an encrypted document gets no randomness. -/
def seedFor (doc : Doc.Doc) : IO (Except String ByteArray) := do
  if doc.file.crypt.isNone then return .ok ByteArray.empty
  try return .ok (← freshSeed)
  catch e => return .error s!"cannot save an encrypted document: {oneLine (toString e)}"

/-- The bytes Save would write for the store's changes (`bytes` unchanged when there are
none), checked as described in the module doc; an error message otherwise (also the
protection policy's refusal, task 12.4). `ivSeed` feeds the AES IVs (`seedFor`). Also returns
the marks read back and the number of marks written or deleted. -/
def build (limits : Limits) (doc : Doc.Doc) (store : Store) (date : String)
    (ivSeed : ByteArray) : Except String (ByteArray × List Mark × Nat) := do
  let plan ← edits doc (scan doc limits) store date
  let orig := doc.file.bytes
  if !plan.isEmpty then
    if let some why := refusal (protection doc limits) then throw why
  let out ← if plan.isEmpty then pure orig
    else match Write.Annots.writeEdits limits doc plan.edits ivSeed with
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

/-- **`build` now**: with the current date (`nowDate`) and a fresh IV seed (`seedFor`). -/
def buildNow (limits : Limits) (doc : Doc.Doc) (store : Store) :
    IO (Except String (ByteArray × List Mark × Nat)) := do
  let date ← nowDate
  match ← seedFor doc with
  | .error e => return .error e
  | .ok seed => return build limits doc store date seed

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

/-- **Save**: builds and checks the bytes for the store's changes (`buildNow`: fresh IV
seed, protection policy), then writes them to `target` atomically; the outcome carries the
policy's notes. -/
def write (limits : Limits) (doc : Doc.Doc) (store : Store) (target : String)
    (prepare : System.FilePath → IO Unit := fun _ => pure ()) :
    IO (Except String Outcome) := do
  match ← buildNow limits doc store with
  | .error e => return .error e
  | .ok (bytes, got, n) =>
    try
      writeAtomic target bytes prepare
      return .ok { path := target, marks := n,
                   appended := bytes.size - doc.file.bytes.size, size := bytes.size,
                   total := got.length,
                   notes := notesFor limits doc n }
    catch e => return .error s!"cannot write {target}: {oneLine (toString e)}"

end SafePdf.Shell.App.Save
