import SafePdf.Api
import SafePdf.Shell.App.Marks
import SafePdf.Shell.App.Save
import SafePdf.Shell.App.Xfdf
import SafePdf.Shell.App.Toolbar

/-!
# C API v2: marks, save and XFDF (task 11.3a3; Plan.md §6 Phases 9–11, §4 C7, §8)

The marks model of the Tk viewer exported to C for the native macOS shell
(`docs/macos-design.md` §3, decision 1: everything with a theorem or `#guard` stays in Lean;
decision 2: flat C structs). This Shell module (unverified; no `IO` except the clock) exports
`@[export safepdf_marks_lean_…]` functions; `macos/safepdf_marks.c` wraps them into the plain C
API of `macos/safepdf_marks.h` and hides every `lean_object`. Nothing here reimplements a rule:
each export calls the function the Tk viewer (`Shell.App.Viewer`) calls on the same user
action, in the same order.

* **The store handle** (`Handle`): the document opened from the bytes the GUI read
  (`Api.openBytes` under `Limits.default`, as the viewer), its marks (`Marks.Store.load` of
  `Save.readMarks`: the marks already saved in the file are listed as saved) and the undo
  history (`Marks.History.start`). Handles are immutable Lean values: every edit returns a new
  handle, which the C side swaps in.
* **Edits** (`edit`): every change of the store is recorded in the history
  (`Marks.History.record`, `merge` for the steps of one slider drag, `seal` to close it) —
  `Viewer.marksChanged`. Adding: `Store.addHighlight`, `addNote` (anchor from
  `Marks.noteAnchor`), the comment of a highlight (`Store.noteOn`, else a note on its exact
  quads in its colour — `Viewer.addNote`), free text and ink (`Store.add`, `addStroke`).
  Changing: `setText`, `recolor`, `setRgb`, `setSize`, `setOpacity`, `translate`. Deleting:
  `removeWithComment` (a highlight's comment goes with it). Undo/redo: `History.undo`/`redo`.
* **Listing** (`list`): the marks of a page (or all) as numbers and texts, decoded by the C
  side into `safepdf_mark` structs — kind, page, colour, display RGB (`Mark.hex`'s colour),
  new / saved / saved-and-changed (`Store.isSaved`, `Store.changedSaved`), whether a note is a
  highlight's comment (`Store.isComment`), the `/Rect` (`Mark.rect` in the page's CropBox),
  quads, point, strokes.
* **Save** (`saveBuild`): `Save.build` (C7: the original bytes a prefix of the result, strict
  reopen, read-back of every mark) with the caller's date (empty: now, `Save.nowDate`) and the
  caller's IV seed. As `Save.seedFor` in the viewer, an **encrypted** document is not saved
  without fresh randomness: the GUI passes `2 * Save.seedSize` = 64 random bytes, fewer is
  refused. The protection notes (`Save.notesFor`: RC4, signed) and the revision-retention
  text (`Save.retentionText`, task 12.5) come back as notes with flags; the `/DocMDP`
  refusal (`Save.refusal`) as its own error code. **The output budget belongs to the GUI**
  (the Tk viewer reserves `Save.outputEstimate` in its pool, `Viewer.withOutput`): the
  caller passes a ceiling, and an estimate above it is refused before anything is built.
  The bytes are written by the GUI (atomic write, panels); afterwards it creates a new store
  from them, as the viewer reopens the written file.
* **Save decisions** (pure, task 9.r2): `Save.route`, `Save.diskState` of the bytes the GUI
  read back from disk, the dialog texts and `Save.writeProblem` / `Save.targetProblem`.
* **XFDF**: `Xfdf.toXfdf` (export; `Xfdf.exportEstimate` against the caller's ceiling) and
  `Xfdf.readXfdf` + `Xfdf.importItems` (import, pages checked against the document, under
  `Xfdf.Limits` defaults — the same validation and limits as `Xfdf.readFile`).

Calling convention as in `Shell.Ffi`: every object argument is owned (Lean v4.36 rejects
`@&` on exports), every result is owned by the caller. Coordinates cross as `Float`s
(`ratOfFloat`: exact for finite values of magnitude at most 2³²; values below 2⁻³⁰ count
as 0; anything else is refused) and come back as `Float`s (`toF`). Mark ids cross as `USize`
(saturating; an id beyond it cannot be named and is never matched).
-/

namespace SafePdf.Shell.FfiMarks

open SafePdf SafePdf.Core
open SafePdf.Core.Raster.Geom (Pt Box)
open SafePdf.Shell.App
open SafePdf.Shell.App.Marks (Mark Color Store History Kind Anchor)

/-- The limits of the store's document (the viewer's, `Viewer.limits`). -/
def limits : Limits := Limits.default

/-- The marks store of one document, as the C side sees it: an opaque `lean_object *`. -/
structure Handle where
  /-- The opened document (`Api.openBytes`). -/
  doc : Api.Document
  /-- The marks (saved and new). -/
  store : Store
  /-- The undo/redo history of `store.marks`. -/
  hist : History

/-! ## Numbers across the boundary -/

/-- A rational as a `Float` (display data only). -/
def toF (q : Rat) : Float := Float.ofInt q.num / Float.ofNat q.den

/-- A natural number as a `Float` (exact below 2⁵³). -/
def natF (n : Nat) : Float := Float.ofNat n

/-- A natural number as a `USize`, saturating at the largest one. -/
def satU (n : Nat) : USize := if n < USize.size then n.toUSize else (USize.size - 1).toUSize

/-- **A `Float` from C as an exact rational**: `none` for NaN, infinities and magnitudes above
2³²; magnitudes below 2⁻³⁰ give 0; otherwise the exact value of the binary64 number
(`Float.frExp`: `f = m · 2^e` with `1/2 ≤ |m| < 1`, so `|m| · 2⁵³` is an integer). -/
def ratOfFloat (f : Float) : Option Rat :=
  if f.isNaN || f.isInf then none
  else if f.abs > 4294967296.0 then none
  else if f.abs < 9.313225746154785e-10 then some 0
  else
    let (m, e) := f.frExp
    let mi : Nat := (m.abs * 9007199254740992.0).toUInt64.toNat
    let q : Rat := if e ≥ 53 then ((mi * 2 ^ (e - 53).toNat : Nat) : Rat)
      else (mi : Rat) / ((2 ^ (53 - e).toNat : Nat) : Rat)
    some (if f < 0 then -q else q)

#guard ratOfFloat 0.5 == some (1 / 2)
#guard ratOfFloat (-698.25) == some (-2793 / 4)
#guard ratOfFloat 612.0 == some 612
#guard ratOfFloat 0.0 == some 0
#guard ratOfFloat (1.0 / 0.0) == none
#guard ratOfFloat 1e10 == none
#guard (ratOfFloat 0.1).map toF == some 0.1

/-- The numbers of a `FloatArray` as rationals; `none` when one is refused (`ratOfFloat`). -/
def ratsOf (a : FloatArray) : Option (List Rat) :=
  a.toList.mapM ratOfFloat

/-- Boxes from `llx lly urx ury` groups (the length must be a multiple of 4). -/
def boxesOf (a : FloatArray) : Option (List Box) := do
  let xs ← ratsOf a
  if xs.length % 4 != 0 then none
  let rec go : List Rat → List Box
    | a :: b :: c :: d :: rest => ⟨a, b, c, d⟩ :: go rest
    | _ => []
  some (go xs)

/-- Points from `x y` pairs (the length must be even). -/
def ptsOf (a : FloatArray) : Option (List Pt) := do
  let xs ← ratsOf a
  if xs.length % 2 != 0 then none
  some (Save.pointsOf xs)

/-- The palette colour with index `i` (`Color.all`: yellow, green, blue, pink, red). -/
def colorOf (i : UInt8) : Option Color := Color.all[i.toNat]?

/-- The index of a palette colour in `Color.all`. -/
def colorIdx (c : Color) : Nat := (Color.all.findIdx? (· == c)).getD 0

/-- `0xRRGGBB` as an RGB triple. -/
def rgbOf (v : UInt32) : Marks.Rgb :=
  let n := v.toNat
  (n / 65536 % 256, n / 256 % 256, n % 256)

#guard rgbOf 0xFF8000 == (255, 128, 0)
#guard Color.all.all fun c => colorOf (colorIdx c).toUInt8 == some c

/-! ## The store -/

/-- **Create** the store of the document `bytes` (the bytes the GUI read through the capped
read): opened as the viewer opens a file, its saved marks restored (`Save.readMarks`), an empty
history. An error message when the bytes do not open. -/
@[export safepdf_marks_lean_create]
def create (bytes : ByteArray) : Except String Handle :=
  match Api.openBytes bytes { limits } with
  | .error e => .error e.message
  | .ok d =>
    let store := Store.load (Save.readMarks d.doc limits)
    .ok ⟨d, store, History.start store.marks⟩

/-- Number of pages of the store's document. -/
@[export safepdf_marks_lean_page_count]
def pageCount (h : Handle) : USize := satU h.doc.doc.pages.size

/-- The page box note icons are placed in (the CropBox, `Save.pageBox`; US Letter when the page
is missing, as `Save.verify`). -/
def boxOf (h : Handle) (page : Nat) : Box :=
  (Save.pageBox h.doc.doc page).getD ⟨0, 0, 612, 792⟩

/-- The result of an edit: the new handle and an id (0 when none). -/
abbrev EditResult := Except String (Handle × USize)

/-- **An edit** of the store (`Viewer.marksChanged`): the new store, recorded in the history
(`merge`: a further step of the current slider drag). -/
def edit (h : Handle) (s : Store) (merge : Bool := false) (id : Nat := 0) : EditResult :=
  .ok ({ h with store := s, hist := h.hist.record s.marks merge }, satU id)

/-- The mark `id`, or an error. -/
def markOr (h : Handle) (id : USize) : Except String Mark :=
  match h.store.find? id.toNat with
  | some m => .ok m
  | none => .error s!"no mark {id.toNat}"

/-- A page index checked against the document. -/
def pageOr (h : Handle) (page : USize) : Except String Nat :=
  if page.toNat < h.doc.doc.pages.size then .ok page.toNat
  else .error s!"page {page.toNat + 1} is not in the document"

/-- A palette colour index, or an error. -/
def colorOr (c : UInt8) : Except String Color :=
  match colorOf c with
  | some c => .ok c
  | none => .error s!"colour index {c.toNat} is not in the palette (0–4)"

/-- **Add a highlight** over `quads` (`llx lly urx ury` per quad, page space) in palette colour
`color` (`Store.addHighlight`; refused without quads). -/
@[export safepdf_marks_lean_add_highlight]
def addHighlight (h : Handle) (page : USize) (color : UInt8) (quads : FloatArray) : EditResult := do
  let p ← pageOr h page
  let c ← colorOr color
  let some qs := boxesOf quads | throw "bad quad coordinates"
  match h.store.addHighlight p c qs with
  | some (s, id) => edit h s (id := id)
  | none => throw "nothing to highlight (no quads)"

/-- **Add a note** with `text` in palette colour `color`: `anchor` 0 at the point `nums = x y`,
1 on the quads `nums` (`Store.addNote`; the anchor comes from `Marks.noteAnchor`, exported as
`noteAnchor`). -/
@[export safepdf_marks_lean_add_note]
def addNote (h : Handle) (page : USize) (color : UInt8) (text : String) (anchor : UInt8)
    (nums : FloatArray) : EditResult := do
  let p ← pageOr h page
  let c ← colorOr color
  let anc ← match anchor.toNat with
    | 0 => match ptsOf nums with
      | some [pt] => pure (Anchor.point pt)
      | _ => throw "a point anchor needs exactly two coordinates"
    | 1 => match boxesOf nums with
      | some (q :: qs) => pure (Anchor.quads (q :: qs))
      | _ => throw "a quad anchor needs at least one quad"
    | _ => throw "unknown anchor kind"
  let (s, id) := h.store.addNote p c text anc
  edit h s (id := id)

/-- **The comment of highlight `id`** (`Viewer.addNote` with a highlight selected, task 9.8):
its existing comment note (`Store.noteOn`, returned unchanged, the store as it is), else a new
note with `text` anchored to exactly its quads, in its colour. -/
@[export safepdf_marks_lean_add_comment]
def addComment (h : Handle) (id : USize) (text : String) : EditResult := do
  let m ← markOr h id
  if m.isNote || m.quads.isEmpty then throw s!"mark {id.toNat} is not a highlight"
  match h.store.noteOn m.page m.quads with
  | some nid => return (h, satU nid)
  | none =>
    let (s, nid) := h.store.addNote m.page m.color text (.quads m.quads)
    edit h s (id := nid)

/-- Font size bounds of free text (task 9.9, PDF.js's 5–100). -/
def sizeOk (n : Nat) : Bool := 5 ≤ n && n ≤ 100

/-- Thickness bounds of ink (task 9.9, 1–20). -/
def widthOk (n : Nat) : Bool := 1 ≤ n && n ≤ 20

/-- **Add free text** `text` with its box's upper-left corner at `(x, y)`, font size `size`
(5–100) and colour `rgb` (`0xRRGGBB`). -/
@[export safepdf_marks_lean_add_free_text]
def addFreeText (h : Handle) (page : USize) (text : String) (x y : Float) (size : UInt32)
    (rgb : UInt32) : EditResult := do
  let p ← pageOr h page
  let (some x, some y) := (ratOfFloat x, ratOfFloat y) | throw "bad coordinates"
  if !sizeOk size.toNat then throw "font size must be 5 to 100"
  let (s, id) := h.store.add p .yellow (.freeText text ⟨x, y⟩ size.toNat (rgbOf rgb))
  edit h s (id := id)

/-- **Add ink**: one stroke `pts` (`x y` pairs, at least one point), thickness `width` (1–20),
`opacity` percent (0–100), colour `rgb`. Further strokes of the same drawing session:
`addStroke`. -/
@[export safepdf_marks_lean_add_ink]
def addInk (h : Handle) (page : USize) (pts : FloatArray) (width opacity rgb : UInt32) :
    EditResult := do
  let p ← pageOr h page
  let some st := ptsOf pts | throw "bad stroke coordinates"
  if st.isEmpty then throw "a stroke needs at least one point"
  if !widthOk width.toNat then throw "thickness must be 1 to 20"
  if opacity.toNat > 100 then throw "opacity must be 0 to 100"
  let (s, id) := h.store.add p .yellow (.ink [st] width.toNat opacity.toNat (rgbOf rgb))
  edit h s (id := id)

/-- **Append a stroke** to ink `id` (`Store.addStroke`). -/
@[export safepdf_marks_lean_add_stroke]
def addStroke (h : Handle) (id : USize) (pts : FloatArray) : EditResult := do
  let m ← markOr h id
  let .ink .. := m.kind | throw s!"mark {id.toNat} is not ink"
  let some st := ptsOf pts | throw "bad stroke coordinates"
  if st.isEmpty then throw "a stroke needs at least one point"
  edit h (h.store.addStroke m.id st) (id := m.id)

/-- **Edit the text** of note or free text `id` (`Store.setText`; unchanged text: no step, as
`Viewer.noteSave`). -/
@[export safepdf_marks_lean_set_text]
def setText (h : Handle) (id : USize) (text : String) : EditResult := do
  let m ← markOr h id
  if !(m.isNote || m.isFreeText) then throw s!"mark {id.toNat} has no text"
  if m.text == text then return (h, satU m.id)
  edit h (h.store.setText m.id text) (id := m.id)

/-- **Recolour** highlight or note `id` with palette colour `color` (`Store.recolor`; free text
and ink take an RGB colour, `setRgb`). -/
@[export safepdf_marks_lean_recolor]
def recolor (h : Handle) (id : USize) (color : UInt8) : EditResult := do
  let m ← markOr h id
  let c ← colorOr color
  if m.isEditor then throw s!"mark {id.toNat} takes an RGB colour"
  edit h (h.store.recolor m.id c) (id := m.id)

/-- **Set the RGB colour** of free text or ink `id` (`Store.setRgb`). -/
@[export safepdf_marks_lean_set_rgb]
def setRgb (h : Handle) (id : USize) (rgb : UInt32) (merge : UInt8) : EditResult := do
  let m ← markOr h id
  if !m.isEditor then throw s!"mark {id.toNat} takes a palette colour"
  edit h (h.store.setRgb m.id (rgbOf rgb)) (merge != 0) (id := m.id)

/-- **Set the font size** (5–100) of free text `id` or the thickness (1–20) of ink `id`
(`Store.setSize`). -/
@[export safepdf_marks_lean_set_size]
def setSize (h : Handle) (id : USize) (n : UInt32) (merge : UInt8) : EditResult := do
  let m ← markOr h id
  match m.kind with
  | .freeText .. => if !sizeOk n.toNat then throw "font size must be 5 to 100"
  | .ink .. => if !widthOk n.toNat then throw "thickness must be 1 to 20"
  | _ => throw s!"mark {id.toNat} has no size"
  edit h (h.store.setSize m.id n.toNat) (merge != 0) (id := m.id)

/-- **Set the opacity** (percent, 0–100) of ink `id` (`Store.setOpacity`). -/
@[export safepdf_marks_lean_set_opacity]
def setOpacity (h : Handle) (id : USize) (o : UInt32) (merge : UInt8) : EditResult := do
  let m ← markOr h id
  let .ink .. := m.kind | throw s!"mark {id.toNat} is not ink"
  if o.toNat > 100 then throw "opacity must be 0 to 100"
  edit h (h.store.setOpacity m.id o.toNat) (merge != 0) (id := m.id)

/-- **Move** free text or ink `id` by `(dx, dy)` page units (`Store.translate`). -/
@[export safepdf_marks_lean_translate]
def translate (h : Handle) (id : USize) (dx dy : Float) (merge : UInt8) : EditResult := do
  let m ← markOr h id
  if !m.isEditor then throw s!"mark {id.toNat} cannot be moved"
  let (some dx, some dy) := (ratOfFloat dx, ratOfFloat dy) | throw "bad offset"
  edit h (h.store.translate m.id dx dy) (merge != 0) (id := m.id)

/-- **Close the open merge step** (a slider released, `History.seal`). -/
@[export safepdf_marks_lean_seal]
def sealStep (h : Handle) : Handle := { h with hist := h.hist.seal }

/-- **Delete** mark `id` (`Store.removeWithComment`: a highlight's comment goes with it). -/
@[export safepdf_marks_lean_delete]
def delete (h : Handle) (id : USize) : EditResult := do
  let m ← markOr h id
  edit h (h.store.removeWithComment m.id) (id := m.id)

/-- **Undo** (`undo` ≠ 0) or **redo** the last edit (`Viewer.undoRedo`: the history is first
brought in step with the store); an error when there is nothing to undo / redo. -/
@[export safepdf_marks_lean_undo_redo]
def undoRedo (h : Handle) (undo : UInt8) : EditResult :=
  let hist := h.hist.record h.store.marks
  let r := if undo != 0 then hist.undo h.store else hist.redo h.store
  match r with
  | some (hist, store) => .ok ({ h with store, hist := hist.record store.marks }, 0)
  | none => .error (if undo != 0 then "nothing to undo" else "nothing to redo")

/-- **The store's state** as numbers: can undo, can redo, dirty (`Store.dirty`), pending
(`Store.pending`), new marks, changed saved marks, deleted saved marks, undo depth, redo depth,
encrypted, page count, number of marks. -/
@[export safepdf_marks_lean_state]
def state (h : Handle) : FloatArray :=
  let s := h.store
  let b (x : Bool) : Float := if x then 1 else 0
  ⟨#[b h.hist.canUndo, b h.hist.canRedo, b s.dirty, natF s.pending, natF s.unsaved.length,
     natF s.changedSaved.length, natF s.deletedSaved.length, natF h.hist.past.length,
     natF h.hist.future.length, b h.doc.doc.file.crypt.isSome, natF h.doc.doc.pages.size,
     natF s.marks.size]⟩

/-- **Hit test**: the topmost mark of `page` under the page point `(x, y)` (`Store.hitAt`, note
icons in the page's CropBox); 0 when none. -/
@[export safepdf_marks_lean_hit_at]
def hitAt (h : Handle) (page : USize) (x y : Float) : USize :=
  match ratOfFloat x, ratOfFloat y with
  | some x, some y => satU ((h.store.hitAt (boxOf h page.toNat) page.toNat ⟨x, y⟩).getD 0)
  | _, _ => 0

/-- **Closing a note's popup without Save** showing `shown` (`Store.onUnsavedClose`, task
9.r12): 0 keep, 1 save `shown` into it (`setText`), 2 delete it (`delete`). -/
@[export safepdf_marks_lean_note_close]
def noteClose (h : Handle) (id : USize) (shown : String) : UInt8 :=
  match h.store.onUnsavedClose id.toNat shown with
  | .keep => 0
  | .save _ => 1
  | .delete => 2

/-- **Where a new note anchors** (`Marks.noteAnchor`, task 10.17): `sel` the boxes of the
current selection on the clicked page (`llx lly urx ury` each), `click` ≠ 0 with the page point
`(x, y)`. 0: no anchor (the caller picks the window centre), 1: the selection's quads, 2: the
point; 255: bad numbers. -/
@[export safepdf_marks_lean_note_anchor]
def noteAnchor (sel : FloatArray) (click : UInt8) (x y : Float) : UInt8 :=
  match boxesOf sel with
  | none => 255
  | some qs =>
    let pt : Option (Option Pt) :=
      if click == 0 then some none
      else match ratOfFloat x, ratOfFloat y with
        | some x, some y => some (some ⟨x, y⟩)
        | _, _ => none
    match pt with
    | none => 255
    | some pt =>
      match Marks.noteAnchor qs pt with
      | none => 0
      | some (.quads _) => 1
      | some (.point _) => 2

/-! ## Listing -/

/-- The kind code of a mark: 0 highlight, 1 note, 2 free text, 3 ink. -/
def kindCode : Kind → Nat
  | .highlight _ => 0
  | .note .. => 1
  | .freeText .. => 2
  | .ink .. => 3

/-- The colour the viewer draws the mark in (`Mark.hex`): the palette's, or the mark's own. -/
def displayRgb (m : Mark) : Marks.Rgb :=
  match m.kind with
  | .freeText _ _ _ c | .ink _ _ _ c => c
  | _ => m.color.rgb

/-- **The numbers of one mark** (layout read by `macos/safepdf_marks.c`): kind, page, colour
index, display R, G, B, state (0 new, 1 saved, 2 saved and changed), is a comment, size,
opacity, has point, x, y, has rect, rect (4), quad count, quads (4 each), stroke count, stroke
lengths, stroke points (2 each). -/
def markNums (h : Handle) (changed : List Nat) (m : Mark) : Array Float :=
  let s := h.store
  let b (x : Bool) : Float := if x then 1 else 0
  let (r, g, bl) := displayRgb m
  let st : Nat := if !s.isSaved m.id then 0 else if changed.contains m.id then 2 else 1
  let (size, op, strokes) : Nat × Nat × List (List Pt) := match m.kind with
    | .freeText _ _ z _ => (z, 100, [])
    | .ink ss w o _ => (w, o, ss)
    | _ => (0, 100, [])
  let pt : Option Pt := match m.kind with
    | .note _ (.point p) => some p
    | .freeText _ p _ _ => some p
    | _ => none
  let rect := m.rect (boxOf h m.page)
  let rectNums := match rect with
    | some r => [toF r.llx, toF r.lly, toF r.urx, toF r.ury]
    | none => [0, 0, 0, 0]
  let qs := m.quads
  (#[natF (kindCode m.kind), natF m.page, natF (colorIdx m.color), natF r, natF g, natF bl,
     natF st, b (s.isComment m), natF size, natF op, b pt.isSome,
     (pt.map (toF ·.x)).getD 0, (pt.map (toF ·.y)).getD 0, b rect.isSome] ++
   rectNums.toArray ++ #[natF qs.length] ++
   (qs.flatMap fun q => [toF q.llx, toF q.lly, toF q.urx, toF q.ury]).toArray ++
   #[natF strokes.length] ++ (strokes.map (natF ·.length)).toArray ++
   (strokes.flatMap (·.flatMap fun p => [toF p.x, toF p.y])).toArray)

/-- **The marks of page `page`** (every page when `all` ≠ 0), oldest first: their ids, their
numbers (`markNums`, concatenated) and their texts. -/
@[export safepdf_marks_lean_list]
def list (h : Handle) (page : USize) (all : UInt8) : Array USize × FloatArray × Array String :=
  let ms := if all != 0 then h.store.marks.toList else h.store.onPage page.toNat
  let changed := h.store.changedSaved.map (·.id)
  (ms.toArray.map (satU ·.id), ⟨ms.foldl (fun acc m => acc ++ markNums h changed m) #[]⟩,
    ms.toArray.map (·.text))

/-! ## Save -/

/-- Save error code: the build or its check failed. -/
def errBuild : Nat := 1
/-- Save error code: a certified document whose `/DocMDP` permits no annotation changes. -/
def errCertified : Nat := 2
/-- Save error code: an encrypted document without a fresh IV seed. -/
def errSeed : Nat := 3
/-- Save error code: the expected output is above the caller's ceiling. -/
def errOutput : Nat := 4

/-- Save note flag: the document uses RC4 (`Save.rc4Note`). -/
def noteRc4 : Nat := 1
/-- Save note flag: the document is signed (`Save.signedNote`). -/
def noteSigned : Nat := 2
/-- Save note flag: saved marks were deleted (`Save.retentionText`). -/
def noteRetention : Nat := 4
/-- Save note flag: nothing changed, the bytes are the original's (a plain copy). -/
def noteCopy : Nat := 8

/-- The expected size of a Save's output (`Save.outputEstimate`; the GUI's budget). -/
@[export safepdf_marks_lean_output_estimate]
def outputEstimate (h : Handle) : USize := satU (Save.outputEstimate h.doc.doc h.store)

/-- **The save** (see the module doc): the bytes, then the numbers `[marks written or deleted,
marks in the written file, bytes appended, note flags, deleted saved marks]` and the notes'
texts; or an error code with its message. `date` empty: now (UTC); `maxOut` 0: no ceiling. -/
@[export safepdf_marks_lean_save_build]
def saveBuild (h : Handle) (seed : ByteArray) (date : String) (maxOut : USize) :
    IO (Except (Nat × String) (ByteArray × FloatArray × Array String)) := do
  let doc := h.doc.doc
  let s := h.store
  let est := Save.outputEstimate doc s
  if maxOut != 0 && est > maxOut.toNat then
    return .error (errOutput, s!"the saved file would need up to {est} bytes, more than the \
      {maxOut.toNat} allowed")
  if doc.file.crypt.isSome && seed.size < 2 * Save.seedSize then
    return .error (errSeed, s!"cannot save an encrypted document without {2 * Save.seedSize} \
      fresh random bytes for its IVs")
  let date ← if date.isEmpty then Save.nowDate else pure date
  match Save.build limits doc s date seed with
  | .error e =>
    let code := if Save.refusal (Save.protection doc limits) == some e then errCertified
      else errBuild
    return .error (code, e)
  | .ok (bytes, got, n) =>
    let prot := Save.notesFor limits doc n
    let isRc4 := prot.contains Save.rc4Note
    let isSigned := prot.contains Save.signedNote
    let del := s.deletedSaved.length
    let flags := (if isRc4 then noteRc4 else 0) + (if isSigned then noteSigned else 0) +
      (if del > 0 then noteRetention else 0) + (if n == 0 then noteCopy else 0)
    let notes := prot ++ (if del > 0 then [Save.retentionText del] else [])
    return .ok (bytes, ⟨#[natF n, natF got.length, natF (bytes.size - doc.file.bytes.size),
      natF flags, natF del]⟩, notes.toArray)

/-- **Is the opened file on disk unchanged?** (`Save.diskState`): `disk` the bytes the GUI
read back (capped at the opened size + 1), `readable` 0 when it could not read them. 0 same,
1 changed, 2 missing. -/
@[export safepdf_marks_lean_disk_state]
def diskState (h : Handle) (disk : ByteArray) (readable : UInt8) : UInt8 :=
  match Save.diskState h.doc.doc.file.bytes (if readable != 0 then some disk else none) with
  | .same => 0
  | .changed => 1
  | .missing => 2

/-- **Save's route** (`Save.route`): 0 nothing, 1 library, 2 Save As…, 3 overwrite without
asking, 4 overwrite after the first-overwrite question. -/
@[export safepdf_marks_lean_route]
def route (dirty library inMemory confirmed : UInt8) : UInt8 :=
  match Save.route (dirty != 0) (library != 0) (inMemory != 0) (confirmed != 0) with
  | .nothing => 0
  | .library => 1
  | .saveAs => 2
  | .overwrite false => 3
  | .overwrite true => 4

/-- The first-overwrite question for `name` with the store's pending count
(`Save.overwriteQuestion`, as `Viewer.overwriteInto`). -/
@[export safepdf_marks_lean_overwrite_question]
def overwriteQuestion (h : Handle) (name : String) : String :=
  Save.overwriteQuestion name h.store.pending

/-- The changed-on-disk question (`Save.changedQuestion`; `st` as `diskState`, 2 missing). -/
@[export safepdf_marks_lean_changed_question]
def changedQuestion (name : String) (st : UInt8) : String :=
  Save.changedQuestion name (if st == 2 then .missing else .changed)

/-- The unsaved-changes question before `what` (`Save.unsavedQuestion` with the store's pending
count). -/
@[export safepdf_marks_lean_unsaved_question]
def unsavedQuestion (h : Handle) (name what : String) (library inMemory into : UInt8) : String :=
  Save.unsavedQuestion name what h.store.pending (library != 0) (inMemory != 0) (into != 0)

/-- Why the opened file cannot be overwritten (`Save.writeProblem`); empty when it can. -/
@[export safepdf_marks_lean_write_problem]
def writeProblem (name : String) (fileWritable dirWritable : UInt8) : String :=
  (Save.writeProblem name (fileWritable != 0) (dirWritable != 0)).getD ""

/-- Why a Save As… / Export target cannot be written (`Save.targetProblem`); empty when it
can. -/
@[export safepdf_marks_lean_target_problem]
def targetProblem (name : String) (isDir isThere fileWritable dirWritable opened : UInt8) :
    String :=
  (Save.targetProblem name (isDir != 0) (isThere != 0) (fileWritable != 0) (dirWritable != 0)
    (opened != 0)).getD ""

/-- The Save As… proposal (`Save.defaultTarget`). -/
@[export safepdf_marks_lean_default_target]
def defaultTarget (path : String) : String := Save.defaultTarget path

/-- A chosen name with the extension `ext` (`Save.withExt`). -/
@[export safepdf_marks_lean_with_ext]
def withExt (name ext : String) : String := Save.withExt name ext

/-! ## XFDF -/

/-- The expected size of an XFDF export (`Xfdf.exportEstimate`; the GUI's budget). -/
@[export safepdf_marks_lean_xfdf_estimate]
def xfdfEstimate (h : Handle) : USize := satU (Xfdf.exportEstimate h.store)

/-- **Export** every mark as XFDF (`Xfdf.toXfdf`, page boxes of the document): `href` the PDF's
file name for `<f href>` (empty: none), `date` (empty: now), `maxOut` a ceiling on
`Xfdf.exportEstimate` (0: none). UTF-8 bytes, or an error. -/
@[export safepdf_marks_lean_xfdf_export]
def xfdfExport (h : Handle) (href date : String) (maxOut : USize) : IO (Except String ByteArray) := do
  let est := Xfdf.exportEstimate h.store
  if maxOut != 0 && est > maxOut.toNat then
    return .error s!"the export would need up to {est} bytes, more than the {maxOut.toNat} allowed"
  let date ← if date.isEmpty then Save.nowDate else pure date
  let xml := Xfdf.toXfdf h.store (Save.pageBox h.doc.doc) date
    (if href.isEmpty then none else some href)
  return .ok xml.toUTF8

/-- **Import** XFDF `bytes` (`Xfdf.readXfdf` with the default limits and the document's page
count, then `Xfdf.importItems`; one undo step): the new handle, the numbers `[added, already
present, skipped, ignored]`, and per skipped annotation (the first `Xfdf.maxReport`) its element
and reason, alternating. A refused file is an error and changes nothing. -/
@[export safepdf_marks_lean_xfdf_import]
def xfdfImport (h : Handle) (bytes : ByteArray) :
    Except String (Handle × FloatArray × Array String) :=
  match Xfdf.readXfdf {} bytes (pages := some h.doc.doc.pages.size) with
  | .error e => .error e.message
  | .ok rep =>
    let (store, ids, dups) := Xfdf.importItems h.store rep.items
    let h' := if ids.isEmpty then h
      else { h with store, hist := h.hist.record store.marks }
    .ok (h', ⟨#[natF ids.length, natF dups, natF rep.skippedCount, natF rep.ignored]⟩,
      (rep.skipped.flatMap fun k => [k.element, k.reason]).toArray)

/-- The message of an `IO` error (the only `IO` here is the clock). -/
@[export safepdf_marks_lean_error_text]
def errorText (e : IO.Error) : String := toString e

/-! ## Tool state, bubble and parameters (task 11.3e1)

The rules of the Tk viewer's floating toolbars and tool modes (`Bubble`, `Toolbar`), for the
native shell's tools, selection bubble and pop-overs: nothing here decides anything itself. -/

/-- The bytes of an RGB triple, as numbers. -/
def rgbNums (c : Marks.Rgb) : List Float := [natF c.1, natF c.2.1, natF c.2.2]

/-- `0xRRGGBB` of an RGB triple. -/
def rgbWord (c : Marks.Rgb) : Nat := c.1 % 256 * 65536 + c.2.1 % 256 * 256 + c.2.2 % 256

/-- **The tools' parameters** (layout read by `macos/safepdf_marks.c`): the highlight palette
(`Color.all`, R G B each), the Add text / Draw palette (`Bubble.EdPop.palette`: count, then R G
B each), the font size, thickness and opacity sliders (`Bubble.EdPop.fontSize`, `thickness`,
`opacity`: lo, hi, step, the default of `Bubble.Ui`), the default text and line colours
(`Bubble.Ui`), `Core.Write.Annots.ftPad`, `lineFactor` and `Marks.noteSize`. `_u` is ignored. -/
@[export safepdf_marks_lean_tool_params]
def toolParams (_u : UInt8) : FloatArray :=
  let u : Bubble.Ui := {}
  let sl (s : Bubble.Slider) (d : Nat) : List Float := [natF s.lo, natF s.hi, natF s.step, natF d]
  ⟨(Color.all.flatMap (rgbNums ·.rgb) ++ [natF Bubble.EdPop.palette.length] ++
    Bubble.EdPop.palette.flatMap rgbNums ++ sl Bubble.EdPop.fontSize u.ftSize ++
    sl Bubble.EdPop.thickness u.inkThick ++ sl Bubble.EdPop.opacity u.inkOpacity ++
    [natF (rgbWord u.ftColor), natF (rgbWord u.inkColor),
     toF Core.Write.Annots.ftPad, toF Core.Write.Annots.lineFactor, toF Marks.noteSize]).toArray⟩

/-- The editor mode as a number: 0 none, 1 Add text, 2 Draw. -/
def editorCode : Bubble.Editor → Nat
  | .none => 0
  | .text => 1
  | .draw => 2

/-- The editor mode of a number (anything else: none). -/
def editorOf (n : Nat) : Bubble.Editor :=
  match n with
  | 1 => .text
  | 2 => .draw
  | _ => .none

/-- The mode as `safepdf_tool_mode` (`Toolbar.Mode.of`): 0 select, 1 highlight, 2 text,
3 draw. -/
def modeCode (u : Bubble.Ui) : Nat :=
  match Toolbar.Mode.of u with
  | .select => 0
  | .highlight => 1
  | .text => 2
  | .draw => 3

/-- A tool state as numbers: tool, pop-over, show all, picker, editor, editor pop-over,
thickness, font size, text colour, line colour, line thickness, line opacity. -/
def uiNums (u : Bubble.Ui) : List Float :=
  let b (x : Bool) : Float := if x then 1 else 0
  [b u.tool, b u.popover, b u.showAll, b u.picker, natF (editorCode u.editor), b u.edPop,
   natF u.thickness, natF u.ftSize, natF (rgbWord u.ftColor), natF (rgbWord u.inkColor),
   natF u.inkThick, natF u.inkOpacity]

/-- A tool state from numbers (`uiNums`'s layout; missing or bad numbers: the defaults). -/
def uiOf (a : FloatArray) : Bubble.Ui :=
  let d : Bubble.Ui := {}
  let n (i : Nat) (dflt : Nat) : Nat :=
    match a.toList[i]? with
    | some f => if f.isNaN || f.isInf || f < 0 || f > 4294967295.0 then dflt else f.toUInt32.toNat
    | none => dflt
  let b (i : Nat) (dflt : Bool) : Bool := n i (if dflt then 1 else 0) != 0
  { tool := b 0 d.tool, popover := b 1 d.popover, showAll := b 2 d.showAll,
    picker := b 3 d.picker, editor := editorOf (n 4 (editorCode d.editor)), edPop := b 5 d.edPop,
    thickness := n 6 d.thickness, ftSize := n 7 d.ftSize,
    ftColor := rgbOf (n 8 (rgbWord d.ftColor)).toUInt32,
    inkColor := rgbOf (n 9 (rgbWord d.inkColor)).toUInt32,
    inkThick := n 10 d.inkThick, inkOpacity := n 11 d.inkOpacity }

/-- **A step of the tool state** (`op`): 0 the initial state, 1 the toolbar's Highlight button
(`Ui.toolClick`, `arg` ≠ 0: there is a selection), 2 Edit → Highlight tool (`Ui.toggleTool`),
3 the Add text / Draw button (`Ui.selectEditor`, `arg` the editor 1 or 2), 4 the Select text
button (`Toolbar.selectTool`), 5 Escape (`Ui.escape`). The new state (`uiNums`), then its mode
(`modeCode`) and whether the Highlight button highlights the selection (op 1). Empty for an
unknown op. -/
@[export safepdf_marks_lean_ui_step]
def uiStep (ui : FloatArray) (op arg : UInt8) : FloatArray :=
  let u := uiOf ui
  let r : Option (Bubble.Ui × Bool) := match op.toNat with
    | 0 => some ({}, false)
    | 1 => some (u.toolClick (arg != 0))
    | 2 => some (u.toggleTool, false)
    | 3 => some (u.selectEditor (editorOf arg.toNat), false)
    | 4 => some (Toolbar.selectTool u, false)
    | 5 => some (u.escape, false)
    | _ => none
  match r with
  | none => FloatArray.empty
  | some (u, hl) => ⟨(uiNums u ++ [natF (modeCode u), if hl then 1 else 0]).toArray⟩

#guard (uiStep (uiStep FloatArray.empty 0 0) 1 0).toList.take 2 == [1, 1]
#guard (uiStep (uiStep FloatArray.empty 0 0) 1 1).toList.getLast? == some 1
#guard (uiStep (uiStep (uiStep FloatArray.empty 0 0) 3 2) 4 0).toList[12]? == some 0

/-- The bubble kind as a number: 0 float, 1 edit, 2 editor. -/
def kindNum : Bubble.Kind → Nat
  | .float => 0
  | .edit => 1
  | .editor => 2

/-- The bubble kind of a number. -/
def kindOfNum : Nat → Option Bubble.Kind
  | 0 => some .float
  | 1 => some .edit
  | 2 => some .editor
  | _ => none

/-- A bubble button as a number: 0 highlight, 1 colour, 2 comment, 3 delete. -/
def btnNum : Bubble.Btn → Nat
  | .highlight => 0
  | .color => 1
  | .comment => 2
  | .delete => 3

/-- **The bubble to show** (`Bubble.kindFor`): 0 float, 1 edit, 255 none. -/
@[export safepdf_marks_lean_bubble_kind]
def bubbleKind (selHere markHere showAll : UInt8) : UInt8 :=
  let u : Bubble.Ui := { showAll := showAll != 0 }
  match Bubble.kindFor (selHere != 0) (markHere != 0) u with
  | some k => (kindNum k).toUInt8
  | none => 255

/-- **A bubble's layout** (`Bubble.Kind.layout`): width and height, then per button its number
(`btnNum`), its command (`Btn.cmd?`, index in `Menu.Cmd.all`, -1 none) and its range x0 x1
from the bubble's left edge; the tooltips (`Btn.tip`) in the same order. Empty for an unknown
kind. -/
@[export safepdf_marks_lean_bubble_layout]
def bubbleLayout (kind : UInt8) : FloatArray × Array String :=
  match kindOfNum kind.toNat with
  | none => (FloatArray.empty, #[])
  | some k =>
    let cmd (b : Bubble.Btn) : Float :=
      match b.cmd? with
      | some c => natF (Menu.Cmd.all.idxOf c)
      | none => -1
    (⟨(#[toF k.width, toF Bubble.height] ++ (k.layout.flatMap fun (b, x0, x1) =>
        [natF (btnNum b), cmd b, toF x0, toF x1]).toArray)⟩,
     (k.layout.map fun (b, _, _) => b.tip).toArray)

/-- **Where a bubble goes** (`Bubble.place`): `sel` the selection's rectangles in canvas
coordinates (`x0 y0 x1 y1` each, y down), the bubble's size `w × h`, the area `x0 y0 x1 y1`.
The rectangle (4 numbers), or empty when there is none or a number is refused. -/
@[export safepdf_marks_lean_bubble_place]
def bubblePlace (sel : FloatArray) (w h : Float) (area : FloatArray) : FloatArray :=
  let r : Option Bubble.Rect := do
    let rs ← boxesOf sel
    let ar ← boxesOf area
    let a ← ar.head?
    let w ← ratOfFloat w
    let h ← ratOfFloat h
    Bubble.place (rs.map fun b => ⟨b.llx, b.lly, b.urx, b.ury⟩) w h ⟨a.llx, a.lly, a.urx, a.ury⟩
  match r with
  | some r => ⟨#[toF r.x0, toF r.y0, toF r.x1, toF r.y1]⟩
  | none => FloatArray.empty

/-- **Escape over the open transients** (`Toolbar.onEscape`): `opened` and the result are bit
masks over `Toolbar.Transient.order` (bit 0 the note popup, 1 the colour picker, 2 the
Highlight pop-over, 3 the Add text / Draw pop-over, 4 the go-to bar, 5 the find bar). -/
@[export safepdf_marks_lean_escape_closes]
def escapeCloses (opened : UInt32) : UInt32 :=
  let order := Toolbar.Transient.order
  let idx := List.range order.length
  let open_ := (idx.zip order).filterMap fun (i, t) =>
    if (opened.toNat / 2 ^ i) % 2 == 1 then some t else none
  let closed := Toolbar.onEscape open_
  ((idx.zip order).foldl (fun acc (i, t) => if closed.contains t then acc + 2 ^ i else acc) 0).toUInt32

#guard escapeCloses 0b101 == 0b1 && escapeCloses 0b110100 == 0b100 && escapeCloses 0 == 0

end SafePdf.Shell.FfiMarks
