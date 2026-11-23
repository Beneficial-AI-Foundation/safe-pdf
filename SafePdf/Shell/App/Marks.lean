import SafePdf.Core.Raster.Geom
import SafePdf.Core.Write.Annots

/-!
# User marks: highlights and notes (task 9.4; Plan.md §6 Phase 9 "User highlights in colors", "Notes", "Persistence — annotations inside the PDF", §10 `SafePdf/Shell/`)

The Tk-free model of the marks a reader adds to a document (unverified shell code, total,
checked by `#guard`s and small theorems). Task 9.5b turns each mark into an annotation
dictionary (`/Highlight` with `/QuadPoints`, `/Text` with `/Contents`) for
`Core.Write.Incremental.writeAnnots`; task 9.5c (`Shell.App.Save`) saves the unsaved ones into
the PDF and restores them from it.

* **Colours** (`Color`): PDF.js's highlight palette (`web/app_options.js`,
  `highlightEditorColors`): yellow `#FFFF98`, green `#53FFBC`, blue `#80EBFF`, pink
  `#FFCBE6`, red `#FF4F5F`; `Color.rgb` gives the bytes, `Color.unit` the `/C` components.
* **Marks** (`Mark`): a stable id (`Mark.id`; `/NM` is `Mark.nm` = `safepdf-mark-ID`, the
  prefix lets 9.5c tell our marks from other annotations), the page index, the colour and the
  kind: a highlight over quads, or a note with its text anchored to quads (a selection) or to
  a page point.
* **Quads** are page-space boxes (`Geom.Box`), one per line run of a selection: the C3 glyph
  boxes of `Select.rangeBoxes`. `Mark.quadPoints` lists them in the `/QuadPoints` order that
  PDF.js and Acrobat use (upper-left, upper-right, lower-left, lower-right); `Mark.rect` is
  the `/Rect`. Everything is in page space, so marks survive zoom, rotation and page changes.
* **Notes** are drawn as an icon of `noteSize` × `noteSize` page units (as a `/Text`
  annotation's icon; PDF.js scales it with the page): at a point anchor its upper-left corner
  is the point, at a quad anchor it sits right of the first quad's upper-right corner; it is
  moved inside the page box when it would stick out (`Mark.iconBox`).
* **Store** (`Store`): the marks of a document in creation order (later ones on top) and the
  next id; `Store.noteOn` finds the note anchored to a highlight's quads (its comment, 9.8). Ids are never reused (`Store.add_id`, `Store.add_next`); `Store.restore` keeps
  the ids of marks read back from a file and `Store.load` builds the store of a file's marks
  (9.5c); `Store.saved` lists the marks stored in the file and `Store.base` their state
  there; `Store.unsaved` (new marks), `Store.changedSaved` (saved marks recoloured or edited)
  and `Store.deletedSaved` (saved marks deleted) are what Save still has to write, and
  `Store.dirty` says whether there is any of it (task 9.5g: saved marks are editable).
  A highlight's **comment** is the newest note anchored to exactly its quads with a
  non-empty text (`Store.commentOf`, 9.8); Save writes it into the highlight as pdf.js does
  (`/Contents` + `/Popup`, 9.5g); deleting a highlight deletes its comment
  (`Store.removeWithComment`). Operations: add, remove, recolour, edit the
  text, find, the marks of a page, hit-testing (`Store.hitAt`: the topmost mark whose icon
  or quads contain a page point; icons are above highlights).
* **Free text and ink** (task 9.9, PDF.js's "Add text" and "Draw" editors): a free-text mark
  holds its text, the page point of its box's upper-left corner, the font size (5–100, PDF.js
  default 10) and a text colour of its own (any RGB, `Rgb`); its box is
  `Core.Write.Annots.freeTextBox` (Helvetica metrics, the box Save writes as `/Rect`). An ink
  mark holds its strokes (page-space points, in drawing order; one mark per drawing session,
  as PDF.js groups them), the thickness (1–20), the opacity in percent and a colour; its box
  is `Core.Write.Annots.inkBox`. Their `Mark.color` is unused (yellow). Both are drawn as
  canvas items while unsaved, are hit-tested by their boxes (above highlights), and can be
  moved (`Store.translate`), edited (`setText`, `setRgb`, `setSize`, `setOpacity`,
  `addStroke`) and deleted.
* **Pixels** (`multiplyRect`, `pixelRect`, `composite`): highlights are blended into the
  rendered page image with the *multiply* blend mode, as PDF.js draws them
  (`web/draw_layer_builder.css`: `mix-blend-mode: multiply`, fill opacity 1): white paper
  takes the colour, black text stays black.
-/

namespace SafePdf.Shell.App.Marks

open SafePdf.Core
open SafePdf.Core.Raster.Geom (Pt Box toScreen)

/-! ## Colours -/

/-- A highlight colour of PDF.js's palette. -/
inductive Color where
  /-- Yellow `#FFFF98` (the default). -/
  | yellow
  /-- Green `#53FFBC`. -/
  | green
  /-- Blue `#80EBFF`. -/
  | blue
  /-- Pink `#FFCBE6`. -/
  | pink
  /-- Red `#FF4F5F`. -/
  | red
  deriving DecidableEq, Repr, Inhabited

/-- The palette in PDF.js's order. -/
def Color.all : List Color := [.yellow, .green, .blue, .pink, .red]

/-- Name of the colour (Tcl value of the colour menus, `emit highlight NAME`). -/
def Color.name : Color → String
  | .yellow => "yellow"
  | .green => "green"
  | .blue => "blue"
  | .pink => "pink"
  | .red => "red"

/-- Menu label of the colour. -/
def Color.label : Color → String
  | .yellow => "Yellow"
  | .green => "Green"
  | .blue => "Blue"
  | .pink => "Pink"
  | .red => "Red"

/-- Red, green and blue bytes (PDF.js `highlightEditorColors`). -/
def Color.rgb : Color → Nat × Nat × Nat
  | .yellow => (0xFF, 0xFF, 0x98)
  | .green => (0x53, 0xFF, 0xBC)
  | .blue => (0x80, 0xEB, 0xFF)
  | .pink => (0xFF, 0xCB, 0xE6)
  | .red => (0xFF, 0x4F, 0x5F)

/-- Two hexadecimal digits of a byte. -/
def hex2 (n : Nat) : String :=
  let d (k : Nat) : Char := "0123456789ABCDEF".toList.getD (k % 16) '0'
  String.ofList [d (n / 16), d n]

/-- `#RRGGBB` of the colour (Tk colour syntax). -/
def Color.hex (c : Color) : String :=
  let (r, g, b) := c.rgb
  "#" ++ hex2 r ++ hex2 g ++ hex2 b

/-- The colour as `/C` components in `[0, 1]` (task 9.5b). -/
def Color.unit (c : Color) : Rat × Rat × Rat :=
  let (r, g, b) := c.rgb
  ((r : Rat) / 255, (g : Rat) / 255, (b : Rat) / 255)

/-- The colour named `s` (`Color.name`). -/
def Color.ofName (s : String) : Option Color :=
  Color.all.find? (·.name == s)

#guard Color.all.map Color.hex == ["#FFFF98", "#53FFBC", "#80EBFF", "#FFCBE6", "#FF4F5F"]
#guard Color.all.all fun c => Color.ofName c.name == some c
#guard Color.ofName "black" == none
#guard Color.yellow.unit == (1, 1, 152 / 255)

/-! ## Marks -/

/-- What a note is attached to. -/
inductive Anchor where
  /-- The quads of a text selection (page space). -/
  | quads (qs : List Box)
  /-- A page point. -/
  | point (p : Pt)
  deriving Repr, Inhabited

/-- An RGB colour as bytes (free text and ink, task 9.9). -/
abbrev Rgb := Nat × Nat × Nat

/-- `#RRGGBB` of an RGB colour. -/
def rgbHex (c : Rgb) : String := "#" ++ hex2 c.1 ++ hex2 c.2.1 ++ hex2 c.2.2

/-- An RGB colour as `/C` components in `[0, 1]`. -/
def rgbUnit (c : Rgb) : Rat × Rat × Rat :=
  ((c.1 : Rat) / 255, (c.2.1 : Rat) / 255, (c.2.2 : Rat) / 255)

/-- The kind of a mark. -/
inductive Kind where
  /-- A highlight over `quads` (page space, one per line run). -/
  | highlight (quads : List Box)
  /-- A note with its text and anchor. -/
  | note (text : String) (anchor : Anchor)
  /-- Free text (task 9.9): the text, the upper-left corner of its box (page space), the font
  size and the text colour. -/
  | freeText (text : String) (pos : Pt) (size : Nat) (rgb : Rgb)
  /-- Ink (task 9.9): strokes of page points, thickness, opacity (percent) and colour. -/
  | ink (strokes : List (List Pt)) (width : Nat) (opacity : Nat) (rgb : Rgb)
  deriving Repr, Inhabited

/-- A user mark. -/
structure Mark where
  /-- Stable id (unique within a document's `Store`, never reused). -/
  id : Nat
  /-- Page index (0-based). -/
  page : Nat
  /-- Colour (highlight fill, note icon). -/
  color : Color
  /-- Highlight or note. -/
  kind : Kind
  deriving Repr, Inhabited

/-- Prefix of the `/NM` name of our marks (9.5c reads marks back by it). -/
def nmPrefix : String := "safepdf-mark-"

/-- The `/NM` (annotation name) of a mark: `safepdf-mark-ID`. -/
def Mark.nm (m : Mark) : String := nmPrefix ++ toString m.id

/-- The id in an `/NM` name written by `Mark.nm`. -/
def idOfNm (s : String) : Option Nat :=
  if s.startsWith nmPrefix then (s.drop nmPrefix.length).toString.toNat? else none

/-- Whether the mark is a note. -/
def Mark.isNote (m : Mark) : Bool :=
  match m.kind with
  | .note .. => true
  | _ => false

/-- Whether the mark is a highlight. -/
def Mark.isHighlight (m : Mark) : Bool :=
  match m.kind with
  | .highlight _ => true
  | _ => false

/-- Whether the mark is free text or ink (an editor of task 9.9: moved, not anchored). -/
def Mark.isEditor (m : Mark) : Bool :=
  match m.kind with
  | .freeText .. | .ink .. => true
  | _ => false

/-- Whether the mark is free text (task 9.r5: the one kind whose saved appearance needs a
font program to be painted). -/
def Mark.isFreeText (m : Mark) : Bool :=
  match m.kind with
  | .freeText .. => true
  | _ => false

/-- The note or free text (empty for a highlight and ink). -/
def Mark.text (m : Mark) : String :=
  match m.kind with
  | .note t _ => t
  | .freeText t .. => t
  | _ => ""

/-- The quads of a mark (none for a note at a point, free text and ink). -/
def Mark.quads (m : Mark) : List Box :=
  match m.kind with
  | .highlight qs => qs
  | .note _ (.quads qs) => qs
  | _ => []

/-- The colour the viewer draws the mark in: the palette colour, or a free text's or ink's
own colour. -/
def Mark.hex (m : Mark) : String :=
  match m.kind with
  | .freeText _ _ _ c | .ink _ _ _ c => rgbHex c
  | _ => m.color.hex

/-- A page point as a Core point. -/
def ptPair (p : Pt) : Rat × Rat := (p.x, p.y)

/-- A Core rectangle as a box. -/
def boxOfRect (r : Core.Write.Annots.Rect) : Box := ⟨r.x0, r.y0, r.x1, r.y1⟩

/-- The page-space box of free text or ink (`Core.Write.Annots.freeTextBox` / `inkBox`, the
`/Rect` Save writes); `none` for other marks and ink without points. -/
def Mark.box (m : Mark) : Option Box :=
  match m.kind with
  | .freeText t p sz _ => some (boxOfRect (Core.Write.Annots.freeTextBox p.x p.y sz t))
  | .ink ss w _ _ => (Core.Write.Annots.inkBox (ss.map (·.map ptPair)) w).map boxOfRect
  | _ => none

/-- Side of a note icon in page units (a `/Text` annotation's usual 20 × 20 icon). -/
def noteSize : Rat := 20

/-- Union of two boxes. -/
def union (a b : Box) : Box :=
  ⟨min a.llx b.llx, min a.lly b.lly, max a.urx b.urx, max a.ury b.ury⟩

/-- Union of a list of boxes (`none` for the empty list). -/
def unionAll : List Box → Option Box
  | [] => none
  | b :: bs => some (bs.foldl union b)

/-- Moves `v` so that the interval `[v, v + s]` lies in `[lo, hi]` when it fits (else `lo`). -/
def clampInto (lo hi s v : Rat) : Rat :=
  if hi - lo < s then lo else max lo (min v (hi - s))

/-- The note icon's page-space box inside the page box `pb`: upper-left corner at a point
anchor, right of the first quad's upper-right corner for a quad anchor; moved inside `pb`.
`none` for a highlight. -/
def Mark.iconBox (pb : Box) (m : Mark) : Option Box :=
  let place (x yTop : Rat) : Box :=
    let x := clampInto pb.llx pb.urx noteSize x
    let y := clampInto pb.lly pb.ury noteSize (yTop - noteSize)
    ⟨x, y, x + noteSize, y + noteSize⟩
  match m.kind with
  | .highlight _ | .freeText .. | .ink .. => none
  | .note _ (.point p) => some (place p.x p.y)
  | .note _ (.quads qs) =>
    match qs with
    | q :: _ => some (place q.urx q.ury)
    | [] => none

/-- The `/QuadPoints` of a mark: per quad `x1 y1 x2 y2 x3 y3 x4 y4` = upper-left,
upper-right, lower-left, lower-right (the order PDF.js and Acrobat write and read). -/
def Mark.quadPoints (m : Mark) : List Rat :=
  m.quads.flatMap fun b => [b.llx, b.ury, b.urx, b.ury, b.llx, b.lly, b.urx, b.lly]

/-- The `/Rect` of the annotation (task 9.5b): the union of the quads, and for a note its
icon box (the page box `pb` places the icon). -/
def Mark.rect (pb : Box) (m : Mark) : Option Box :=
  match m.kind with
  | .highlight qs => unionAll qs
  | .note _ _ => m.iconBox pb
  | _ => m.box

/-! ## Store -/

/-- The marks of one document: creation order (later marks are drawn on top) and the next
fresh id. -/
structure Store where
  /-- Marks, oldest first. -/
  marks : Array Mark := #[]
  /-- The id the next mark gets (larger than every id in `marks`). -/
  nextId : Nat := 1
  /-- Ids of the marks that are stored in the open file (read back on open or written by a
  save, task 9.5c). They are drawn by the renderer from their appearance streams (after an
  edit, from the viewer's preview of the next save, task 9.5g). -/
  saved : List Nat := []
  /-- The saved marks as they are in the file (task 9.5g: what edits are compared with). -/
  base : List Mark := []
  deriving Inhabited

/-- Adds a mark of `kind` on `page` in `color`; returns the store and the new mark's id. -/
def Store.add (s : Store) (page : Nat) (color : Color) (kind : Kind) : Store × Nat :=
  ({ s with marks := s.marks.push ⟨s.nextId, page, color, kind⟩, nextId := s.nextId + 1 },
    s.nextId)

/-- The new mark gets the store's next id. -/
theorem Store.add_id (s : Store) (p : Nat) (c : Color) (k : Kind) :
    (s.add p c k).2 = s.nextId := rfl

/-- Adding a mark advances the next id, so ids are never reused. -/
theorem Store.add_next (s : Store) (p : Nat) (c : Color) (k : Kind) :
    (s.add p c k).1.nextId = s.nextId + 1 := rfl

/-- Adds a highlight over `quads`; `none` when there are no quads. -/
def Store.addHighlight (s : Store) (page : Nat) (color : Color) (quads : List Box) :
    Option (Store × Nat) :=
  if quads.isEmpty then none else some (s.add page color (.highlight quads))

/-- Adds a note with `text` at `anchor`. -/
def Store.addNote (s : Store) (page : Nat) (color : Color) (text : String) (anchor : Anchor) :
    Store × Nat :=
  s.add page color (.note text anchor)

/-- Puts back a mark read from a file with its own id (task 9.5c): replaces a mark with the
same id, and keeps `nextId` above every id. -/
def Store.restore (s : Store) (m : Mark) : Store :=
  { s with marks := (s.marks.filter (·.id != m.id)).push m,
           nextId := max s.nextId (m.id + 1) }

/-- Whether mark `id` is stored in the open file (task 9.5c). -/
def Store.isSaved (s : Store) (id : Nat) : Bool := s.saved.contains id

/-- The marks not yet stored in the file, oldest first (what Save writes, task 9.5c). -/
def Store.unsaved (s : Store) : List Mark :=
  (s.marks.filter (!s.isSaved ·.id)).toList

/-- The mark with id `id`. -/
def Store.find? (s : Store) (id : Nat) : Option Mark :=
  s.marks.find? (·.id == id)

/-- Whether two kinds agree in everything Save writes: a highlight's quads; a note's text
and quads; free text's text, position, size and colour; ink's strokes, thickness, opacity and
colour. -/
def Kind.same : Kind → Kind → Bool
  | .highlight a, .highlight b => a == b
  | .note t a, .note u b =>
    t == u && (match a, b with
      | .quads x, .quads y => x == y
      | .point _, .point _ => true
      | _, _ => false)
  | .freeText t p z c, .freeText u q y d => t == u && p == q && z == y && c == d
  | .ink s w o c, .ink t v p d => s == t && w == v && o == p && c == d
  | _, _ => false

/-- Whether two marks are the same in everything Save writes (id, page, colour, kind with its
text, quads, position, strokes, sizes and colours). -/
def Mark.same (a b : Mark) : Bool :=
  a.id == b.id && a.page == b.page && a.color == b.color && a.kind.same b.kind

/-- Saved marks that differ from their state in the file (recoloured, text edited; 9.5g). -/
def Store.changedSaved (s : Store) : List Mark :=
  (s.marks.filter fun m => s.isSaved m.id &&
    match s.base.find? (·.id == m.id) with
    | some b => !m.same b
    | none => false).toList

/-- Ids of saved marks that were deleted (9.5g). -/
def Store.deletedSaved (s : Store) : List Nat :=
  s.saved.filter fun id => (s.find? id).isNone

/-- Whether there are unsaved changes: new marks, or saved marks changed or deleted (the
title's `*`, the prompt on close/quit/open). -/
def Store.dirty (s : Store) : Bool :=
  s.marks.any (!s.isSaved ·.id) || !s.changedSaved.isEmpty || !s.deletedSaved.isEmpty

/-- The number of unsaved changes (new, changed and deleted marks). -/
def Store.pending (s : Store) : Nat :=
  s.unsaved.length + s.changedSaved.length + s.deletedSaved.length

/-- The store of the marks read back from a file (task 9.5c): each restored with its own id
(`restore`, later duplicates of an id replace earlier ones), all of them saved. -/
def Store.load (ms : List Mark) : Store :=
  let s := ms.foldl Store.restore {}
  { s with saved := (s.marks.map (·.id)).toList, base := s.marks.toList }

/-- The note of page `page` anchored to exactly the quads `qs` (the comment of a highlight
over `qs`, task 9.8), the newest first. -/
def Store.noteOn (s : Store) (page : Nat) (qs : List Box) : Option Nat :=
  ((s.marks.filter (·.page == page)).toList.reverse.find? fun m =>
    match m.kind with
    | .note _ (.quads qs') => qs' == qs
    | _ => false).map (·.id)

/-- Removes the mark `id` (nothing when absent). -/
def Store.remove (s : Store) (id : Nat) : Store :=
  { s with marks := s.marks.filter (·.id != id) }

/-- The comment of highlight `h` (task 9.5g): the newest note on its page anchored to exactly
its quads (`noteOn`), when its text is not empty. Save writes it into the highlight
(`/Contents` + `/Popup`, as pdf.js). -/
def Store.commentOf (s : Store) (h : Mark) : Option Mark :=
  if h.isNote || h.quads.isEmpty then none
  else
    match (s.noteOn h.page h.quads).bind s.find? with
    | some n => if n.text.isEmpty then none else some n
    | none => none

/-- Whether note `m` is the comment of a highlight of the store (`commentOf`). -/
def Store.isComment (s : Store) (m : Mark) : Bool :=
  m.isNote && s.marks.any fun h => !h.isNote && h.page == m.page &&
    ((s.commentOf h).map (·.id)) == some m.id

/-- Removes mark `id` and, for a highlight, its comment (`noteOn`; task 9.5g: deleting a
highlight deletes its comment note / popup). -/
def Store.removeWithComment (s : Store) (id : Nat) : Store :=
  match s.find? id with
  | some m =>
    if m.isNote || m.quads.isEmpty then s.remove id
    else
      match s.noteOn m.page m.quads with
      | some n => (s.remove id).remove n
      | none => s.remove id
  | none => s

/-- Changes the colour of mark `id`. -/
def Store.recolor (s : Store) (id : Nat) (c : Color) : Store :=
  { s with marks := s.marks.map fun m => if m.id == id then { m with color := c } else m }

/-- Replaces the text of note or free text `id` (other marks are left alone). -/
def Store.setText (s : Store) (id : Nat) (t : String) : Store :=
  { s with marks := s.marks.map fun m =>
      if m.id == id then
        match m.kind with
        | .note _ a => { m with kind := .note t a }
        | .freeText _ p z c => { m with kind := .freeText t p z c }
        | _ => m
      else m }

/-- Changes mark `id` with `f` on its kind. -/
def Store.mapKind (s : Store) (id : Nat) (f : Kind → Kind) : Store :=
  { s with marks := s.marks.map fun m => if m.id == id then { m with kind := f m.kind } else m }

/-- Sets the colour of free text or ink `id`. -/
def Store.setRgb (s : Store) (id : Nat) (c : Rgb) : Store :=
  s.mapKind id fun
    | .freeText t p z _ => .freeText t p z c
    | .ink ss w o _ => .ink ss w o c
    | k => k

/-- Sets the font size of free text `id`, or the thickness of ink `id`. -/
def Store.setSize (s : Store) (id : Nat) (n : Nat) : Store :=
  s.mapKind id fun
    | .freeText t p _ c => .freeText t p n c
    | .ink ss _ o c => .ink ss n o c
    | k => k

/-- Sets the opacity (percent) of ink `id`. -/
def Store.setOpacity (s : Store) (id : Nat) (o : Nat) : Store :=
  s.mapKind id fun
    | .ink ss w _ c => .ink ss w o c
    | k => k

/-- Appends a stroke to ink `id` (task 9.9: the strokes of one drawing session form one
mark). -/
def Store.addStroke (s : Store) (id : Nat) (st : List Pt) : Store :=
  s.mapKind id fun
    | .ink ss w o c => .ink (ss ++ [st]) w o c
    | k => k

/-- Moves free text or ink `id` by `(dx, dy)` page units. -/
def Store.translate (s : Store) (id : Nat) (dx dy : Rat) : Store :=
  let mv (p : Pt) : Pt := ⟨p.x + dx, p.y + dy⟩
  s.mapKind id fun
    | .freeText t p z c => .freeText t (mv p) z c
    | .ink ss w o c => .ink (ss.map (·.map mv)) w o c
    | k => k

/-- The marks of page `p`, oldest first. -/
def Store.onPage (s : Store) (p : Nat) : List Mark :=
  (s.marks.filter (·.page == p)).toList

/-- Whether box `b` contains the point `p` (borders included). -/
def Box.contains (b : Box) (p : Pt) : Bool :=
  decide (b.llx ≤ p.x) && decide (p.x ≤ b.urx) && decide (b.lly ≤ p.y) && decide (p.y ≤ b.ury)

/-- The topmost mark of page `page` under the page point `pt` (page box `pb` for note icons):
note icons first (they are drawn above the highlights), then quads, later marks before
earlier ones; on the quads of a highlight with a comment (a note anchored to the same quads)
the highlight. -/
def Store.hitAt (s : Store) (pb : Box) (page : Nat) (pt : Pt) : Option Nat :=
  let ms := (s.onPage page).reverse
  let icon := ms.find? fun m =>
    (m.iconBox pb).any (Box.contains · pt) || m.box.any (Box.contains · pt)
  let quad := ms.find? fun m => m.quads.any (Box.contains · pt)
  -- On the quads of a commented highlight (a note anchored to exactly its quads, task 9.8)
  -- the highlight wins; the comment is reached through its icon.
  let quad := quad.map fun m =>
    if m.isNote then (ms.find? fun h => !h.isNote && h.quads == m.quads).getD m else m
  (icon <|> quad).map (·.id)

/-! ## Pixels -/

/-- `a · b / 255`, rounded (the multiply blend of two bytes). -/
def mul8 (a b : Nat) : UInt8 :=
  UInt8.ofNat ((a * b + 127) / 255)

/-- Byte `i` of `d` multiplied by `c` (`mul8`); `d` unchanged when `i` is out of range. -/
def mulAt (d : ByteArray) (i c : Nat) : ByteArray :=
  if h : i < d.size then d.set i (mul8 (d.get i h).toNat c) h else d

/-- Multiplies the pixels of `[x0, x1) × [y0, y1)` of an RGBA image of width `w` with the
colour `(r, g, b)` (alpha kept); columns at or beyond `w` and bytes outside the data are
skipped. -/
def multiplyRect (data : ByteArray) (w : Nat) (x0 y0 x1 y1 : Nat) (rgb : Nat × Nat × Nat) :
    ByteArray := Id.run do
  let (r, g, b) := rgb
  let mut d := data
  for y in [y0:y1] do
    for x in [x0:min x1 w] do
      let i := 4 * (y * w + x)
      d := mulAt (mulAt (mulAt d i r) (i + 1) g) (i + 2) b
  return d

/-- The pixel rectangle `(x0, y0, x1, y1)` (end exclusive, clipped to `w × h`) that a
page-space box covers on an image drawn at zoom `z`, rotation `rot` of page box `pb`
(`Geom.toScreen`, C2): the pixels whose centres lie in the box. `none` when empty. -/
def pixelRect (z : Rat) (rot : Doc.Rotation) (pb : Box) (w h : Nat) (b : Box) :
    Option (Nat × Nat × Nat × Nat) :=
  let p0 := toScreen z rot pb ⟨b.llx, b.lly⟩
  let p1 := toScreen z rot pb ⟨b.urx, b.ury⟩
  let cl (v : Rat) (n : Nat) : Nat := min n ((v + 1 / 2).floor.toNat)
  let x0 := cl (min p0.x p1.x) w
  let x1 := cl (max p0.x p1.x) w
  let y0 := cl (min p0.y p1.y) h
  let y1 := cl (max p0.y p1.y) h
  if x0 < x1 && y0 < y1 then some (x0, y0, x1, y1) else none

/-- The page image with the highlights of `ms` multiplied in (notes are canvas items, not
pixels). -/
def composite (z : Rat) (rot : Doc.Rotation) (pb : Box) (w h : Nat) (data : ByteArray)
    (ms : List Mark) : ByteArray :=
  ms.foldl (fun d m =>
    match m.kind with
    | .highlight qs => qs.foldl (fun d q =>
        match pixelRect z rot pb w h q with
        | some (x0, y0, x1, y1) => multiplyRect d w x0 y0 x1 y1 m.color.rgb
        | none => d) d
    | _ => d) data

/-! ## Checks -/

private def pb : Box := ⟨0, 0, 612, 792⟩

private def q1 : Box := ⟨100, 698, 166, 708⟩
private def q2 : Box := ⟨100, 686, 111, 696⟩

private def sample : Store :=
  let s : Store := {}
  let (s, _) := (s.addHighlight 0 .yellow [q1, q2]).getD (s, 0)
  let (s, _) := s.addNote 0 .yellow "hello" (.point ⟨300, 400⟩)
  let (s, _) := (s.addHighlight 1 .green [q2]).getD (s, 0)
  let (s, _) := s.addNote 0 .blue "on text" (.quads [q2])
  s

#guard sample.marks.map (·.id) == #[1, 2, 3, 4] && sample.nextId == 5
#guard (sample.onPage 0).map (·.id) == [1, 2, 4] && (sample.onPage 1).map (·.id) == [3]
#guard ({} : Store).addHighlight 0 .red [] |>.isNone
-- Ids are never reused: removing the newest mark and adding again gives a fresh id.
#guard ((sample.remove 4).add 0 .red (.highlight [q1])).2 == 5
#guard (sample.remove 2).marks.map (·.id) == #[1, 3, 4]
#guard (sample.remove 9).marks.size == 4
-- Recolour and edit.
#guard ((sample.recolor 1 .pink).find? 1).map (·.color) == some .pink
#guard ((sample.recolor 1 .pink).find? 3).map (·.color) == some .green
#guard ((sample.setText 2 "new [text] $x").find? 2).map (·.text) == some "new [text] $x"
#guard ((sample.setText 1 "ignored").find? 1).map (·.isNote) == some false
-- Restoring a mark keeps its id and moves `nextId` past it.
#guard let s := sample.restore ⟨40, 0, .red, .highlight [q1]⟩
  s.nextId == 41 && s.marks.size == 5 && (s.add 0 .red (.note "" (.point ⟨0, 0⟩))).2 == 41
#guard (sample.restore ⟨1, 0, .red, .highlight [q2]⟩).marks.size == 4
-- Loaded marks are saved; new ones are not; ids continue after the loaded ones.
#guard let s := Store.load [⟨7, 0, .red, .highlight [q1]⟩, ⟨3, 1, .blue, .highlight [q2]⟩]
  !s.dirty && s.nextId == 8 && s.isSaved 3 && s.isSaved 7 &&
  let (s', id) := s.add 0 .yellow (.note "x" (.point ⟨0, 0⟩))
  id == 8 && s'.dirty && (s'.unsaved.map (·.id)) == [8] && s'.isSaved 7
#guard (Store.load [⟨2, 0, .red, .highlight [q1]⟩, ⟨2, 0, .green, .highlight [q1]⟩]).marks.size == 1
#guard sample.dirty && sample.unsaved.length == 4 && !({} : Store).dirty
-- Edits of saved marks make the store dirty (9.5g); undoing them makes it clean again.
#guard let s := Store.load [⟨7, 0, .red, .highlight [q1]⟩, ⟨3, 0, .blue, .note "x" (.quads [q1])⟩]
  !s.dirty && (s.recolor 7 .green).dirty && !((s.recolor 7 .green).recolor 7 .red).dirty &&
  (s.setText 3 "y").dirty && (s.setText 3 "y").pending == 1 &&
  (s.remove 3).deletedSaved == [3] && (s.removeWithComment 7).marks.size == 0 &&
  (s.removeWithComment 7).pending == 2
-- The comment of a highlight: the note on its quads with a text.
#guard let s := Store.load [⟨7, 0, .red, .highlight [q1]⟩, ⟨3, 0, .blue, .note "x" (.quads [q1])⟩]
  ((s.find? 7).bind s.commentOf |>.map (·.id)) == some 3 &&
  ((s.find? 3).map s.isComment) == some true &&
  (((s.setText 3 "").find? 7).bind (s.setText 3 "").commentOf).isNone
-- `/NM` names.
#guard ((sample.find? 3).map Mark.nm) == some "safepdf-mark-3"
#guard idOfNm "safepdf-mark-17" == some 17 && idOfNm "other-17" == none &&
  idOfNm "safepdf-mark-" == none
-- Quad points: upper-left, upper-right, lower-left, lower-right.
#guard ((sample.find? 1).map Mark.quadPoints) ==
  some [100, 708, 166, 708, 100, 698, 166, 698, 100, 696, 111, 696, 100, 686, 111, 686]
#guard ((sample.find? 1).bind (Mark.rect pb)) == some ⟨100, 686, 166, 708⟩
-- Note icons: at the point, right of the first quad, kept inside the page.
#guard ((sample.find? 2).bind (Mark.iconBox pb)) == some ⟨300, 380, 320, 400⟩
#guard ((sample.find? 4).bind (Mark.iconBox pb)) == some ⟨111, 676, 131, 696⟩
#guard (Mark.iconBox pb ⟨9, 0, .yellow, .note "" (.point ⟨605, 5⟩)⟩) == some ⟨592, 0, 612, 20⟩
#guard ((sample.find? 1).bind (Mark.iconBox pb)).isNone
-- The comment of a highlight: the note anchored to the same quads, on the same page.
#guard sample.noteOn 0 [q2] == some 4 && sample.noteOn 1 [q2] == none &&
  sample.noteOn 0 [q1, q2] == none
-- Hit-testing: icons above highlights, later marks above earlier ones, the right page only.
#guard sample.hitAt pb 0 ⟨310, 390⟩ == some 2
#guard sample.hitAt pb 0 ⟨150, 700⟩ == some 1
#guard sample.hitAt pb 0 ⟨105, 690⟩ == some 4
#guard sample.hitAt pb 0 ⟨115, 680⟩ == some 4
#guard sample.hitAt pb 1 ⟨105, 690⟩ == some 3
#guard sample.hitAt pb 0 ⟨500, 100⟩ == none
-- A highlight's comment (same quads) does not hide the highlight; its icon selects it.
#guard let s := (sample.addNote 1 .green "comment" (.quads [q2])).1
  s.hitAt pb 1 ⟨105, 690⟩ == some 3 && s.hitAt pb 1 ⟨120, 690⟩ == some 5
-- Free text and ink (task 9.9): boxes from the Core layout, hit above highlights, edits.
private def ed : Store :=
  let (s, _) := sample.add 0 .yellow (.freeText "Hi" ⟨100, 710⟩ 12 (255, 0, 0))
  let (s, _) := s.add 0 .yellow (.ink [[⟨400, 400⟩, ⟨420, 430⟩]] 2 100 (0, 0, 255))
  s

private def ftKind (t : String) (sz : Nat) (c : Rgb) : Kind := .freeText t ⟨100, 710⟩ sz c

#guard ((ed.find? 6).bind Mark.box) == some ⟨398, 398, 422, 432⟩
#guard ed.hitAt pb 0 ⟨105, 700⟩ == some 5 && ed.hitAt pb 0 ⟨410, 410⟩ == some 6
#guard ((ed.find? 5).map Mark.hex) == some "#FF0000" && ((ed.find? 6).map Mark.text) == some ""
#guard ((((ed.setText 5 "Bye").setRgb 5 (0, 0, 0)).setSize 5 20).find? 5).map
  (·.kind.same (ftKind "Bye" 20 (0, 0, 0))) == some true
#guard (((ed.translate 6 10 (-5)).addStroke 6 [⟨1, 1⟩]).find? 6).map (·.kind.same
  (.ink [[⟨410, 395⟩, ⟨430, 425⟩], [⟨1, 1⟩]] 2 100 (0, 0, 255))) == some true
#guard ((ed.setOpacity 6 50).find? 6).map
  (·.kind.same (.ink [[⟨400, 400⟩, ⟨420, 430⟩]] 2 50 (0, 0, 255))) == some true
#guard let s := Store.load [⟨7, 0, .yellow, .freeText "x" ⟨1, 2⟩ 10 (0, 0, 0)⟩]
  !s.dirty && (s.translate 7 1 0).dirty && (s.setSize 7 11).dirty && !(s.setOpacity 7 3).dirty
-- Multiply: white takes the colour, black stays black, alpha is kept.
#guard mul8 255 0x98 == 0x98 && mul8 0 0xFF == 0 && mul8 128 128 == 64
#guard (multiplyRect (ByteArray.mk #[255, 255, 255, 255, 0, 0, 0, 255]) 2 0 0 2 1
  Color.green.rgb).toList == [0x53, 0xFF, 0xBC, 255, 0, 0, 0, 255]
#guard (multiplyRect (ByteArray.mk #[255, 255, 255, 255, 255, 255, 255, 255]) 2 1 0 2 1
  Color.yellow.rgb).toList == [255, 255, 255, 255, 255, 255, 0x98, 255]
-- Out-of-range rectangles are clipped.
#guard (multiplyRect (ByteArray.mk #[255, 255, 255, 255]) 1 0 0 5 5 Color.red.rgb).toList ==
  [0xFF, 0x4F, 0x5F, 255]
-- Pixel rectangles at zoom 1 (y flipped about the page box) and zoom 2, rotated 90°.
#guard pixelRect 1 .r0 pb 612 792 q1 == some (100, 84, 166, 94)
#guard pixelRect 2 .r0 pb 1224 1584 q1 == some (200, 168, 332, 188)
#guard (pixelRect 1 .r90 pb 792 612 q1).map (fun (x0, y0, x1, y1) => (x1 - x0, y1 - y0)) ==
  some (10, 66)
#guard pixelRect 1 .r0 pb 612 792 ⟨700, 0, 800, 10⟩ == none

end SafePdf.Shell.App.Marks
