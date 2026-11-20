import SafePdf.Core.Raster.Geom

/-!
# User marks: highlights and notes (task 9.4; Plan.md §6 Phase 9 "User highlights in colors", "Notes", "Persistence — annotations inside the PDF", §10 `SafePdf/Shell/`)

The Tk-free model of the marks a reader adds to a document (unverified shell code, total,
checked by `#guard`s and small theorems). Marks live in memory in this task; task 9.5b turns
each one into an annotation dictionary (`/Highlight` with `/QuadPoints`, `/Text` with
`/Contents`) for `Core.Write.Incremental.writeAnnots`, task 9.5c saves and reloads them.

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
  the ids of marks read back from a file (9.5c). Operations: add, remove, recolour, edit the
  text, find, the marks of a page, hit-testing (`Store.hitAt`: the topmost mark whose icon
  or quads contain a page point; icons are above highlights).
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

/-- The kind of a mark. -/
inductive Kind where
  /-- A highlight over `quads` (page space, one per line run). -/
  | highlight (quads : List Box)
  /-- A note with its text and anchor. -/
  | note (text : String) (anchor : Anchor)
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
  | .highlight _ => false

/-- The note text (empty for a highlight). -/
def Mark.text (m : Mark) : String :=
  match m.kind with
  | .note t _ => t
  | .highlight _ => ""

/-- The quads of a mark (none for a note at a point). -/
def Mark.quads (m : Mark) : List Box :=
  match m.kind with
  | .highlight qs => qs
  | .note _ (.quads qs) => qs
  | .note _ (.point _) => []

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
  | .highlight _ => none
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

/-! ## Store -/

/-- The marks of one document: creation order (later marks are drawn on top) and the next
fresh id. -/
structure Store where
  /-- Marks, oldest first. -/
  marks : Array Mark := #[]
  /-- The id the next mark gets (larger than every id in `marks`). -/
  nextId : Nat := 1
  deriving Inhabited

/-- Adds a mark of `kind` on `page` in `color`; returns the store and the new mark's id. -/
def Store.add (s : Store) (page : Nat) (color : Color) (kind : Kind) : Store × Nat :=
  ({ marks := s.marks.push ⟨s.nextId, page, color, kind⟩, nextId := s.nextId + 1 }, s.nextId)

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
  { marks := (s.marks.filter (·.id != m.id)).push m, nextId := max s.nextId (m.id + 1) }

/-- The mark with id `id`. -/
def Store.find? (s : Store) (id : Nat) : Option Mark :=
  s.marks.find? (·.id == id)

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

/-- Changes the colour of mark `id`. -/
def Store.recolor (s : Store) (id : Nat) (c : Color) : Store :=
  { s with marks := s.marks.map fun m => if m.id == id then { m with color := c } else m }

/-- Replaces the text of note `id` (highlights are left alone). -/
def Store.setText (s : Store) (id : Nat) (t : String) : Store :=
  { s with marks := s.marks.map fun m =>
      if m.id == id then
        match m.kind with
        | .note _ a => { m with kind := .note t a }
        | .highlight _ => m
      else m }

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
  let icon := ms.find? fun m => (m.iconBox pb).any (Box.contains · pt)
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
    | .note .. => d) data

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
