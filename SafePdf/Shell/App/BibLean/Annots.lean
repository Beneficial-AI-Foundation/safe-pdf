import SafePdf.Shell.App.Marks
import SafePdf.Shell.App.Select
import SafePdf.Shell.App.Save
import SafePdf.Shell.App.BibLean.Launch

/-!
# Annotations both ways with bib-lean (task 10.2; Plan.md §6 Phase 10 "Annotations both ways")

The viewer's half of the annotation routes of bib-lean's reader contract
(`bib-lean/docs/READER-CONTRACT.md` §3–§4): the stored annotation set is loaded into the
marks model (`Marks.Store`), the whole set is posted back as the contract's **neutral JSON**
after each change and on exit, and the annotated file (the Phase 9 writer's output,
`Save.build`) is sent with `PUT /api/attachments/{key}/file`. Unverified shell code; the
conversions are pure, total and checked by `#guard`s, the `IO` part (`Sync`) only schedules
requests and never blocks or fails the viewer.

**Load** (`neutralOfStored`, `mergeStored`). `GET /api/items/{key}` lists the annotation
children in bib-lean's stored form, `{"itemType": "annotation", "annotation": {kind,
pageIndex, position, text, comment, color, sortIndex}}`; `position` is the compact JSON
`{"extra", "id", "kind", "rects"}` the server built from the neutral element (contract
§4.3), so the neutral element is recovered exactly (numbers are kept as their text).
Then each element is either

* **ours** — `id` is a mark's `/NM` (`safepdf-mark-N`, `Marks.idOfNm`), kind `highlight` or
  `note`, every rectangle four numbers: it becomes mark `N` (`ownMark?`), restored with its own
  id (`Marks.Store.restore`) unless the store already holds mark `N` (read back from the PDF's
  own `/Annots`, which wins); a restored mark is *unsaved* (it is in the library, not yet in
  the file). A highlight's `comment` becomes a note anchored to the highlight's quads (the
  viewer's form of a comment, task 9.8); a note's `extra.quads` (if any) is its anchor, else the
  upper-left corner of its rectangle; the colour is the palette colour nearest to `#rrggbb`
  (`colorOfHex`; the marks model only has PDF.js's five colours);
* **somebody else's** (pdf.js's `"12R"` ids, no id, another kind, anything not convertible) —
  kept **verbatim** (`passthrough`) and posted back unchanged every time. The set replaces the
  previous one (contract A2), so dropping them would delete them from the library; kept,
  their item keys stay. They are not shown as marks: pdf.js's ones are annotations inside the
  file, which the renderer already draws, and a second copy would be written on Save.

**Send** (`neutralsOf`, `bodyOf`). Every mark becomes one element (`neutralOfMark`): `id` its
`/NM` (stable, so bib-lean keeps its item key, contract §4.2), `kind` `highlight` or `note`,
`pageIndex`, `rects` (a highlight's quads; a note's icon box, `Mark.iconBox` in the page's
CropBox), `text` (a highlight's: the page text under its quads, `textUnder`, from the same
glyph cells as the selection, `Select.cellsOf`), `comment` (a note's text; a highlight's: the
newest note anchored to exactly its quads, `Store.noteOn`, which is then not sent on its own),
`color` (`#rrggbb`, lower case), `sortIndex` and `extra` (a note anchored to quads:
`{"quads": [...]}`; otherwise `null`). Numbers are written with at most three decimals
(`fmtNum`; the writer rounds to 1/1000 too), so a loaded set is sent back unchanged.
`sortIndex` is computed as the stock viewer (`web/reader.js` `annotationsOfPdf`):
`PPPPP|OOOOOO|TTTTT` = page, the character offset of the marked text in the page text (0 for
notes) and `top − max y` of the rectangles with `top` the CropBox's upper edge, each floored
at 0 and zero-padded; elements are sorted by it (stably), the pass-through ones follow.

**Free text and ink** (task 9.9): the contract has the kinds `text` and `ink` (§4.1, the
stock viewer maps pdf.js's `FreeText` and `Ink` onto them), so they are sent too: free text as
`kind` `text` with `rects` its box (`Mark.box`), `text` the typed text, `comment` `null`,
`color` its own colour and `extra` `{"fontSize": N}`; ink as `kind` `ink` with `rects` its
box, `text`/`comment` `null`, its colour and `extra` `{"inkList": [[x1, y1, x2, y2, …], …],
"width": W, "opacity": O}` (one array per stroke; opacity in percent). Loading reads them back
(`ownMark?`): the box's upper-left corner is the free text's position; without a usable
`extra` the size is 10 and an ink element is passed through.

**Coordinates.** The contract's rectangles are in PDF user space (points, origin bottom-left,
before `/Rotate`), the space `Marks` quads live in (`Geom.toScreen` applies the CropBox
origin and the rotation only on the way to the screen), so rectangles and quads are the same
numbers (`boxOfRect`/`rectOf`, normalised so `x0 ≤ x1`, `y0 ≤ y1`): neither the page's
`/Rotate` nor a CropBox offset changes them (`#guard`s below); the CropBox only places note
icons and gives `top`.

**When** (`Sync`). `Sync.onMarksChanged` records the newest store and wakes one background
worker (a dedicated thread); the worker waits until no change came for `debounceMs` (400 ms,
as the stock viewer), then posts the body — only when it differs from the last one the server
accepted. `Sync.onSaved` queues the annotated bytes; the worker sends them with `PUT` before
the next post (the stock viewer's order: the file, then the set). `Sync.flush` (on exit) skips
the wait and gives the worker at most a grace period. Every failure (status, refused or
dropped connection, time limit) goes to stderr as `viewer --biblean: METHOD PATH: …` — the
method, the path (the key only) and the status, never the token or a body — and is otherwise
ignored: viewing never depends on the server.

**Viewer hooks** (wired into the window by task 10.1b, `Main.lean` `windowInit`, as
`Viewer.Library`): `Sync.create` + `Sync.load` (`loadInitial`: the store to show at open,
from the marks read back from the PDF; its `nextId` is above every stored id, so a new mark
never takes the id of a stored one), then `Sync.onMarksChanged` after every change of the
viewer's store, `Sync.onSaved` with `Save.build`'s bytes instead of writing a file (Save to
library), and `Sync.flush` on Close and after the window closed.
-/

namespace SafePdf.Shell.App.BibLean.Annots

open SafePdf.Core
open SafePdf.Core.Raster.Geom (Pt Box)
open SafePdf.Shell.App.Marks (Mark Color Store Anchor)
open SafePdf.Shell.App.BibLean.Http (JVal)

/-! ## Numbers -/

/-- Parses a JSON number (`-? digits (. digits)? ([eE] [+-]? digits)?`) exactly as a
rational; at most 40 mantissa digits and exponents up to ±40, else `none`. -/
def parseNum? (s : String) : Option Rat := do
  let cs := s.toList
  let (neg, cs) := match cs with
    | '-' :: r => (true, r)
    | r => (false, r)
  let ip := cs.takeWhile Char.isDigit
  let cs := cs.drop ip.length
  let (fp, cs) := match cs with
    | '.' :: r => (r.takeWhile Char.isDigit, r.drop (r.takeWhile Char.isDigit).length)
    | r => ([], r)
  if ip.isEmpty && fp.isEmpty then none
  if ip.length + fp.length > 40 then none
  let (e, rest) ← match cs with
    | c :: r =>
      if c == 'e' || c == 'E' then
        let (en, r) := match r with
          | '-' :: r => (true, r)
          | '+' :: r => (false, r)
          | r => (false, r)
        let ds := r.takeWhile Char.isDigit
        match (String.ofList ds).toNat? with
        | some n => if ds.isEmpty || n > 40 then none
                    else some ((if en then -(n : Int) else (n : Int)), r.drop ds.length)
        | none => none
      else some (0, c :: r)
    | [] => some (0, [])
  unless rest.isEmpty do none
  let m : Nat := ((String.ofList (ip ++ fp)).toNat?).getD 0
  let v : Rat := (m : Rat) / ((10 ^ fp.length : Nat) : Rat)
  let v := if e ≥ 0 then v * ((10 ^ e.toNat : Nat) : Rat) else v / ((10 ^ (-e).toNat : Nat) : Rat)
  return if neg then -v else v

#guard parseNum? "100" == some 100 && parseNum? "-0.5" == some (-1 / 2)
#guard parseNum? "1.25e2" == some 125 && parseNum? "125E-2" == some (5 / 4)
#guard parseNum? "." == none && parseNum? "1x" == none && parseNum? "" == none
#guard parseNum? "1e999" == none && parseNum? ".5" == some (1 / 2)

/-- `x` rounded to 1/1000 (halves away from zero) as a JSON number: no exponent, no
trailing zeros, no `-0`. -/
def fmtNum (x : Rat) : String :=
  let a := if x < 0 then -x else x
  let n := (a * 1000 + 1 / 2).floor.toNat
  let ip := n / 1000
  let fp := n % 1000
  let fs := (Save.pad 3 fp).toList.reverse.dropWhile (· == '0') |>.reverse
  let body := toString ip ++ (if fs.isEmpty then "" else "." ++ String.ofList fs)
  if x < 0 && n != 0 then "-" ++ body else body

#guard fmtNum 100 == "100" && fmtNum (1 / 3) == "0.333" && fmtNum (-1 / 2) == "-0.5"
#guard fmtNum (2 / 3) == "0.667" && fmtNum (-1 / 10000) == "0" && fmtNum (12345 / 1000) == "12.345"
#guard fmtNum (5 / 10000) == "0.001" && fmtNum (1999999 / 1000000) == "2"
-- Printing what was parsed from our own output gives the same text.
#guard ["100", "0.333", "-0.5", "612", "698.4", "0"].all fun s => (parseNum? s).map fmtNum == some s

/-! ## JSON output -/

/-- A JSON string literal (`Text.jsonString`). -/
def jstr (s : String) : String := Text.jsonString s

/-- A JSON value as compact text (numbers as kept, members in order). Nesting deeper than
`fuel` is written as `null` (parsed values are at most `Http.maxDepth` deep). -/
def render : Nat → JVal → String
  | 0, _ => "null"
  | _ + 1, .null => "null"
  | _ + 1, .bool b => if b then "true" else "false"
  | _ + 1, .num t => t
  | _ + 1, .str s => jstr s
  | f + 1, .arr xs => "[" ++ ",".intercalate (xs.toList.map (render f)) ++ "]"
  | f + 1, .obj kvs =>
    "{" ++ ",".intercalate (kvs.toList.map fun (k, v) => jstr k ++ ":" ++ render f v) ++ "}"

/-- `render` with enough fuel for every parsed value. -/
def jtext (v : JVal) : String := render (Http.maxDepth + 2) v

#guard jtext (JVal.obj #[("a", .arr #[.num "1.50", .null, .bool true]), ("b", .str "x\"")]) ==
  "{\"a\":[1.50,null,true],\"b\":\"x\\\"\"}"

/-- An optional string as JSON (`null` for `none`). -/
def optStr : Option String → String
  | some s => jstr s
  | none => "null"

/-! ## Rectangles and colours -/

/-- The page-space box of a contract rectangle `[x0, y0, x1, y1]` (normalised). -/
def boxOfRect (v : JVal) : Option Box :=
  match v with
  | .arr #[.num a, .num b, .num c, .num d] => do
    let (x0, y0, x1, y1) := (← parseNum? a, ← parseNum? b, ← parseNum? c, ← parseNum? d)
    some ⟨min x0 x1, min y0 y1, max x0 x1, max y0 y1⟩
  | _ => none

/-- The contract rectangle of a page-space box. -/
def rectOf (b : Box) : String :=
  s!"[{fmtNum b.llx},{fmtNum b.lly},{fmtNum b.urx},{fmtNum b.ury}]"

/-- A list of boxes as a JSON array of rectangles. -/
def rectsText (bs : List Box) : String := "[" ++ ",".intercalate (bs.map rectOf) ++ "]"

/-- All rectangles of a JSON array, `none` if one is not four numbers. -/
def boxesOf (v : JVal) : Option (List Box) :=
  match v with
  | .arr xs => xs.toList.mapM boxOfRect
  | _ => none

#guard boxesOf (.arr #[.arr #[.num "166", .num "708", .num "100", .num "698"]]) ==
  some [⟨100, 698, 166, 708⟩]
#guard boxesOf (.arr #[.arr #[.num "1", .num "2", .num "3"]]) == none

/-- Lower-case `#rrggbb` of a palette colour. -/
def hexOf (c : Color) : String := (c.hex.toList.map Char.toLower) |> String.ofList

/-- The value of a hex digit. -/
def hexDigit? (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c.toLower && c.toLower ≤ 'f' then some (c.toLower.toNat - 'a'.toNat + 10)
  else none

/-- The palette colour nearest to `#rrggbb` (`Save.nearestColor`); yellow for anything else
(the contract's default, `#ffd400`, is nearest to yellow too). -/
def colorOfHex (s : String) : Color :=
  match s.toList with
  | ['#', r1, r2, g1, g2, b1, b2] =>
    let byte (h l : Char) : Option Rat := do
      return (((← hexDigit? h) * 16 + (← hexDigit? l) : Nat) : Rat) / 255
    match byte r1 r2, byte g1 g2, byte b1 b2 with
    | some r, some g, some b => Save.nearestColor [r, g, b]
    | _, _, _ => .yellow
  | _ => .yellow

#guard Color.all.all fun c => colorOfHex (hexOf c) == c && colorOfHex c.hex == c
#guard colorOfHex "#ffd400" == .yellow && colorOfHex "#ff0000" == .red &&
  colorOfHex "red" == .yellow
#guard hexOf .green == "#53ffbc"

/-- The RGB bytes of `#rrggbb` (black when malformed). -/
def rgbOfHex (s : String) : Marks.Rgb :=
  match s.toList with
  | ['#', r1, r2, g1, g2, b1, b2] =>
    let byte (h l : Char) : Option Nat := return (← hexDigit? h) * 16 + (← hexDigit? l)
    match byte r1 r2, byte g1 g2, byte b1 b2 with
    | some r, some g, some b => (r, g, b)
    | _, _, _ => (0, 0, 0)
  | _ => (0, 0, 0)

#guard rgbOfHex "#0060df" == (0, 96, 223) && rgbOfHex "red" == (0, 0, 0)

/-- The colour of a mark as the contract writes it (`#rrggbb`, lower case). -/
def markHex (m : Mark) : String := (m.hex.toList.map Char.toLower) |> String.ofList

/-! ## Page text under quads and the sort key -/

/-- What the conversion needs of a page: its CropBox (note icons, `top`) and its glyph cells
in reading order (`Select.cellsOf`, as the viewer's selection). -/
structure PageInfo where
  /-- The CropBox in page (user) space. -/
  box : Box
  /-- Glyph cells in reading order. -/
  cells : Array Select.Cell := #[]
  deriving Inhabited

/-- Whether a glyph box lies under a quad: its horizontal centre inside the quad and the
vertical overlap at least half the smaller height (as `reader.js`'s `textUnder`). -/
def under (q c : Box) : Bool :=
  let cx := (c.llx + c.urx) / 2
  let vo := min q.ury c.ury - max q.lly c.lly
  decide (q.llx ≤ cx) && decide (cx ≤ q.urx) && decide (vo > 0) &&
    decide (2 * vo ≥ min (q.ury - q.lly) (c.ury - c.lly))

/-- Whitespace runs collapsed to one space, trimmed. -/
def collapse (s : String) : String :=
  let ws := s.split (fun c => c.isWhitespace) |>.toList.map (·.toString) |>.filter (!·.isEmpty)
  " ".intercalate ws

#guard collapse "  a \n\n b  c " == "a b c"

/-- The text under `qs` and its character offset in the page text (the cells' `sep`s and
texts, as `Select.fullText`): the covered cells in reading order, joined by their own
separators when adjacent and by a space across a gap, whitespace collapsed; `none` when no
glyph is covered (offset 0). -/
def textUnder (cells : Array Select.Cell) (qs : List Box) : Option String × Nat := Id.run do
  let mut off := 0
  let mut first : Option Nat := none
  let mut prev : Option Nat := none
  let mut out := ""
  for h : i in [0:cells.size] do
    let c := cells[i]
    let sep := if i == 0 then "" else c.sep
    if qs.any (under · c.box) then
      if first.isNone then first := some (off + sep.length)
      out := if prev == some (i - 1) && i > 0 then out ++ sep ++ c.text
             else if out.isEmpty then c.text else out ++ " " ++ c.text
      prev := some i
    off := off + sep.length + c.text.length
  let t := collapse out
  return (if t.isEmpty then none else some t, first.getD 0)

/-- `n` zero-padded to `w` digits (at least). -/
def padN (w n : Nat) : String := Save.pad w n

/-- The sort key `PPPPP|OOOOOO|TTTTT` (see the module doc). -/
def sortIndex (page offset : Nat) (top maxY : Rat) : String :=
  let t := top - maxY
  s!"{padN 5 page}|{padN 6 offset}|{padN 5 (if t < 0 then 0 else t.floor.toNat)}"

#guard sortIndex 3 42 792 (1405 / 2) == "00003|000042|00089"
#guard sortIndex 0 0 100 200 == "00000|000000|00000"

/-! ## Marks → neutral JSON -/

/-- A neutral element as JSON text, members in the contract's order. -/
def element (id : String) (kind : String) (page : Nat) (rects : List Box)
    (text comment : Option String) (color : String) (sortKey : String) (extra : String) :
    String :=
  s!"\{\"id\":{jstr id},\"kind\":{jstr kind},\"pageIndex\":{page},\"rects\":{rectsText rects},\
\"text\":{optStr text},\"comment\":{optStr comment},\"color\":{jstr color},\
\"sortIndex\":{jstr sortKey},\"extra\":{extra}}"

/-- Whether note `m` is the comment of a highlight of the store (anchored to exactly the
quads of a highlight on its page, and the newest such note: `Store.noteOn`). -/
def isComment (s : Store) (m : Mark) : Bool :=
  match m.kind with
  | .note _ (.quads qs) =>
    s.noteOn m.page qs == some m.id &&
      (s.onPage m.page).any fun h => !h.isNote && h.quads == qs
  | _ => false

/-- The neutral element of mark `m` (`none` for a comment note, which travels with its
highlight, or a mark without rectangles), with its sort key. -/
def neutralOfMark (info : Nat → PageInfo) (s : Store) (m : Mark) : Option (String × String) :=
  let pi := info m.page
  let top := pi.box.ury
  match m.kind with
  | .highlight qs =>
    match Marks.unionAll qs with
    | none => none
    | some u =>
      let (text, off) := textUnder pi.cells qs
      let comment := (s.noteOn m.page qs).bind s.find? |>.map Mark.text |>.filter (!·.isEmpty)
      let key := sortIndex m.page off top u.ury
      some (key, element m.nm "highlight" m.page qs text comment (hexOf m.color) key "null")
  | .note t a =>
    if isComment s m then none
    else match m.iconBox pi.box with
      | none => none
      | some ib =>
        let extra := match a with
          | .quads qs => "{\"quads\":" ++ rectsText qs ++ "}"
          | .point _ => "null"
        let key := sortIndex m.page 0 top ib.ury
        some (key, element m.nm "note" m.page [ib] none (some t) (hexOf m.color) key extra)
  | .freeText t _ sz _ =>
    match m.box with
    | none => none
    | some b =>
      let key := sortIndex m.page 0 top b.ury
      some (key, element m.nm "text" m.page [b] (some t) none (markHex m) key
        s!"\{\"fontSize\":{sz}}")
  | .ink ss w o _ =>
    match m.box with
    | none => none
    | some b =>
      let key := sortIndex m.page 0 top b.ury
      let strokes := ss.map fun st =>
        "[" ++ ",".intercalate (st.flatMap fun p => [fmtNum p.x, fmtNum p.y]) ++ "]"
      some (key, element m.nm "ink" m.page [b] none none (markHex m) key
        s!"\{\"inkList\":[{",".intercalate strokes}],\"width\":{w},\"opacity\":{o}}")

/-- The elements of all marks, sorted by sort key (stable: creation order on ties). -/
def neutralsOf (info : Nat → PageInfo) (s : Store) : List String :=
  let xs := s.marks.toList.filterMap (neutralOfMark info s)
  (xs.mergeSort fun a b => decide (a.1 ≤ b.1)).map (·.2)

/-- The `id` of a pass-through element. -/
def idOf? (v : JVal) : Option String := v.get? "id" >>= JVal.str?

/-- **The `POST …/annotations` body**: the marks' elements, then the pass-through elements
verbatim (an element whose `id` a mark already uses is left out, ids stay unique). -/
def bodyOf (info : Nat → PageInfo) (s : Store) (passthrough : Array JVal) : String :=
  let own := neutralsOf info s
  let ids := s.marks.toList.map Mark.nm
  let other := passthrough.toList.filter fun v => match idOf? v with
    | some i => !ids.contains i
    | none => true
  "[" ++ ",".intercalate (own ++ other.map jtext) ++ "]"

/-! ## The stored form → neutral elements → marks -/

/-- Member `k` of an object, `null` when absent. -/
def getD (v : JVal) (k : String) : JVal := (v.get? k).getD .null

/-- The neutral element of one stored child (`children[i]` of `GET /api/items/{key}`), as
JSON members in the contract's order (contract §4.3: `id`, `kind`, `rects`, `extra` from the
parsed `position`, the rest from the annotation; a kind missing from the position is the
stored kind). `none` for a child that is not an annotation. -/
def neutralOfStored (child : JVal) : Option JVal := do
  unless (child.get? "itemType" >>= JVal.str?) == some "annotation" do none
  let a ← child.get? "annotation"
  let pos : JVal := match a.get? "position" >>= JVal.str? with
    | some p => (Http.parseJson p.toUTF8).toOption.getD .null
    | none => .null
  let kind := match pos.get? "kind" with
    | some (.str k) => JVal.str k
    | _ => getD a "kind"
  let rects := match pos.get? "rects" with
    | some (.arr xs) => JVal.arr xs
    | _ => .arr #[]
  some (.obj #[("id", getD pos "id"), ("kind", kind), ("pageIndex", getD a "pageIndex"),
    ("rects", rects), ("text", getD a "text"), ("comment", getD a "comment"),
    ("color", getD a "color"), ("sortIndex", getD a "sortIndex"), ("extra", getD pos "extra")])

/-- The neutral elements of a `GET /api/items/{key}` answer (its annotation children, in
order). -/
def storedOf (detail : JVal) : Array JVal :=
  match detail.get? "children" with
  | some (.arr cs) => cs.filterMap neutralOfStored
  | _ => #[]

/-- One of our marks from a neutral element (see the module doc), with a highlight's
comment; `none` for anything else. -/
def ownMark? (v : JVal) : Option (Mark × Option String) := do
  let id ← Marks.idOfNm (← idOf? v)
  let page ← match v.get? "pageIndex" with
    | some (.num t) => t.toNat?
    | _ => none
  let rects ← boxesOf (getD v "rects")
  let color := colorOfHex ((v.get? "color" >>= JVal.str?).getD "")
  let comment := (v.get? "comment" >>= JVal.str?)
  match v.get? "kind" >>= JVal.str? with
  | some "highlight" =>
    if rects.isEmpty then none
    else some (⟨id, page, color, .highlight rects⟩, comment.filter (!·.isEmpty))
  | some "text" =>
    let r ← rects.head?
    let text := ((v.get? "text" >>= JVal.str?) <|> comment).getD ""
    let size := match (getD v "extra").get? "fontSize" with
      | some (.num n) => ((parseNum? n).map fun q => max 1 (min 1000 ((q + 1 / 2).floor.toNat))).getD 10
      | _ => 10
    some (⟨id, page, .yellow, .freeText text ⟨r.llx, r.ury⟩ size
      (rgbOfHex ((v.get? "color" >>= JVal.str?).getD "#000000"))⟩, none)
  | some "ink" =>
    let ex := getD v "extra"
    let numN (k : String) (d : Nat) : Nat := match ex.get? k with
      | some (.num n) => ((parseNum? n).map fun q => (q + 1 / 2).floor.toNat).getD d
      | _ => d
    let strokes ← match ex.get? "inkList" with
      | some (.arr xs) => xs.toList.mapM fun
          | .arr ns => do
            let qs ← ns.toList.mapM fun | .num t => parseNum? t | _ => none
            some (Save.pointsOf qs)
          | _ => none
      | _ => none
    if strokes.isEmpty || strokes.any List.isEmpty then none
    some (⟨id, page, .yellow, .ink strokes (max 1 (numN "width" 1)) (min 100 (numN "opacity" 100))
      (rgbOfHex ((v.get? "color" >>= JVal.str?).getD "#000000"))⟩, none)
  | some "note" =>
    let text := comment.getD ((v.get? "text" >>= JVal.str?).getD "")
    let quads := (getD v "extra").get? "quads" |>.bind boxesOf |>.getD []
    if !quads.isEmpty then some (⟨id, page, color, .note text (.quads quads)⟩, none)
    else match rects with
      | r :: _ => some (⟨id, page, color, .note text (.point ⟨r.llx, r.ury⟩)⟩, none)
      | [] => none
  | _ => none

/-- **Merges the stored set into the store** (`fileStore`: the marks read back from the PDF):
our elements become marks (a mark already in the store wins; a stored highlight comment the
store lacks is added as a note on its quads), the rest is returned for pass-through. -/
def mergeStored (stored : Array JVal) (fileStore : Store) : Store × Array JVal := Id.run do
  let mut s := fileStore
  let mut other : Array JVal := #[]
  let mut comments : Array (Mark × String) := #[]
  for v in stored do
    match ownMark? v with
    | none => other := other.push v
    | some (m, c) =>
      if (s.find? m.id).isNone then s := s.restore m
      if let some t := c then comments := comments.push (m, t)
  for (m, t) in comments do
    if (s.noteOn m.page m.quads).isNone then
      s := (s.addNote m.page m.color t (.quads m.quads)).1
  return (s, other)

/-! ## Checks -/

private def pb : Box := ⟨0, 0, 612, 792⟩
private def q1 : Box := ⟨100, 698, 166, 708⟩
private def q2 : Box := ⟨100, 686, 111, 696⟩

/-- A cell with text `t` (separator `sep`) over the box `b`. -/
private def cell (t sep : String) (b : Box) : Select.Cell := ⟨t, sep, b, 0⟩

/-- `Hello world` on the line of `q1` (ten units per letter from x = 100), `next` below. -/
private def cells : Array Select.Cell :=
  #[cell "H" "" ⟨100, 698, 110, 708⟩, cell "i" "" ⟨110, 698, 120, 708⟩,
    cell "y" " " ⟨130, 698, 140, 708⟩, cell "o" "" ⟨140, 698, 150, 708⟩,
    cell "u" "" ⟨150, 698, 160, 708⟩, cell "n" "\n" ⟨100, 686, 110, 696⟩]

private def info (_ : Nat) : PageInfo := ⟨pb, cells⟩

#guard textUnder cells [q1] == (some "Hi you", 0)
#guard textUnder cells [⟨128, 698, 166, 708⟩] == (some "you", 3)
#guard textUnder cells [q2] == (some "n", 7)
#guard textUnder cells [⟨100, 698, 125, 708⟩, q2] == (some "Hi n", 0)
#guard textUnder cells [⟨300, 0, 400, 10⟩] == (none, 0)

private def store0 : Store :=
  let s : Store := {}
  let (s, _) := (s.addHighlight 0 .yellow [q1]).getD (s, 0)
  let (s, _) := s.addNote 0 .blue "a note" (.point ⟨300, 400⟩)
  let (s, _) := s.addNote 0 .yellow "my comment" (.quads [q1])
  let (s, _) := s.addNote 1 .green "on text" (.quads [q2])
  s

#guard neutralsOf info store0 ==
  ["{\"id\":\"safepdf-mark-1\",\"kind\":\"highlight\",\"pageIndex\":0,\"rects\":[[100,698,166,708]],\"text\":\"Hi you\",\"comment\":\"my comment\",\"color\":\"#ffff98\",\"sortIndex\":\"00000|000000|00084\",\"extra\":null}",
   "{\"id\":\"safepdf-mark-2\",\"kind\":\"note\",\"pageIndex\":0,\"rects\":[[300,380,320,400]],\"text\":null,\"comment\":\"a note\",\"color\":\"#80ebff\",\"sortIndex\":\"00000|000000|00392\",\"extra\":null}",
   "{\"id\":\"safepdf-mark-4\",\"kind\":\"note\",\"pageIndex\":1,\"rects\":[[111,676,131,696]],\"text\":null,\"comment\":\"on text\",\"color\":\"#53ffbc\",\"sortIndex\":\"00001|000000|00096\",\"extra\":{\"quads\":[[100,686,111,696]]}}"]

/-- `bodyOf` parsed back as neutral elements. -/
private def parsedBody (s : Store) (pt : Array JVal := #[]) : Array JVal :=
  match Http.parseJson (bodyOf info s pt).toUTF8 with
  | .ok (.arr xs) => xs
  | _ => #[]

/-- The marks of a store without the `saved` list, for comparisons. -/
private def sig (s : Store) : List (Nat × Nat × String × List Rat × String × Bool) :=
  s.marks.toList.map fun m => (m.id, m.page, m.color.name, m.quadPoints, m.text, m.isNote)

-- Round trip: the elements of a store load back into the same marks (the comment note 3 comes
-- back as a fresh note 5 on the same quads) and send back the same body.
#guard let (s, other) := mergeStored (parsedBody store0) {}
  other.isEmpty && (sig s).map (·.1) == [1, 2, 4, 5] &&
  ((sig s).map (·.2)).all (((sig store0).map (·.2)).contains ·) &&
  bodyOf info s #[] == bodyOf info store0 #[]
-- Free text and ink (task 9.9): kinds `text` and `ink`, read back into the same marks.
private def storeEd : Store :=
  let (s, _) := ({} : Store).add 0 .yellow (.freeText "Typed ✓" ⟨72.5, 700⟩ 14 (255, 0, 0))
  let (s, _) := s.add 1 .yellow (.ink [[⟨10, 10⟩, ⟨20.25, 30⟩], [⟨5, 5⟩]] 3 40 (0, 96, 223))
  s
#guard neutralsOf info storeEd ==
  ["{\"id\":\"safepdf-mark-1\",\"kind\":\"text\",\"pageIndex\":0,\"rects\":[[72.5,677.1,123.19,700]],\"text\":\"Typed ✓\",\"comment\":null,\"color\":\"#ff0000\",\"sortIndex\":\"00000|000000|00092\",\"extra\":{\"fontSize\":14}}",
   "{\"id\":\"safepdf-mark-2\",\"kind\":\"ink\",\"pageIndex\":1,\"rects\":[[2,2,23.25,33]],\"text\":null,\"comment\":null,\"color\":\"#0060df\",\"sortIndex\":\"00001|000000|00759\",\"extra\":{\"inkList\":[[10,10,20.25,30],[5,5]],\"width\":3,\"opacity\":40}}"]
#guard let (s, other) := mergeStored (parsedBody storeEd) {}
  other.isEmpty && s.marks.size == 2 &&
  (s.marks.toList.zip storeEd.marks.toList).all (fun (a, b) => a.id == b.id && a.kind.same b.kind) &&
  bodyOf info s #[] == bodyOf info storeEd #[]
-- Our own marks read back from the PDF win over the stored elements; the stored-only ones are
-- restored unsaved.
#guard let fileStore := Store.load [⟨1, 0, .red, .highlight [q1]⟩]
  let (s, _) := mergeStored (parsedBody store0) fileStore
  (s.find? 1).map (·.color) == some .red && s.isSaved 1 && !s.isSaved 2 && s.dirty &&
    s.nextId == 6
-- Elements of other viewers pass through verbatim, also with our id kinds they cannot be.
#guard let foreign := JVal.obj #[("id", .str "12R"), ("kind", .str "highlight"),
      ("pageIndex", .num "0"), ("rects", .arr #[.arr #[.num "1.50", .num "2", .num "3", .num "4"]]),
      ("text", .null), ("comment", .null), ("color", .str "#ffd400"),
      ("sortIndex", .str "00000|000000|00000"), ("extra", .obj #[("subtype", .str "Highlight")])]
  let odd := JVal.obj #[("id", .str "safepdf-mark-9"), ("kind", .str "strikeout"),
      ("pageIndex", .num "0"), ("rects", .arr #[])]
  let (s, other) := mergeStored #[foreign, odd] {}
  s.marks.isEmpty && other.size == 2 &&
    bodyOf info {} other == "[" ++ jtext foreign ++ "," ++ jtext odd ++ "]" &&
    ((jtext foreign).splitOn "[1.50,2,3,4]").length == 2
-- A pass-through element whose id a mark uses is not sent twice.
#guard let dup := JVal.obj #[("id", .str "safepdf-mark-1"), ("kind", .str "ink")]
  (parsedBody store0 #[dup]).size == 3
-- The stored form (bib-lean's `GET /api/items/{key}` children) gives back the neutral element.
#guard let child := (Http.parseJson ("{\"key\":\"K2345678\",\"itemType\":\"annotation\",\"annotation\":{\"kind\":\"underline\",\"pageIndex\":2,\"position\":\"{\\\"extra\\\":null,\\\"id\\\":\\\"7R\\\",\\\"kind\\\":\\\"strikeout\\\",\\\"rects\\\":[[1,2,3,4.5]]}\",\"text\":\"t\",\"comment\":null,\"color\":\"#ff0000\",\"sortIndex\":\"00002|000000|00000\"}}").toUTF8).toOption.getD .null
  (neutralOfStored child).map jtext ==
    some "{\"id\":\"7R\",\"kind\":\"strikeout\",\"pageIndex\":2,\"rects\":[[1,2,3,4.5]],\"text\":\"t\",\"comment\":null,\"color\":\"#ff0000\",\"sortIndex\":\"00002|000000|00000\",\"extra\":null}"
#guard neutralOfStored (.obj #[("itemType", .str "note")]) |>.isNone
-- A position that is not contract JSON: the stored kind, no rects, no id (pass-through).
#guard let child := JVal.obj #[("itemType", .str "annotation"), ("annotation", .obj
      #[("kind", .str "highlight"), ("pageIndex", .num "0"), ("position", .str "{bad"),
        ("color", .str "#ffd400"), ("sortIndex", .str "x")])]
  ((neutralOfStored child).bind ownMark?).isNone &&
    (neutralOfStored child).map jtext ==
      some "{\"id\":null,\"kind\":\"highlight\",\"pageIndex\":0,\"rects\":[],\"text\":null,\"comment\":null,\"color\":\"#ffd400\",\"sortIndex\":\"x\",\"extra\":null}"
-- Colours off the palette load as the nearest palette colour.
#guard let v := JVal.obj #[("id", .str "safepdf-mark-5"), ("kind", .str "highlight"),
      ("pageIndex", .num "1"), ("rects", .arr #[.arr #[.num "10", .num "20", .num "30", .num "40"]]),
      ("color", .str "#ff2020")]
  (ownMark? v).map (fun (m, _) => (m.id, m.page, m.color, m.quads)) ==
    some (5, 1, .red, [⟨10, 20, 30, 40⟩])
-- Coordinates: user space on both sides, whatever the rotation and the CropBox origin. A page
-- with CropBox [50 60 500 760] and /Rotate 90: the rectangle is the quad itself, the note icon
-- is placed inside the CropBox, and `top` is the CropBox's upper edge (760).
#guard let crop : Box := ⟨50, 60, 500, 760⟩
  let info' (_ : Nat) : PageInfo := ⟨crop, #[]⟩
  let s := (({} : Store).addHighlight 0 .yellow [⟨100, 690, 160, 702⟩]).map (·.1) |>.getD {}
  let s := (s.addNote 0 .yellow "corner" (.point ⟨10, 790⟩)).1
  neutralsOf info' s ==
    ["{\"id\":\"safepdf-mark-2\",\"kind\":\"note\",\"pageIndex\":0,\"rects\":[[50,740,70,760]],\"text\":null,\"comment\":\"corner\",\"color\":\"#ffff98\",\"sortIndex\":\"00000|000000|00000\",\"extra\":null}",
     "{\"id\":\"safepdf-mark-1\",\"kind\":\"highlight\",\"pageIndex\":0,\"rects\":[[100,690,160,702]],\"text\":null,\"comment\":null,\"color\":\"#ffff98\",\"sortIndex\":\"00000|000000|00058\",\"extra\":null}"]
-- The screen transform is where rotation and the CropBox origin act: the same quad maps to
-- different pixels for /Rotate 0 and 90, while its contract rectangle stays the same.
#guard let crop : Box := ⟨50, 60, 500, 760⟩
  let q : Box := ⟨100, 690, 160, 702⟩
  Raster.Geom.toScreen 1 .r0 crop ⟨q.llx, q.ury⟩ == ⟨50, 58⟩ &&
    Raster.Geom.toScreen 1 .r90 crop ⟨q.llx, q.ury⟩ == ⟨642, 50⟩ &&
    rectOf q == "[100,690,160,702]"

/-! ## The background sync (IO) -/

/-- Mutable state of a `Sync`, behind one `IO.Ref` (all updates are `modifyGet`s). -/
structure SyncState where
  /-- Bumped by every change and every save. -/
  gen : Nat := 0
  /-- The newest store (`none` until the first change). -/
  store : Option Store := none
  /-- Annotated bytes waiting for the `PUT`. -/
  put : Option ByteArray := none
  /-- Whether the worker thread runs. -/
  running : Bool := false
  /-- Skip the debounce wait (on exit). -/
  urgent : Bool := false
  /-- The last body the server accepted. -/
  lastSent : Option String := none
  /-- Elements of other viewers, posted back verbatim. -/
  passthrough : Array JVal := #[]
  /-- Outcomes, oldest first (`POST …/annotations: HTTP 200`, …). -/
  log : Array String := #[]
  /-- Glyph cells and CropBoxes of pages, computed on first use. -/
  pages : Array (Option PageInfo) := #[]
  deriving Inhabited

/-- The annotation sync of one bib-lean session. -/
structure Sync where
  /-- Server, key and token. -/
  session : Launch.Session
  /-- The document as opened (page text, CropBoxes). -/
  document : SafePdf.Api.Document
  /-- The stored set of the launch (neutral elements, in the answer's order). -/
  stored : Array JVal
  /-- Debounce delay in milliseconds. -/
  debounceMs : UInt32 := 400
  /-- Where outcomes are reported (stderr by default; never the token or a body). -/
  report : String → IO Unit := fun m => IO.eprintln s!"viewer --biblean: {m}"
  /-- The state. -/
  state : IO.Ref SyncState

/-- Largest file `PUT` accepts (contract §3: 64 MiB). -/
def maxPutBytes : Nat := 64 * 1024 * 1024

/-- Limits of the `PUT`'s answer: small JSON, two minutes. -/
def putLimits : Http.Limits := { maxBodyBytes := 64 * 1024, timeoutMs := 120000 }

/-- The sync of an opened session (`stored`: the elements of `Opened.detail`). -/
def Sync.create (o : Launch.Opened) : IO Sync := do
  let stored := (o.detail.map storedOf).getD #[]
  let pages := Array.replicate o.document.pageCount none
  return { session := o.session, document := o.document, stored,
           state := ← IO.mkRef { pages } }

/-- **`loadInitial`**: the store to show, `fileStore` (the marks read back from the PDF)
merged with the stored set (`mergeStored`); remembers the pass-through elements. -/
def Sync.load (y : Sync) (fileStore : Store) : IO Store := do
  let (s, other) := mergeStored y.stored fileStore
  y.state.modify ({ · with passthrough := other })
  return s

/-- The page info of page `i` (cached). -/
def Sync.pageInfo (y : Sync) (i : Nat) : IO PageInfo := do
  if let some (some pi) := (← y.state.get).pages[i]? then return pi
  let d := y.document
  let box := (Save.pageBox d.doc i).getD ⟨0, 0, 612, 792⟩
  let cells := match SafePdf.Api.pageTextCore d i with
    | .ok pt => Select.cellsOf {} pt.lines
    | .error _ => #[]
  let pi : PageInfo := { box, cells }
  y.state.modify fun st => { st with pages := st.pages.setIfInBounds i (some pi) }
  return pi

/-- Records and reports one outcome (reported only when it is a failure). -/
def Sync.note (y : Sync) (msg : String) (failed : Bool) : IO Unit := do
  y.state.modify fun st => { st with log := st.log.push msg }
  if failed then y.report msg

/-- `PUT /api/attachments/{key}/file` with `bytes` (never throws). -/
def Sync.sendFile (y : Sync) (bytes : ByteArray) : IO Unit := do
  let path := s!"/api/attachments/{y.session.key}/file"
  if bytes.size > maxPutBytes then
    y.note s!"PUT {path}: not sent, {bytes.size} bytes is more than 64 MiB" true
    return
  try
    let r ← Http.exchange y.session.origin y.session.token "PUT" path
      (some (bytes, "application/pdf")) putLimits
    let code := (Launch.errorCode? r.body).map (s!" ({·})") |>.getD ""
    y.note s!"PUT {path}: HTTP {r.status}{code}" !(200 ≤ r.status && r.status < 300)
  catch e => y.note s!"{e}" true

/-- Posts the set of `s` unless the server already has exactly this body. -/
def Sync.sendSet (y : Sync) (s : Store) : IO Unit := do
  let mut infos : Array PageInfo := #[]
  for i in [0:y.document.pageCount] do
    if s.marks.any (·.page == i) then infos := infos.push (← y.pageInfo i)
    else infos := infos.push default
  let st ← y.state.get
  let body := bodyOf (fun i => infos.getD i default) s st.passthrough
  if st.lastSent == some body then return
  let path := s!"/api/attachments/{y.session.key}/annotations"
  let (ok, msg) ← Launch.postAttachment y.session "annotations" body.toUTF8 "application/json"
  if ok then y.state.modify ({ · with lastSent := some body })
  y.note s!"POST {path}: {msg}" !ok

/-- The worker: waits for `debounceMs` without a change (unless urgent), then sends the
queued file and the newest set; ends when nothing new came meanwhile. -/
def Sync.worker (y : Sync) : IO Unit := do
  repeat
    let g0 := (← y.state.get).gen
    unless (← y.state.get).urgent do IO.sleep y.debounceMs
    let st ← y.state.get
    if st.gen != g0 && !st.urgent then continue
    let (g1, put, store) ← y.state.modifyGet fun st =>
      ((st.gen, st.put, st.store), { st with put := none })
    if let some b := put then y.sendFile b
    if let some s := store then y.sendSet s
    let done ← y.state.modifyGet fun st =>
      if st.gen == g1 && st.put.isNone then (true, { st with running := false })
      else (false, st)
    if done then break

/-- Wakes the worker (starts it unless it runs). -/
def Sync.kick (y : Sync) (f : SyncState → SyncState) : IO Unit := do
  let start ← y.state.modifyGet fun st =>
    let st := f { st with gen := st.gen + 1 }
    (!st.running, { st with running := true })
  if start then
    discard <| IO.asTask (prio := .dedicated) do
      try y.worker
      catch e =>
        y.state.modify ({ · with running := false })
        y.report s!"annotation sync stopped: {e}"

/-- **`onMarksChanged`**: the viewer's store after a change (add, remove, recolour, text,
save); posted after `debounceMs` without a further change. Returns at once. -/
def Sync.onMarksChanged (y : Sync) (s : Store) : IO Unit :=
  y.kick ({ · with store := some s })

/-- **`onSaved`**: the annotated file (`Save.build`'s bytes) to `PUT`; sent by the worker
before the next post. Returns at once. -/
def Sync.onSaved (y : Sync) (bytes : ByteArray) : IO Unit :=
  y.kick ({ · with put := some bytes })

/-- **On exit**: sends what is pending without the debounce wait and waits at most `graceMs`
for it. `true` when everything was sent (or nothing was pending). -/
def Sync.flush (y : Sync) (graceMs : Nat := 3000) : IO Bool := do
  let pending ← y.state.modifyGet fun st =>
    (st.running || st.put.isSome || st.store.isSome, { st with urgent := true })
  unless pending do return true
  -- A fresh round (it skips the wait); it posts nothing when the server has this body.
  y.kick id
  let t0 ← IO.monoMsNow
  repeat
    if !(← y.state.get).running then break
    if (← IO.monoMsNow) - t0 ≥ graceMs then break
    IO.sleep 20
  return !(← y.state.get).running

/-- The outcomes so far. -/
def Sync.outcomes (y : Sync) : IO (Array String) := return (← y.state.get).log

end SafePdf.Shell.App.BibLean.Annots
