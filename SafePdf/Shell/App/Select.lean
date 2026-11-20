import SafePdf.Core.Text
import SafePdf.Core.Raster.Geom

/-!
# Viewer text selection and search (task 8.2c; Plan.md §4 C3, §6 Phase 8, §10 `SafePdf/Shell/`)

The pure, Tk-free part of the viewer's selection, copy and search (unverified shell code, but
total and checked by `#guard`s, with one theorem about search hits). Everything is computed
from the verified text extraction (`Core.Text.PageText`, through
`Annot.extractDocPageAnnots` in the viewer, as the text view): the glyphs' page-space origins,
advances and sizes (C3: text ↔ position) and the reading-order lines of `Text.layout`.

* **Cells.** `cellsOf o lines` lists the glyphs of the page in reading order (lines in order,
  each line's glyphs in `Text.lineOrder`) as `Cell`s: the glyph's text, the separator that the
  layout puts before it (`""`, a word space `" "`, or the line break `"\n"`/`"\n\n"`), its
  page-space box and its line. The separators follow `Text.lineText`/`Text.layout` exactly
  (overprinted duplicates keep their box but contribute no text), so the text of all cells is
  the page text (`fullText`, checked by `#guard`s against `Text.layout`).
* **Boxes.** `glyphBox g`: along the baseline from the origin to the end of the advance, across
  it from 0.2 em below to 0.8 em above the baseline, in the glyph's own direction (`dir`),
  as an axis-aligned page-space `Box`.
* **Selection.** A selection is a range of cells (inclusive). `nearest cs p`: the cell whose
  box is nearest to the page point `p` (squared distance to the box, 0 inside; first on ties).
  A drag from `p` to `q` selects `nearest p … nearest q` in reading order (`dragRange`);
  `wordAt` extends a cell to its word (letters, digits and non-ASCII characters joined without
  separator); `rangeText` is the text to copy; `rangeBoxes` the highlight rectangles (one per
  line run).
* **Search.** `normChars cs`: the page text lower-cased (ASCII and Latin-1 letters) with every
  whitespace run collapsed to one space, each character tagged with the cell it comes from
  (separator characters with the cell they precede). `normQuery` normalises a query the same
  way and trims it. `findAll hay q` lists the start positions of every match (overlapping
  matches included); `findAll_sound` proves each one is a match. `hitRange` maps a match to
  its cells (a query never starts or ends with a space, so both ends are glyph characters).
-/

namespace SafePdf.Shell.App.Select

open SafePdf.Core
open SafePdf.Core.Content (Fixed)
open SafePdf.Core.Raster.Geom (Pt Box)
open SafePdf.Core.Text (Glyph Line Options)

/-! ## Cells -/

/-- A glyph of the page in reading order. -/
structure Cell where
  /-- The glyph's text (`""` for an overprinted duplicate, which `Text.lineText` drops). -/
  text : String
  /-- What the layout puts before this glyph when it follows the previous cell: `""`, `" "`
  (word gap) or a line break (`"\n"`, `"\n\n"`); `""` for the first cell. -/
  sep : String
  /-- Page-space box (`glyphBox`). -/
  box : Box
  /-- Index of its line in `PageText.lines`. -/
  line : Nat
  deriving Repr, Inhabited

/-- A `Fixed` as a rational number. -/
def fr (x : Fixed) : Rat := (x.raw : Rat) / 1000000

/-- Page coordinates of a point given in a direction's frame (inverse of `Text.rotFrame`). -/
def unFrame (dir : Nat) (u v : Rat) : Rat × Rat :=
  match dir with
  | 1 => (-v, u)
  | 2 => (-u, -v)
  | 3 => (v, -u)
  | _ => (u, v)

/-- Descent of a glyph box below the baseline, in em. -/
def descent : Rat := 1 / 5

/-- Ascent of a glyph box above the baseline, in em. -/
def ascent : Rat := 4 / 5

/-- The page-space box of a glyph: its advance along the baseline, `descent` em below and
`ascent` em above the baseline (in the glyph's direction), as an axis-aligned box. -/
def glyphBox (g : Glyph) : Box :=
  let u0 := fr g.u
  let u1 := fr g.uEnd
  let v := fr g.v
  let s0 := fr g.fontSize
  let s := if s0 < 0 then -s0 else s0
  let (x0, y0) := unFrame g.dir (min u0 u1) (v - descent * s)
  let (x1, y1) := unFrame g.dir (max u0 u1) (v + ascent * s)
  ⟨min x0 x1, min y0 y1, max x0 x1, max y0 y1⟩

/-- The separator before the first glyph of line `l` after line `prev` (as `Text.layout`). -/
def lineSep (o : Options) (prev : Option Line) (l : Line) : String :=
  match prev with
  | none => ""
  | some p =>
    if l.dir != p.dir ||
        Text.withinPermille (Fixed.sub l.v p.v) (Text.fmax p.size l.size) o.paraGap then "\n"
    else "\n\n"

/-- The cells of one line (line index `li`, separator `lsep` before its first glyph), as
`Text.lineText` lays it out: an overprinted duplicate gets empty text and separator; a word
gap becomes `" "`. -/
def lineCells (o : Options) (li : Nat) (lsep : String) (l : Line) : Array Cell :=
  let (out, _) := (Text.lineOrder o l).foldl (fun (acc : Array Cell × Option Glyph) g =>
    match acc.2 with
    | none => (acc.1.push ⟨g.text, lsep, glyphBox g, li⟩, some g)
    | some p =>
      let sz := Text.fmax p.fontSize g.fontSize
      let dup := p.text == g.text && Text.withinPermille (Fixed.sub g.u p.u) sz 100 &&
        Text.withinPermille (Fixed.sub g.v p.v) sz 100
      if dup then (acc.1.push ⟨"", "", glyphBox g, li⟩, acc.2)
      else
        let gap := Fixed.sub g.u (Fixed.add p.u p.width)
        let space := gap.raw > 0 && !Text.withinPermille gap sz o.wordGap &&
          Text.spaceMayFollow p.text && !g.text.startsWith " "
        (acc.1.push ⟨g.text, if space then " " else "", glyphBox g, li⟩, some g)) (#[], none)
  out

/-- The cells of a page: the glyphs of `lines` (`PageText.lines`) in reading order. -/
def cellsOf (o : Options) (lines : Array Line) : Array Cell :=
  let (out, _, _) := lines.foldl (fun (acc : Array Cell × Option Line × Nat) l =>
    (acc.1 ++ lineCells o acc.2.2 (lineSep o acc.2.1 l) l, some l, acc.2.2 + 1)) (#[], none, 0)
  out

/-- The text of the cells `a … b` (inclusive, in either order; clamped to the array). -/
def rangeText (cs : Array Cell) (a b : Nat) : String :=
  let lo := min a b
  let hi := min (max a b) (cs.size - 1)
  (List.range (hi + 1 - lo)).foldl (fun acc k =>
    match cs[lo + k]? with
    | some c => if k == 0 then acc ++ c.text else acc ++ c.sep ++ c.text
    | none => acc) ""

/-- The text of all cells. -/
def fullText (cs : Array Cell) : String :=
  if cs.size == 0 then "" else rangeText cs 0 (cs.size - 1)

/-! ## Hit testing -/

/-- Squared distance from `p` to the box `b` (0 inside). -/
def distSq (b : Box) (p : Pt) : Rat :=
  let dx := if p.x < b.llx then b.llx - p.x else if b.urx < p.x then p.x - b.urx else 0
  let dy := if p.y < b.lly then b.lly - p.y else if b.ury < p.y then p.y - b.ury else 0
  dx * dx + dy * dy

/-- The cell whose box is nearest to the page point `p` (the first on ties); `none` when there
are no cells. -/
def nearest (cs : Array Cell) (p : Pt) : Option Nat :=
  let (_, best) := cs.foldl (fun (acc : Nat × Option (Nat × Rat)) c =>
    let d := distSq c.box p
    let best := match acc.2 with
      | some (j, e) => if d < e then some (acc.1, d) else some (j, e)
      | none => some (acc.1, d)
    (acc.1 + 1, best)) (0, none)
  best.map (·.1)

/-- The cell range (low, high) selected by a drag from page point `p` to `q`. -/
def dragRange (cs : Array Cell) (p q : Pt) : Option (Nat × Nat) :=
  match nearest cs p, nearest cs q with
  | some a, some b => some (min a b, max a b)
  | _, _ => none

/-- Whether a cell's text belongs to a word: letters, digits, or characters above ASCII
(accented letters, CJK, …); an empty (overprint) cell joins its neighbours. -/
def wordish (c : Cell) : Bool :=
  c.text.all fun ch => ch.isAlphanum || (ch.toNat ≥ 128 && ch.toNat != 0xA0)

/-- Moves `i` left while the cell before it belongs to the same word (`fuel` steps). -/
def wordLo (cs : Array Cell) : Nat → Nat → Nat
  | 0, i => i
  | fuel + 1, i =>
    match i, cs[i]?, cs[i - 1]? with
    | 0, _, _ => 0
    | _, some c, some p => if c.sep == "" && wordish p then wordLo cs fuel (i - 1) else i
    | _, _, _ => i

/-- Moves `i` right while the next cell belongs to the same word (`fuel` steps). -/
def wordHi (cs : Array Cell) : Nat → Nat → Nat
  | 0, i => i
  | fuel + 1, i =>
    match cs[i + 1]? with
    | some n => if n.sep == "" && wordish n then wordHi cs fuel (i + 1) else i
    | none => i

/-- The word around cell `i` (double click): the maximal run of `wordish` cells without a
separator between them; just `i` when its own text is not a word character. -/
def wordAt (cs : Array Cell) (i : Nat) : Nat × Nat :=
  match cs[i]? with
  | some c =>
    if c.text.isEmpty || !wordish c then (i, i)
    else (wordLo cs i i, wordHi cs cs.size i)
  | none => (i, i)

/-- Union of two boxes. -/
def Box.union (a b : Box) : Box :=
  ⟨min a.llx b.llx, min a.lly b.lly, max a.urx b.urx, max a.ury b.ury⟩

/-- Highlight boxes of the cells `a … b` (inclusive): one box per run of cells on the same
line, in reading order. -/
def rangeBoxes (cs : Array Cell) (a b : Nat) : List Box :=
  let lo := min a b
  let hi := max a b
  let (done, cur) := (List.range (hi + 1 - lo)).foldl
    (fun (acc : Array Box × Option (Nat × Box)) k =>
      match cs[lo + k]? with
      | none => acc
      | some c =>
        match acc.2 with
        | some (l, bx) =>
          if l == c.line then (acc.1, some (l, Box.union bx c.box))
          else (acc.1.push bx, some (c.line, c.box))
        | none => (acc.1, some (c.line, c.box))) (#[], none)
  match cur with
  | some (_, bx) => (done.push bx).toList
  | none => done.toList

/-! ## Search -/

/-- Lower case for ASCII and Latin-1 capitals (À–Þ except ×). -/
def lowerChar (c : Char) : Char :=
  if ('A'.toNat ≤ c.toNat && c.toNat ≤ 'Z'.toNat) ||
      (0xC0 ≤ c.toNat && c.toNat ≤ 0xDE && c.toNat != 0xD7) then Char.ofNat (c.toNat + 32)
  else c

/-- Whitespace for search: Unicode `isWhitespace` (ASCII) and U+00A0. -/
def isWs (c : Char) : Bool := c.isWhitespace || c.toNat == 0xA0

/-- Appends `c` (tagged `i`) to a normalised character array: lower-cased; whitespace becomes
one space, dropped at the start and after another space. -/
def pushNorm (out : Array (Char × Nat)) (i : Nat) (c : Char) : Array (Char × Nat) :=
  if isWs c then
    match out.back? with
    | some (' ', _) | none => out
    | _ => out.push (' ', i)
  else out.push (lowerChar c, i)

/-- The page text normalised for search, each character tagged with its cell. -/
def normChars (cs : Array Cell) : Array (Char × Nat) :=
  let (out, _) := cs.foldl (fun (acc : Array (Char × Nat) × Nat) c =>
    let o := (c.sep.toList ++ c.text.toList).foldl (fun o ch => pushNorm o acc.2 ch) acc.1
    (o, acc.2 + 1)) (#[], 0)
  out

/-- A query normalised as `normChars` (lower case, whitespace runs to one space) and trimmed. -/
def normQuery (s : String) : Array Char :=
  let a := (s.toList.foldl (fun o ch => pushNorm o 0 ch) #[]).map (·.1)
  match a.back? with
  | some ' ' => a.pop
  | _ => a

/-- Whether the query `q` occurs in `hay` at position `k`. -/
def matchAt (hay : Array (Char × Nat)) (q : Array Char) (k : Nat) : Bool :=
  decide (k + q.size ≤ hay.size) &&
    (List.range q.size).all fun j => (hay[k + j]?).map Prod.fst == q[j]?

/-- All start positions of `q` in `hay`, ascending (overlapping matches included; none for an
empty query). -/
def findAll (hay : Array (Char × Nat)) (q : Array Char) : List Nat :=
  if q.size == 0 then []
  else (List.range (hay.size + 1 - q.size)).filter (matchAt hay q)

/-- **Search hits are matches**: at every position `findAll` returns, the normalised page
text holds exactly the query's characters. -/
theorem findAll_sound {hay : Array (Char × Nat)} {q : Array Char} {k : Nat}
    (h : k ∈ findAll hay q) :
    k + q.size ≤ hay.size ∧ ∀ j, j < q.size → (hay[k + j]?).map Prod.fst = q[j]? := by
  unfold findAll at h
  split at h
  · simp at h
  · have hm := (List.mem_filter.mp h).2
    unfold matchAt at hm
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
      beq_iff_eq] at hm
    exact ⟨hm.1, fun j hj => hm.2 j hj⟩

/-- The cells (first, last) of the match of length `n` at position `k`. -/
def hitRange (hay : Array (Char × Nat)) (n k : Nat) : Nat × Nat :=
  (((hay[k]?).map (·.2)).getD 0, ((hay[k + n - 1]?).map (·.2)).getD 0)

/-- A page's selection and search index: its cells and its normalised text. -/
structure PageIndex where
  /-- Cells in reading order. -/
  cells : Array Cell
  /-- Normalised text with cell tags (`normChars cells`). -/
  hay : Array (Char × Nat)
  deriving Inhabited

/-- The index of an extracted page (default layout options, as the text view). -/
def PageIndex.ofText (pt : Text.PageText) : PageIndex :=
  let cs := cellsOf {} pt.lines
  ⟨cs, normChars cs⟩

/-- The hits of `q` on a page, as cell ranges. -/
def PageIndex.hits (ix : PageIndex) (q : Array Char) : Array (Nat × Nat) :=
  ((findAll ix.hay q).map (hitRange ix.hay q.size)).toArray

/-! ## Checks -/

/-- A synthetic left-to-right glyph of size 10 at `(x, y)` with advance `w`. -/
private def mkG (t : String) (x y w : Int) (dir : Nat := 0) : Glyph :=
  { text := t, code := [], item := 0, seq := 0, x := Fixed.ofInt x, y := Fixed.ofInt y,
    width := Fixed.ofInt w, dir, fontSize := Fixed.ofInt 10, visible := true }

/-- "Hello World" (word gap 17) on one line, "Zebra" on the next, "end" after a paragraph
gap; the first line ends with an overprint of the second `l` (dropped by the layout). -/
private def sample : List Glyph :=
  [mkG "H" 100 700 7, mkG "e" 107 700 5, mkG "l" 112 700 3, mkG "l" 115 700 3, mkG "o" 118 700 5,
   mkG "W" 140 700 9, mkG "o" 149 700 5, mkG "r" 154 700 4, mkG "l" 158 700 3, mkG "d" 161 700 5,
   mkG "l" 115 700 3,
   mkG "Z" 100 688 6, mkG "e" 106 688 5, mkG "b" 111 688 5, mkG "r" 116 688 4, mkG "a" 120 688 5,
   mkG "e" 100 600 5, mkG "n" 105 600 5, mkG "d" 110 600 5]

/-- Cells of `sample`: H0 e1 l2 l3 (overprint)4 o5 W6 o7 r8 l9 d10 Z11 e12 b13 r14 a15 e16 n17
d18. -/
private def sampleCells : Array Cell := cellsOf {} (Text.layout {} sample).1

/-- The extraction result of `sample`. -/
private def samplePT : Text.PageText :=
  { fonts := [], items := #[], glyphs := sample, lines := (Text.layout {} sample).1, text := "",
    warnings := 0 }

-- The cells' text is the layout's page text (separators and overprints as `Text.layout`).
#guard (Text.layout {} sample).2 == "Hello World\nZebra\n\nend"
#guard fullText sampleCells == (Text.layout {} sample).2
#guard fullText (cellsOf {} (Text.layout {} sample.reverse).1) == (Text.layout {} sample.reverse).2
#guard (sampleCells[4]?.map (·.text)) == some ""
#guard rangeText sampleCells 6 13 == "World\nZeb"
#guard rangeText sampleCells 13 6 == "World\nZeb"
#guard rangeText sampleCells 15 100 == "a\n\nend"
-- Boxes: x along the advance, y from 2 below to 8 above the baseline (size 10); rotated text.
#guard (sampleCells[0]?.map (·.box)) == some ⟨100, 698, 107, 708⟩
#guard glyphBox (mkG "A" 100 700 6 1) == ⟨92, 700, 102, 706⟩
-- Hit testing: inside a box, and the nearest box from outside.
#guard nearest sampleCells ⟨101, 703⟩ == some 0
#guard nearest sampleCells ⟨170, 701⟩ == some 10
#guard nearest sampleCells ⟨103, 650⟩ == some 11
#guard dragRange sampleCells ⟨150, 703⟩ ⟨101, 690⟩ == some (7, 11)
#guard (dragRange sampleCells ⟨150, 703⟩ ⟨101, 690⟩).map (fun (a, b) => rangeText sampleCells a b)
  == some "orld\nZ"
#guard dragRange #[] ⟨0, 0⟩ ⟨1, 1⟩ == none
-- Double click: the word around a cell (the overprint belongs to "Hello").
#guard wordAt sampleCells 1 == (0, 5) && wordAt sampleCells 7 == (6, 10)
#guard rangeText sampleCells (wordAt sampleCells 8).1 (wordAt sampleCells 8).2 == "World"
-- One highlight box per line run.
#guard rangeBoxes sampleCells 6 12 == [⟨140, 698, 166, 708⟩, ⟨100, 686, 111, 696⟩]
-- Search: case-insensitive, whitespace-normalised, hits mapped back to cells.
#guard normQuery "  hELLO \n  world " == #['h', 'e', 'l', 'l', 'o', ' ', 'w', 'o', 'r', 'l', 'd']
#guard normQuery "ÀB×" == #['à', 'b', '×']
#guard String.ofList (normChars sampleCells).toList.unzip.1 == "hello world zebra end"
#guard (PageIndex.ofText samplePT).hits (normQuery "O W") == #[(5, 6)]
#guard ((PageIndex.ofText samplePT).hits (normQuery "zebra   END")).toList.map
  (fun (a, b) => rangeText sampleCells a b) == ["Zebra\n\nend"]
#guard let ix := PageIndex.ofText samplePT
  (ix.hits (normQuery "l")).size == 3 && (ix.hits (normQuery "xyz")).size == 0 &&
    (ix.hits (normQuery "  ")).size == 0
#guard findAll #[('a', 0), ('a', 1), ('a', 2)] #['a', 'a'] == [0, 1]

end SafePdf.Shell.App.Select
