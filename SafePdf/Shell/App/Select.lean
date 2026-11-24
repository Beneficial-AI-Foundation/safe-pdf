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
  line run, for search hits and highlight marks); `selBands` the drawn selection (one band per
  line, full line height, consecutive lines of a paragraph joined; task 10.18, see the section
  doc and `bandAt_meet`, `shape_covers`, `bandAt_covers`).
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

/-- The separator before the first glyph of line `l` after line `prev` (`Text.lineSep`, as
`Text.layout`). -/
def lineSep (o : Options) (prev : Option Line) (l : Line) : String := Text.lineSep o prev l

/-- The cells of one line (line index `li`, separator `lsep` before its first glyph), as
`Text.lineText` lays it out (`Text.glyphSep`): an overprinted duplicate gets empty text and
separator; a word gap becomes `" "`. -/
def lineCells (o : Options) (li : Nat) (lsep : String) (l : Line) : Array Cell :=
  let (out, _) := (Text.lineOrder o l).foldl (fun (acc : Array Cell × Option Glyph) g =>
    match acc.2 with
    | none => (acc.1.push ⟨g.text, lsep, glyphBox g, li⟩, some g)
    | some p =>
      match Text.glyphSep o l.frame p g with
      | none => (acc.1.push ⟨"", "", glyphBox g, li⟩, acc.2)
      | some sep => (acc.1.push ⟨g.text, sep, glyphBox g, li⟩, some g)) (#[], none)
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

/-- The runs of the cells `a … b` (inclusive) on one line, in reading order: the line, the
index of the run's first cell and the union of the run's boxes. -/
def lineRuns (cs : Array Cell) (a b : Nat) : List (Nat × Nat × Box) :=
  let lo := min a b
  let hi := max a b
  let (done, cur) := (List.range (hi + 1 - lo)).foldl
    (fun (acc : Array (Nat × Nat × Box) × Option (Nat × Nat × Box)) k =>
      match cs[lo + k]? with
      | none => acc
      | some c =>
        match acc.2 with
        | some (l, i, bx) =>
          if l == c.line then (acc.1, some (l, i, Box.union bx c.box))
          else (acc.1.push (l, i, bx), some (c.line, lo + k, c.box))
        | none => (acc.1, some (c.line, lo + k, c.box))) (#[], none)
  match cur with
  | some r => (done.push r).toList
  | none => done.toList

/-- Highlight boxes of the cells `a … b` (inclusive): one box per run of cells on the same
line, in reading order (search hits, highlight marks' quads). -/
def rangeBoxes (cs : Array Cell) (a b : Nat) : List Box :=
  (lineRuns cs a b).map (·.2.2)

/-! ## Selection bands (task 10.18)

The selection is drawn as one band per line, a continuous fill as in PDF.js and Preview:

* **Height.** A band spans its line's full height: from the lowest to the highest glyph box of
  the whole line (every cell of that line, selected or not).
* **Width.** The first line of the selection runs from the selection start (its leftmost
  selected glyph box) to the line's end, interior lines from the line's start to its end, the
  last line from the line's start to the selection end; a single-line selection from the start
  to the end glyph. Each band also contains the union of the line's selected glyph boxes
  (`shape`), so it covers every selected glyph box whatever the glyph order.
* **Joining.** Two consecutive bands are joined — the upper one's bottom and the lower one's
  top both move to the midpoint of the gap — when (1) both lines are left-to-right horizontal
  text (direction 0), (2) the layout puts a plain line break between them (`"\n"`: same
  direction and frame, baseline step within `Options.paraGap`; a paragraph break `"\n\n"` or a
  column change is never joined), and (3) the gap between the bands is between 0 and the
  smaller band's height. Bands only ever grow (`lowerTo`, `raiseTo`), so overlapping bands of
  tightly set lines stay as they are (they already touch).
* **Other directions.** Lines that are not left-to-right horizontal (rotated or vertical
  text) keep the run box of their selected glyphs, as `rangeBoxes`, and are never joined.

Copy and search are unchanged (`rangeText`, `findAll`); only the drawn shape is new. -/

/-- `a` lies inside `b`. -/
def Box.inside (a b : Box) : Prop :=
  b.llx ≤ a.llx ∧ b.lly ≤ a.lly ∧ a.urx ≤ b.urx ∧ a.ury ≤ b.ury

instance (a b : Box) : Decidable (Box.inside a b) := by unfold Box.inside; exact inferInstance

/-- The band of one selected line before joining: the full line's height (`full`), from the
selection start (`first` line) or the line start to the selection end (`last` line) or the
line end, united with the selected glyphs' run box `sel`. -/
def shape (first last : Bool) (full sel : Box) : Box :=
  Box.union sel ⟨if first then sel.llx else full.llx, full.lly,
    if last then sel.urx else full.urx, full.ury⟩

/-- **A shaped band covers the selected glyphs of its line.** -/
theorem shape_covers (first last : Bool) (full sel : Box) :
    Box.inside sel (shape first last full sel) := by
  unfold Box.inside shape Box.union
  simp only
  refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

/-- Moves a band's bottom down to `m` (when joined below); never shrinks it. -/
def lowerTo (b : Box) : Option Rat → Box
  | some m => { b with lly := min b.lly m }
  | none => b

/-- Moves a band's top up to `m` (when joined above); never shrinks it. -/
def raiseTo (b : Box) : Option Rat → Box
  | some m => { b with ury := max b.ury m }
  | none => b

/-- Height of a box. -/
def Box.height (b : Box) : Rat := b.ury - b.lly

/-- Where the bands `k` and `k + 1` of `bs` meet, when `ok k` (same paragraph, both horizontal)
and the gap from the upper band's bottom down to the lower band's top is between 0 and the
smaller band's height: the gap's midpoint. -/
def meetAt (bs : Array Box) (ok : Nat → Bool) (k : Nat) : Option Rat :=
  match bs[k]?, bs[k + 1]? with
  | some u, some w =>
    if ok k && decide (w.ury ≤ u.lly) &&
        decide (u.lly - w.ury ≤ min (Box.height u) (Box.height w)) then
      some ((u.lly + w.ury) / 2)
    else none
  | _, _ => none

/-- Where band `k` meets band `k - 1` (none for the first band). -/
def prevMeet (bs : Array Box) (ok : Nat → Bool) : Nat → Option Rat
  | 0 => none
  | j + 1 => meetAt bs ok j

/-- The joined band `k` of the shaped bands `bs`: lowered to the meeting point with band
`k + 1`, raised to the one with band `k - 1`. -/
def bandAt (bs : Array Box) (ok : Nat → Bool) (k : Nat) : Option Box :=
  bs[k]?.map fun b => raiseTo (lowerTo b (meetAt bs ok k)) (prevMeet bs ok k)

/-- The meeting point lies in the gap: at or below the upper band's bottom, at or above the
lower band's top. -/
theorem meetAt_spec {bs : Array Box} {ok : Nat → Bool} {k : Nat} {m : Rat}
    (h : meetAt bs ok k = some m) :
    ∃ u w, bs[k]? = some u ∧ bs[k + 1]? = some w ∧ m ≤ u.lly ∧ w.ury ≤ m := by
  unfold meetAt at h
  split at h
  · rename_i u w hu hw
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      cases h
      exact ⟨u, w, hu, hw, by grind, by grind⟩
    · cases h
  · cases h

/-- **Joined bands meet**: when bands `k` and `k + 1` are joined, the bottom of band `k` is the
top of band `k + 1` (no gap, no overlap). -/
theorem bandAt_meet {bs : Array Box} {ok : Nat → Bool} {k : Nat} {m : Rat}
    (h : meetAt bs ok k = some m) :
    ∃ u w, bandAt bs ok k = some u ∧ bandAt bs ok (k + 1) = some w ∧ u.lly = m ∧ w.ury = m := by
  obtain ⟨u, w, hu, hw, hm1, hm2⟩ := meetAt_spec h
  refine ⟨raiseTo (lowerTo u (some m)) (prevMeet bs ok k),
    raiseTo (lowerTo w (meetAt bs ok (k + 1))) (some m),
    by simp [bandAt, hu, h], by simp [bandAt, hw, prevMeet, h], ?_, ?_⟩
  · cases prevMeet bs ok k <;> simp [raiseTo, lowerTo] <;> grind
  · cases meetAt bs ok (k + 1) <;> simp [raiseTo, lowerTo] <;> grind

/-- **Joining only grows a band**: the joined band `k` contains the shaped band `k`. -/
theorem bandAt_covers {bs : Array Box} {ok : Nat → Bool} {k : Nat} {b : Box}
    (h : bs[k]? = some b) : ∃ c, bandAt bs ok k = some c ∧ Box.inside b c := by
  refine ⟨raiseTo (lowerTo b (meetAt bs ok k)) (prevMeet bs ok k), by simp [bandAt, h], ?_⟩
  unfold Box.inside
  cases meetAt bs ok k <;> cases prevMeet bs ok k <;> simp [raiseTo, lowerTo] <;> grind

/-- The first cell of the line of cell `i` (moving left at most `fuel` cells). -/
def lineStart (cs : Array Cell) : Nat → Nat → Nat
  | 0, i => i
  | fuel + 1, i =>
    match i with
    | 0 => 0
    | j + 1 =>
      match cs[j]?, cs[j + 1]? with
      | some p, some c => if p.line == c.line then lineStart cs fuel j else j + 1
      | _, _ => j + 1

/-- The last cell of the line of cell `i` (moving right at most `fuel` cells). -/
def lineEnd (cs : Array Cell) : Nat → Nat → Nat
  | 0, i => i
  | fuel + 1, i =>
    match cs[i]?, cs[i + 1]? with
    | some c, some n => if c.line == n.line then lineEnd cs fuel (i + 1) else i
    | _, _ => i

/-- The selection bands of the cells `a … b` (inclusive), one per line in reading order (see
the section doc); `dirs` gives each line's direction (`PageIndex.lineDirs`, missing: 0). -/
def selBands (cs : Array Cell) (dirs : Array Nat) (a b : Nat) : List Box :=
  if cs.size == 0 then [] else
  let lo := min a b
  let hi := min (max a b) (cs.size - 1)
  let sel := (lineRuns cs lo hi).toArray
  let full := lineRuns cs (lineStart cs lo lo) (lineEnd cs cs.size hi)
  let n := sel.size
  let horiz (l : Nat) : Bool := dirs[l]?.getD 0 == 0
  let fullOf (l : Nat) : Option (Nat × Nat × Box) := full.find? (·.1 == l)
  let shaped : Array Box := sel.mapIdx fun k r =>
    match horiz r.1, fullOf r.1 with
    | true, some (_, _, f) => shape (k == 0) (k + 1 == n) f r.2.2
    | _, _ => r.2.2
  let ok (k : Nat) : Bool :=
    match sel[k]?, sel[k + 1]? with
    | some (l0, _, _), some (l1, _, _) =>
      horiz l0 && horiz l1 &&
        ((fullOf l1).bind fun (_, i, _) => cs[i]?.map (·.sep == "\n")).getD false
    | _, _ => false
  (List.range n).filterMap (bandAt shaped ok)

/-- Every selected glyph box lies inside one of the selection bands (checked by `#guard`s;
the parts are `shape_covers` and `bandAt_covers`). -/
def bandsCover (cs : Array Cell) (dirs : Array Nat) (a b : Nat) : Bool :=
  let bs := selBands cs dirs a b
  (List.range (max a b + 1 - min a b)).all fun k =>
    match cs[min a b + k]? with
    | some c => bs.any fun band => decide (Box.inside c.box band)
    | none => true

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
  /-- The direction (`Line.dir`) of each line, by `Cell.line` (for `selBands`). -/
  lineDirs : Array Nat
  /-- Task 12.5: whether each cell's glyph is one the page does not paint (`Tr 3`/`Tr 7`,
  `Glyph.visible` false), by cell index (`cellsHidden`). -/
  hidden : Array Bool := #[]
  deriving Inhabited

/-- Task 12.5: for each cell of `cellsOf o lines`, in the same order, whether its glyph is not
painted by the page (`Glyph.visible` false). Glyphs outside the CropBox and glyphs the clip
hides are not in `lines` at all (`Text.Options.keeps_hiddenWhy`, `Text.unclipped`). -/
def cellsHidden (o : Options) (lines : Array Line) : Array Bool :=
  lines.foldl (fun acc l => acc ++ ((Text.lineOrder o l).map fun g => !g.visible).toArray) #[]

/-- The index of a page's cells, line directions and hidden flags (as the worker sends them,
task 12.2d), with the normalised search text computed from the cells (`normChars`). -/
def PageIndex.ofCells (cells : Array Cell) (lineDirs : Array Nat) (hidden : Array Bool) :
    PageIndex :=
  { cells, hay := normChars cells, lineDirs, hidden }

/-- The index of an extracted page (default layout options, as the text view). -/
def PageIndex.ofText (pt : Text.PageText) : PageIndex :=
  PageIndex.ofCells (cellsOf {} pt.lines) (pt.lines.map (·.dir)) (cellsHidden {} pt.lines)

/-- Task 12.5: the number of characters of `rangeText ix.cells a b` that come from glyphs the
page does not paint (separators not counted). -/
def PageIndex.hiddenChars (ix : PageIndex) (a b : Nat) : Nat :=
  let lo := min a b
  let hi := min (max a b) (ix.cells.size - 1)
  (List.range (hi + 1 - lo)).foldl (fun n k =>
    match ix.cells[lo + k]?, ix.hidden[lo + k]? with
    | some c, some true => n + c.text.length
    | _, _ => n) 0

/-- The selection bands of the cells `a … b` on this page (`selBands`). -/
def PageIndex.bands (ix : PageIndex) (a b : Nat) : List Box := selBands ix.cells ix.lineDirs a b

/-- The hits of `q` on a page, as cell ranges. -/
def PageIndex.hits (ix : PageIndex) (q : Array Char) : Array (Nat × Nat) :=
  ((findAll ix.hay q).map (hitRange ix.hay q.size)).toArray

/-- The line of cell `i` (triple click): its first and last cell (`lineStart`, `lineEnd`). -/
def lineAt (cs : Array Cell) (i : Nat) : Nat × Nat :=
  (lineStart cs i i, lineEnd cs cs.size i)

/-- The status after a copy of `n` characters, `hidden` of them from glyphs the page does not
paint (task 12.5): the copy keeps invisible text — an OCR layer over a scan is the text of the
page — but says how much of it the page does not show, so text hidden from the reader (a
prompt or a payload) never reaches the clipboard unannounced. -/
def copyStatus (n hidden : Nat) : String :=
  if hidden == 0 then s!"copied {n} characters"
  else s!"copied {n} characters; the copied text includes {hidden} characters that are not \
    visible on the page (invisible text, e.g. an OCR layer)"

/-! ## The search loop (the viewer's `nextHit`)

Find Next / Find Previous look at the current page first (the hit after, or before, the
current one), then at the other pages in order (`searchPages`, wrapping around to the current
page), stopping at the first page with a hit: its first hit going forward, its last going
backward. The viewer (`Viewer.nextHit`) runs this order with the worker's page indices and a
work allowance; `searchStep` is the same order over the hit counts known so far, for a caller
that fetches page indices itself. -/

/-- The hit to show on the current page, which has `c` hits: the one after (`forward`) or
before the current hit `cur` (an index on this page), or the first (last) one without a
current hit; `none` when there is no such hit on this page. -/
def hitOnCurrent (c : Nat) (cur : Option Nat) (forward : Bool) : Option Nat :=
  let cand := if forward then some ((cur.map (· + 1)).getD 0)
    else match cur with
      | some k => if k > 0 then some (k - 1) else none
      | none => if c > 0 then some (c - 1) else none
  match cand with
  | some k => if k < c then some k else none
  | none => none

/-- The pages a search visits after the current page `page` of `n`, in order: the following
(`forward`) or preceding pages, wrapping around, ending with `page` itself. -/
def searchPages (n page : Nat) (forward : Bool) : List Nat :=
  (List.range n).map fun j =>
    let i := j + 1
    if forward then (page + i) % n else (page + n - i % n) % n

/-- The hit shown on another page with `c > 0` hits: its first going forward, its last
backward. -/
def firstHitOn (forward : Bool) (c : Nat) : Nat := if forward then 0 else c - 1

/-- Whether reaching page `p` from page `page` wrapped around the document. -/
def wrappedTo (forward : Bool) (page p : Nat) : Bool := if forward then p ≤ page else p ≥ page

/-- One step of a search over the hit counts known so far. -/
inductive SearchStep where
  /-- The next hit: page, index of the hit on that page, hits on that page, wrapped around. -/
  | hit (p k c : Nat) (wrapped : Bool)
  /-- The hit count of page `p` is needed first (fetch its index, then step again). -/
  | need (p : Nat)
  /-- No hit in the document. -/
  | none
  deriving Repr, BEq, Inhabited

/-- **One step of the search** (`Viewer.nextHit`'s order): `counts[p]` is page `p`'s number of
hits (`some 0` for a page without text or whose index failed), `none` while its index is not
known; `cur` the current hit's index when it is on `page`. -/
def searchStep (counts : Array (Option Nat)) (page : Nat) (cur : Option Nat) (forward : Bool) :
    SearchStep :=
  let rest : SearchStep :=
    let r := (searchPages counts.size page forward).findSome? fun p =>
      match counts[p]? with
      | some (some c) => if c > 0 then some (SearchStep.hit p (firstHitOn forward c) c
          (wrappedTo forward page p)) else Option.none
      | some Option.none => some (SearchStep.need p)
      | Option.none => Option.none
    r.getD .none
  match counts[page]? with
  | some Option.none => .need page
  | some (some c) =>
    match hitOnCurrent c cur forward with
    | some k => .hit page k c false
    | Option.none => rest
  | Option.none => rest

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
  { fonts := [], items := #[], glyphs := sample, shown := sample,
    lines := (Text.layout {} sample).1, text := "",
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
-- Selection bands (10.18): "World" to the line end (166, past the overprint), the next line
-- from its start to "Ze"; the 2-point gap closed at 697; "end" after a paragraph break is
-- not joined (its own height, 598–608).
#guard selBands sampleCells #[0, 0, 0] 6 12 == [⟨140, 697, 166, 708⟩, ⟨100, 686, 111, 697⟩]
#guard selBands sampleCells #[0, 0, 0] 2 17 ==
  [⟨112, 697, 166, 708⟩, ⟨100, 686, 125, 697⟩, ⟨100, 598, 110, 608⟩]
#guard selBands sampleCells #[0, 0, 0] 17 2 == selBands sampleCells #[0, 0, 0] 2 17
-- A single-line selection: from the start glyph to the end glyph, the line's full height.
#guard selBands sampleCells #[0, 0, 0] 1 2 == [⟨107, 698, 115, 708⟩]
#guard selBands sampleCells #[] 0 100 == selBands sampleCells #[0, 0, 0] 0 18
#guard selBands #[] #[] 0 3 == []
#guard (List.range 19).all fun a => (List.range 19).all fun b => bandsCover sampleCells #[0, 0, 0] a b
-- Copy is unchanged by the drawing.
#guard rangeText sampleCells 2 17 == "llo World\nZebra\n\nen"

/-- Three lines of one paragraph (baselines 700, 688, 676, size 10; widths 15, 25, 10). -/
private def para : List Glyph :=
  [mkG "a" 100 700 5, mkG "b" 105 700 5, mkG "c" 110 700 5,
   mkG "d" 100 688 5, mkG "e" 105 688 5, mkG "f" 110 688 5, mkG "g" 115 688 5, mkG "h" 120 688 5,
   mkG "i" 100 676 5, mkG "j" 105 676 5]

private def paraCells : Array Cell := cellsOf {} (Text.layout {} para).1

-- Interior line: its full width and height, meeting both neighbours (685 and 697).
#guard selBands paraCells #[0, 0, 0] 1 8 ==
  [⟨105, 697, 115, 708⟩, ⟨100, 685, 125, 697⟩, ⟨100, 674, 105, 685⟩]
#guard (List.range 10).all fun a => (List.range 10).all fun b => bandsCover paraCells #[0, 0, 0] a b
-- Consecutive bands touch: each band's bottom is the next one's top.
#guard let bs := selBands paraCells #[0, 0, 0] 0 9
  (bs.zip bs.tail).all fun (u, w) => u.lly == w.ury
-- A gap larger than a line height is never joined, even within one layout paragraph (lines 40
-- apart with a paragraph gap of 10000 ‰, so the layout keeps a plain line break).
#guard selBands (cellsOf { paraGap := 10000 } (Text.layout { paraGap := 10000 }
  [mkG "a" 100 700 5, mkG "b" 100 660 5]).1) #[0, 0] 0 1 == [⟨100, 698, 105, 708⟩, ⟨100, 658, 105, 668⟩]
-- Vertical text (direction 1) keeps the selected glyphs' run boxes and is never joined.
#guard selBands paraCells #[1, 1, 1] 1 8 == rangeBoxes paraCells 1 8
#guard selBands paraCells #[0, 1, 0] 1 8 ==
  [⟨105, 698, 115, 708⟩, ⟨100, 686, 125, 696⟩, ⟨100, 674, 105, 684⟩]
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
-- Task 12.5: invisible (`Tr 3`) glyphs are counted by the copy's hidden-character count.
private def ocrSample : List Glyph :=
  sample.take 5 ++ ((sample.drop 5).take 5).map fun g => { g with visible := false }
private def ocrPT : Text.PageText :=
  { samplePT with glyphs := ocrSample, shown := ocrSample, lines := (Text.layout {} ocrSample).1 }
#guard (PageIndex.ofText ocrPT).hidden.size == (PageIndex.ofText ocrPT).cells.size
#guard (PageIndex.ofText ocrPT).hiddenChars 0 100 == 5
#guard (PageIndex.ofText ocrPT).hiddenChars 0 4 == 0
#guard (PageIndex.ofText ocrPT).hiddenChars 7 5 == 3
#guard (PageIndex.ofText samplePT).hiddenChars 0 100 == 0
#guard rangeText (PageIndex.ofText ocrPT).cells 0 100 == "Hello World"
#guard copyStatus 5 0 == "copied 5 characters"
#guard copyStatus 11 3 == "copied 11 characters; the copied text includes 3 characters that are \
  not visible on the page (invisible text, e.g. an OCR layer)"
-- Triple click: the whole line of a cell.
#guard lineAt sampleCells 7 == (0, 10) && lineAt sampleCells 12 == (11, 15) &&
  lineAt sampleCells 17 == (16, 18) && lineAt sampleCells 0 == (0, 10)
-- The search loop's page order and steps.
#guard searchPages 5 2 true == [3, 4, 0, 1, 2] && searchPages 5 2 false == [1, 0, 4, 3, 2]
#guard searchPages 0 0 true == []
#guard hitOnCurrent 3 (some 1) true == some 2 && hitOnCurrent 3 (some 2) true == none &&
  hitOnCurrent 3 none false == some 2 && hitOnCurrent 3 (some 0) false == none &&
  hitOnCurrent 0 none true == none
#guard searchStep #[some 2, none, some 0, some 1] 0 (some 1) true == .need 1
#guard searchStep #[some 2, some 0, some 0, some 1] 0 (some 1) true == .hit 3 0 1 false
#guard searchStep #[some 2, some 0, some 0, some 1] 3 (some 0) true == .hit 0 0 2 true
#guard searchStep #[some 2, some 0, some 0, some 1] 0 none false == .hit 0 1 2 false
#guard searchStep #[some 2, some 0, some 0, some 1] 0 (some 0) false == .hit 3 0 1 true
#guard searchStep #[some 1, some 0] 0 (some 0) true == .hit 0 0 1 true
#guard searchStep #[none, some 4] 0 none true == .need 0
#guard searchStep #[some 0, some 0] 1 none true == .none
#guard searchStep #[] 0 none true == .none

end SafePdf.Shell.App.Select
