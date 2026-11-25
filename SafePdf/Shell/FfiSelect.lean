import SafePdf.Shell.App.Select
import SafePdf.Shell.App.Links
import SafePdf.Shell.App.Budget
import SafePdf.Shell.FfiMarks

/-!
# C API v2: text selection, copy and search (task 11.3a4; Plan.md §4 C3, §6 Phases 8–11)

The viewer's selection and search (`Shell.App.Select`) exported for the native macOS shell
(`docs/macos-design.md` §3, decision 1: whatever has a theorem or a `#guard` stays in Lean and
crosses as a pure function; decision 2: flat C structs). `macos/safepdf_select.c` wraps these
`@[export safepdf_select_lean_…]` functions into the plain C API of `macos/safepdf_select.h`.
Every export **calls** the function the Tk viewer (`Shell.App.Viewer`) calls on the same user
action; nothing is re-implemented:

* **The page handle** (`pageNew`): a `safepdf_page_index` (the worker's `pageIndex` answer,
  as `safepdf_doc_page_index` delivers it) converted once into a `Select.PageIndex` by
  `Select.PageIndex.ofCells` — the same constructor `Viewer.indexOfReply` uses for the worker's
  reply (the normalised search text is computed here, `Select.normChars`). The handle is an
  immutable Lean value, so hit tests during a drag never re-marshal the cells.
* **Pointer**: `Select.nearest` (hit test), `Select.dragRange` (drag), `Select.wordAt` (double
  click), `Select.lineAt` (triple click: the line's `lineStart`/`lineEnd`).
* **Drawing**: `Select.selBands` (the selection bands of task 10.18; `shape_covers`,
  `bandAt_covers`, `bandAt_meet`) and `Select.rangeBoxes` (one box per line run: search hits,
  highlight quads).
* **Copy**: `Select.rangeText`, `PageIndex.hiddenChars` and `Select.copyStatus` (task 12.5:
  invisible text is copied and counted in the status).
* **Search**: `Select.normQuery`, `PageIndex.hits` (`findAll`, sound by `findAll_sound`;
  `hitRange`), over one page or over the pages of a document whose indices the caller has
  (highlight-all), and `Select.searchStep` (Find Next/Previous: `Viewer.nextHit`'s order over
  the hit counts known so far; the caller fetches the index a step asks for).
* **Pointer and links** (task 11.3d1, the gaps the native page view needed): the cursor's text
  test (`Viewer.pointerHit`: a glyph box contains the point, `Links.Box.contains`), the link
  under a point (`Links.linkAt`, the topmost one) and its status text (`Links.describe`), and
  the search's work allowance (`Budget.Allowance.start` / `spend` with `Budget.ceilings`, task
  12.3), so Find Next stops after the same number of pages and seconds as `Viewer.nextHit`.

**Numbers.** Coordinates cross as `Float`s. Into Lean they become exact rationals
(`FfiMarks.ratOfFloat`; a box coordinate it refuses — beyond ±2³², infinite, NaN — is clamped
to ±2³², NaN to 0, `coord`; a refused pointer coordinate means "no point"). Out of Lean they
are display doubles (`FfiMarks.toF`), counts and indices are `Float`s (exact below 2⁵³).
Calling convention as `Shell.FfiMarks`: every object argument is owned (Lean v4.36 rejects
`@&` on exports), every result is owned by the caller.
-/

namespace SafePdf.Shell.FfiSelect

open SafePdf.Core.Raster.Geom (Pt Box)
open SafePdf.Shell.App.Select
open SafePdf.Shell.FfiMarks (ratOfFloat toF natF satU)

/-! ## Numbers across the boundary -/

/-- A box coordinate from C as a rational: exact (`ratOfFloat`), else clamped to ±2³² (NaN: 0). -/
def coord (f : Float) : Rat :=
  match ratOfFloat f with
  | some q => q
  | none => if f.isNaN then 0 else if f > 0 then 4294967296 else -4294967296

/-- A count or index from C (`Float`): negative or NaN values are 0. -/
def natOf (f : Float) : Nat := if f > 0 then f.toUInt64.toNat else 0

/-- A pointer position from C; `none` when a coordinate is refused (`ratOfFloat`). -/
def ptOf (x y : Float) : Option Pt :=
  match ratOfFloat x, ratOfFloat y with
  | some x, some y => some ⟨x, y⟩
  | _, _ => none

/-- Boxes as four `Float`s each (`llx lly urx ury`). -/
def boxesF (bs : List Box) : List Float :=
  bs.flatMap fun b => [toF b.llx, toF b.lly, toF b.urx, toF b.ury]

/-- A cell range as two `Float`s. -/
def rangeF (r : Nat × Nat) : List Float := [natF r.1, natF r.2]

#guard coord 1.5 == 3 / 2 && coord (1.0 / 0.0) == 4294967296 && coord (0.0 / 0.0) == 0
#guard natOf (-3.0) == 0 && natOf 7.0 == 7

/-! ## The page handle -/

/-- **A page's selection handle** from the flat `safepdf_page_index`: `nums` holds six numbers
per cell (box `llx lly urx ury`, line, hidden flag) followed by one direction per line; `strs`
two strings per cell (text, separator). Built with `PageIndex.ofCells`, as the viewer builds
the worker's reply. An error when the sizes disagree with `nCells`/`nLines`. -/
@[export safepdf_select_lean_page_new]
def pageNew (nums : FloatArray) (strs : Array String) (nCells nLines : USize) :
    Except String PageIndex :=
  let n := nCells.toNat
  let m := nLines.toNat
  if nums.size != 6 * n + m || strs.size != 2 * n then .error "malformed page index"
  else
    let g (i : Nat) : Float := (nums[i]?).getD 0
    let cells := (Array.range n).map fun i =>
      ({ text := (strs[2 * i]?).getD "", sep := (strs[2 * i + 1]?).getD "",
         box := ⟨coord (g (6 * i)), coord (g (6 * i + 1)), coord (g (6 * i + 2)),
           coord (g (6 * i + 3))⟩,
         line := natOf (g (6 * i + 4)) } : Cell)
    let hidden := (Array.range n).map fun i => g (6 * i + 5) != 0
    let dirs := (Array.range m).map fun j => natOf (g (6 * n + j))
    .ok (PageIndex.ofCells cells dirs hidden)

/-- Number of cells of a page. -/
@[export safepdf_select_lean_cell_count]
def cellCount (h : PageIndex) : USize := satU h.cells.size

/-! ## Pointer: hit test, drag, word, line -/

/-- `Select.nearest` at page point `(x, y)`: `i + 1` for cell `i`, `0` for none (no cells, or
a refused coordinate). -/
@[export safepdf_select_lean_nearest]
def nearest (h : PageIndex) (x y : Float) : USize :=
  match ptOf x y with
  | some p => match App.Select.nearest h.cells p with
    | some i => satU (i + 1)
    | none => 0
  | none => 0

/-- `Select.dragRange` from `(x0, y0)` to `(x1, y1)`. Out: found flag, first, last. -/
@[export safepdf_select_lean_drag]
def drag (h : PageIndex) (x0 y0 x1 y1 : Float) : FloatArray :=
  match ptOf x0 y0, ptOf x1 y1 with
  | some p, some q => match dragRange h.cells p q with
    | some r => ⟨#[1] ++ (rangeF r).toArray⟩
    | none => ⟨#[0, 0, 0]⟩
  | _, _ => ⟨#[0, 0, 0]⟩

/-- `Select.wordAt` (double click). Out: first, last. -/
@[export safepdf_select_lean_word_at]
def wordAtW (h : PageIndex) (i : USize) : FloatArray := ⟨(rangeF (wordAt h.cells i.toNat)).toArray⟩

/-- `Select.lineAt` (triple click). Out: first, last. -/
@[export safepdf_select_lean_line_at]
def lineAtW (h : PageIndex) (i : USize) : FloatArray := ⟨(rangeF (lineAt h.cells i.toNat)).toArray⟩

/-! ## Drawing and copy -/

/-- `Select.selBands` of the cells `a … b` (`PageIndex.bands`). Out: four numbers per band. -/
@[export safepdf_select_lean_bands]
def bands (h : PageIndex) (a b : USize) : FloatArray := ⟨(boxesF (h.bands a.toNat b.toNat)).toArray⟩

/-- `Select.rangeBoxes` of the cells `a … b`. Out: four numbers per box. -/
@[export safepdf_select_lean_range_boxes]
def rangeBoxesW (h : PageIndex) (a b : USize) : FloatArray :=
  ⟨(boxesF (rangeBoxes h.cells a.toNat b.toNat)).toArray⟩

/-- **Copy** of the cells `a … b` (as `Viewer.copySel`): the text (`Select.rangeText`) and the
status (`Select.copyStatus` of its length and `PageIndex.hiddenChars`). Out: (text, status),
(characters, hidden characters). -/
@[export safepdf_select_lean_copy]
def copy (h : PageIndex) (a b : USize) : Array String × FloatArray :=
  let t := rangeText h.cells a.toNat b.toNat
  let hid := h.hiddenChars a.toNat b.toNat
  (#[t, copyStatus t.length hid], ⟨#[natF t.length, natF hid]⟩)

/-! ## Search -/

/-- `Select.normQuery` as a string (the query the status line shows). -/
@[export safepdf_select_lean_norm_query]
def normQueryW (q : String) : String := String.ofList (normQuery q).toList

/-- Number of hits of query `q` on a page (`PageIndex.hits` of `normQuery q`). -/
@[export safepdf_select_lean_count]
def count (h : PageIndex) (q : String) : USize := satU (h.hits (normQuery q)).size

/-- The hits of `q` on a page with their highlight boxes: per hit first, last, number of boxes,
the boxes (`rangeBoxes`). -/
def pageHits (h : PageIndex) (q : Array Char) : Array (Nat × Nat × List Box) :=
  (h.hits q).map fun (a, b) => (a, b, rangeBoxes h.cells a b)

/-- A hit on the wire: first, last, number of boxes, the boxes. -/
def hitF (a b : Nat) (bs : List Box) : List Float :=
  [natF a, natF b, natF bs.length] ++ boxesF bs

/-- **The hits of `q` on a page**. Out: hit count, then per hit `hitF`. -/
@[export safepdf_select_lean_find]
def find (h : PageIndex) (q : String) : FloatArray :=
  let hs := pageHits h (normQuery q)
  ⟨(natF hs.size :: hs.toList.flatMap fun (a, b, bs) => hitF a b bs).toArray⟩

/-- **The hits of `q` on every page whose index is given** (highlight-all; `none`: a page whose
index the caller does not have, skipped). Out: hit count, then per hit its page and `hitF`. -/
@[export safepdf_select_lean_find_doc]
def findDoc (hs : Array (Option PageIndex)) (q : String) : FloatArray :=
  let nq := normQuery q
  let all := (hs.mapIdx fun p o => match o with
    | some h => (pageHits h nq).map fun (a, b, bs) => (p, a, b, bs)
    | none => #[]).flatten
  ⟨(natF all.size :: all.toList.flatMap fun (p, a, b, bs) => natF p :: hitF a b bs).toArray⟩

/-- **Find Next / Previous** (`Select.searchStep`): `counts` one number per page, its hit count
(negative: not known yet); `cur` `k + 1` for the current hit `k` on `page`, `0` for none. Out:
kind (0 hit, 1 need the index of a page, 2 no hit), page, hit index, hits on that page,
wrapped flag. -/
@[export safepdf_select_lean_next_hit]
def nextHit (counts : FloatArray) (page cur : USize) (forward : UInt8) : FloatArray :=
  let cs : Array (Option Nat) := counts.data.map fun f => if f < 0 then none else some (natOf f)
  let cur := if cur == 0 then none else some (cur.toNat - 1)
  match searchStep cs page.toNat cur (forward != 0) with
  | .hit p k c w => ⟨#[0, natF p, natF k, natF c, if w then 1 else 0]⟩
  | .need p => ⟨#[1, natF p, 0, 0, 0]⟩
  | .none => ⟨#[2, 0, 0, 0, 0]⟩

-- A page "ab c" on one line (boxes 10 wide at x = 0, 10, 30), then the round trip of the
-- exports a drag, a double click, a copy and a search make.
private def tiny : Except String PageIndex :=
  pageNew ⟨#[0, 0, 10, 10, 0, 0, 10, 0, 20, 10, 0, 0, 30, 0, 40, 10, 0, 1, 0]⟩
    #["a", "", "b", "", "c", " "] 3 1

#guard match tiny with
  | .ok h => cellCount h == 3 && nearest h 35 5 == 3 && nearest h 1 1 == 1 &&
      nearest h (0.0 / 0.0) 1 == 0 &&
      (drag h 35 5 1 1).data == #[1, 0, 2] && (wordAtW h 0).data == #[0, 1] &&
      (lineAtW h 1).data == #[0, 2] && (copy h 0 2).1 == #["ab c", copyStatus 4 1] &&
      (copy h 0 2).2.data == #[4, 1] && count h "B C" == 1 && normQueryW "  B  C " == "b c" &&
      (find h "b").data == #[1, 1, 1, 1, 10, 0, 20, 10] &&
      (findDoc #[some h, none, some h] "c").data ==
        #[2, 0, 2, 2, 1, 30, 0, 40, 10, 2, 2, 2, 1, 30, 0, 40, 10] &&
      (bands h 0 2).data == #[0, 0, 40, 10]
  | .error _ => false
#guard match pageNew ⟨#[1]⟩ #[] 0 0 with
  | .error _ => true
  | .ok _ => false
#guard (nextHit ⟨#[2, -1, 0]⟩ 0 2 1).data == #[1, 1, 0, 0, 0]
#guard (nextHit ⟨#[2, 0, 1]⟩ 0 2 1).data == #[0, 2, 0, 1, 0]
#guard (nextHit ⟨#[0, 0]⟩ 0 0 1).data == #[2, 0, 0, 0, 0]

/-! ## Pointer and links (task 11.3d1) -/

/-- **Whether page point `(x, y)` lies in a glyph box** (the cursor's text test of
`Viewer.pointerHit`: `cells.any (Links.Box.contains ·.box p)`). `1` yes, `0` no (or a refused
coordinate). -/
@[export safepdf_select_lean_over_text]
def overText (h : PageIndex) (x y : Float) : UInt8 :=
  match ptOf x y with
  | some p => if h.cells.any (fun c => App.Links.Box.contains c.box p) then 1 else 0
  | none => 0

/-- Links from four `Float`s per box (`llx lly urx ury`); the action plays no part in
`Links.linkAt`. -/
def linksOfBoxes (boxes : FloatArray) : Array App.Links.Link :=
  let g (i : Nat) : Float := (boxes[i]?).getD 0
  (Array.range (boxes.size / 4)).map fun i =>
    { box := ⟨coord (g (4 * i)), coord (g (4 * i + 1)), coord (g (4 * i + 2)),
        coord (g (4 * i + 3))⟩, action := .none }

/-- **The link at page point `(x, y)`** (`Links.linkAt`: the topmost, last in `/Annots`
order, whose rectangle contains the point). `i + 1` for link `i`, `0` for none. -/
@[export safepdf_select_lean_link_at]
def linkAtW (boxes : FloatArray) (x y : Float) : USize :=
  match ptOf x y with
  | some p => match App.Links.linkAt (linksOfBoxes boxes) p with
    | some (i, _) => satU (i + 1)
    | none => 0
  | none => 0

/-- An action from C (`safepdf_action_kind`: 0 go to `page`, 1 URI, 2 page not in the
document, 3 unresolved name, 4 other action type, else none). The destination's position plays
no part in `Links.describe`. -/
def actionOfC (kind page : USize) (text : String) : App.Links.Action :=
  match kind.toNat with
  | 0 => .goto { page := page.toNat }
  | 1 => .uri text
  | 2 => .badPage
  | 3 => .unresolved text
  | 4 => .other text
  | _ => .none

/-- **A link's status text** (`Links.describe`, as the Tk viewer's hover and activation show
it), with the page labels `labels` of an `n`-page document. -/
@[export safepdf_select_lean_link_describe]
def describeW (kind page : USize) (text : String) (labels : Array String) (n : USize) : String :=
  App.Links.describe labels n.toNat (actionOfC kind page text)

/-- **The search's work allowance at time `now`** (ms; `Budget.Allowance.start` of
`Budget.ceilings`). Out: pages, end time (ms). -/
@[export safepdf_select_lean_allowance_start]
def allowanceStart (now : UInt64) : FloatArray :=
  let a := App.Budget.Allowance.start App.Budget.ceilings now.toNat
  ⟨#[natF a.pages, natF a.endsAt]⟩

/-- **Spend one page of an allowance at time `now`** (`Budget.Allowance.spend`). Out: spent
flag, pages, end time (unchanged when used up). -/
@[export safepdf_select_lean_allowance_spend]
def allowanceSpend (pages endsAt now : UInt64) : FloatArray :=
  match (App.Budget.Allowance.mk pages.toNat endsAt.toNat).spend now.toNat with
  | some a => ⟨#[1, natF a.pages, natF a.endsAt]⟩
  | none => ⟨#[0, natF pages.toNat, natF endsAt.toNat]⟩

#guard match tiny with
  | .ok h => overText h 5 5 == 1 && overText h 25 5 == 0 && overText h (0.0 / 0.0) 5 == 0
  | .error _ => false
#guard linkAtW ⟨#[0, 0, 10, 10, 5, 5, 20, 20]⟩ 6 6 == 2 &&
  linkAtW ⟨#[0, 0, 10, 10, 5, 5, 20, 20]⟩ 1 1 == 1 && linkAtW ⟨#[0, 0, 10, 10]⟩ 11 1 == 0
#guard describeW 0 2 "" #["i", "ii", "1"] 3 == "go to page 1 (3/3)" &&
  describeW 1 0 "http://x" #[] 1 == "external link (click to copy the address): http://x" &&
  describeW 4 0 "Launch" #[] 1 == "link action /Launch (not followed)"
#guard (allowanceStart 5).data == #[natF App.Budget.ceilings.searchPages,
  natF (5 + App.Budget.ceilings.searchMs)]
#guard (allowanceSpend 2 100 50).data == #[1, 1, 100] && (allowanceSpend 0 100 50).data == #[0, 0, 100] &&
  (allowanceSpend 2 100 100).data == #[0, 2, 100]

end SafePdf.Shell.FfiSelect
