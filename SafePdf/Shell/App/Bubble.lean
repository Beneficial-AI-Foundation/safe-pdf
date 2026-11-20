import SafePdf.Shell.App.Menu
import SafePdf.Shell.App.Marks

/-!
# Selection bubble and Highlight pop-over after PDF.js (task 9.8; Plan.md §6 Phase 9 "Look and feel: imitate PDF.js" — *Selection bubble*, *Toolbar, right*; §10 `SafePdf/Shell/`)

The Tk-free logic of the floating toolbars of the viewer (unverified shell code, total,
checked by `#guard`s and small theorems). The design reference is PDF.js, Firefox's viewer
(Mozilla, Apache-2.0; `src/display/editor/toolbar.js` `FloatingToolbar` / `EditorToolbar`,
`src/display/editor/color_picker.js`, `web/annotation_editor_layer_builder.css`
`.editToolbar`, `.colorPicker`, `#highlightParamsToolbarContainer`); `Viewer` re-draws it
with Tk canvas items, nothing of PDF.js is copied.

* **Bubbles** (`Kind`): after a text selection, the *float* bubble with one Highlight button
  (PDF.js's highlight floating button); on a selected highlight, the *edit* bubble: a colour
  swatch with a chevron (`Btn.color`, opens the colour picker), Comment and Delete, separated
  by dividers. Sizes from PDF.js's CSS: 28 px buttons, 2 px padding, 1 px border, dividers
  with 2 px margins, the colour button 4 + 16 + 4 + 12 + 4 px.
* **Placement** (`place`): as PDF.js, the bubble's right edge is at the *last point* of the
  selection (`lastPoint`: the right end of the lowest line box, `#getLastPoint`) and its top
  `gap` (6 px, `--editor-toolbar-vert-offset`) below it; when it would leave the area (the
  canvas scroll region) at the bottom it goes above the selection; then it is clamped into
  the area (`place_inside`). Coordinates are canvas pixels (y down), so the bubble follows
  scrolling; the viewer places it again after every zoom, rotation and page change.
* **Colour picker** (`pickerRect`, `pickerHit`): the drop-down under the colour button, the
  five swatches in a column (PDF.js `.dropdown`: 8 px padding, 16 px swatches, 11 px gap);
  above the bubble when it does not fit below.
* **Highlight pop-over** (`Popover`): "Highlight color" with five 24 px swatches (the current
  one ringed), "Thickness" slider 8–24 (PDF.js `editorFreeHighlightThickness`, default 12;
  used by free highlights, a later task — the value is kept), a divider, and the "Show all"
  switch. `Popover.hit` maps a click to its part; `thicknessAt` maps a slider position to a
  value (clamped) and `thumbX` back (`thicknessAt_thumbX`).
* **Tool state** (`Ui`): whether the Highlight tool is active (then a mouse-up that selects
  text highlights it at once, `Ui.highlightOnRelease`, PDF.js behaviour), whether the
  pop-over and the colour picker are open, the thickness and "Show all". The toolbar button
  highlights a selection when there is one (as since 9.4), else toggles the tool and its
  pop-over (`Ui.toolClick`); Escape closes the picker and the pop-over (`Ui.escape`).
* **Commands**: the bubble buttons run `Menu.Cmd` scripts (`Btn.cmd?`: Highlight
  selection, Add note…, Delete mark), so menubar, keys and bubbles share one vocabulary.
-/

namespace SafePdf.Shell.App.Bubble

open Marks (Color)

/-! ## Rectangles (canvas pixels, y down) -/

/-- A rectangle in canvas pixels: left, top, right, bottom. -/
structure Rect where
  /-- Left. -/
  x0 : Rat
  /-- Top. -/
  y0 : Rat
  /-- Right. -/
  x1 : Rat
  /-- Bottom. -/
  y1 : Rat
  deriving DecidableEq, Repr, Inhabited

/-- Whether the point `(x, y)` lies in `r` (borders included). -/
def Rect.contains (r : Rect) (x y : Rat) : Bool :=
  decide (r.x0 ≤ x) && decide (x ≤ r.x1) && decide (r.y0 ≤ y) && decide (y ≤ r.y1)

/-- Smallest rectangle containing both. -/
def Rect.union (a b : Rect) : Rect :=
  ⟨min a.x0 b.x0, min a.y0 b.y0, max a.x1 b.x1, max a.y1 b.y1⟩

/-- Union of a list of rectangles (`none` for the empty list). -/
def unionAll : List Rect → Option Rect
  | [] => none
  | r :: rs => some (rs.foldl Rect.union r)

/-- PDF.js's `#getLastPoint` for left-to-right text: the right end of the lowest box
(largest bottom; among equal bottoms the rightmost). -/
def lastPoint (rs : List Rect) : Option (Rat × Rat) :=
  rs.foldl (fun acc r =>
    match acc with
    | none => some (r.x1, r.y1)
    | some (x, y) =>
      if y < r.y1 then some (r.x1, r.y1)
      else if r.y1 == y && x < r.x1 then some (r.x1, y)
      else acc) none

/-- Vertical distance between the selection and the bubble (`--editor-toolbar-vert-offset`). -/
def gap : Rat := 6

/-- `v` moved so that `[v, v + s]` lies in `[lo, hi]` when it fits (else `lo`). -/
def clampInto (lo hi s v : Rat) : Rat :=
  if hi - lo < s then lo else max lo (min v (hi - s))

/-- `clampInto` never goes below `lo`. -/
theorem clampInto_lo (lo hi s v : Rat) : lo ≤ clampInto lo hi s v := by
  unfold clampInto
  rw [Rat.max_def, Rat.min_def]
  split <;> (try split) <;> (try split) <;> grind

/-- When `s` fits, `[clampInto …, clampInto … + s]` ends at or before `hi`. -/
theorem clampInto_hi (lo hi s v : Rat) (h : s ≤ hi - lo) : clampInto lo hi s v + s ≤ hi := by
  unfold clampInto
  rw [Rat.max_def, Rat.min_def]
  split <;> (try split) <;> (try split) <;> grind

/-- Where a bubble of `w × h` pixels goes for the selection boxes `sel` inside `area`: right
edge at the last point, top `gap` below it (above the selection when it does not fit below),
clamped into `area`. `none` without boxes. -/
def place (sel : List Rect) (w h : Rat) (area : Rect) : Option Rect := do
  let (lx, ly) ← lastPoint sel
  let u ← unionAll sel
  let y := if ly + gap + h ≤ area.y1 then ly + gap else u.y0 - gap - h
  let x := clampInto area.x0 area.x1 w (lx - w)
  let y := clampInto area.y0 area.y1 h y
  some ⟨x, y, x + w, y + h⟩

/-- A placed bubble lies inside the area when the area is large enough. -/
theorem place_inside (sel : List Rect) (w h : Rat) (area r : Rect)
    (hw : w ≤ area.x1 - area.x0) (hh : h ≤ area.y1 - area.y0)
    (hp : place sel w h area = some r) :
    area.x0 ≤ r.x0 ∧ r.x1 ≤ area.x1 ∧ area.y0 ≤ r.y0 ∧ r.y1 ≤ area.y1 := by
  unfold place at hp
  cases hl : lastPoint sel with
  | none => simp [hl] at hp
  | some lp =>
    cases hu : unionAll sel with
    | none => simp [hl, hu] at hp
    | some u =>
      simp only [hl, hu, bind, Option.bind, Option.some.injEq] at hp
      subst hp
      exact ⟨clampInto_lo .., clampInto_hi _ _ _ _ hw, clampInto_lo .., clampInto_hi _ _ _ _ hh⟩

/-! ## Bubbles -/

/-- Which bubble is shown. -/
inductive Kind where
  /-- After a text selection: one Highlight button. -/
  | float
  /-- On a selected highlight: colour, Comment, Delete. -/
  | edit
  deriving DecidableEq, Repr, Inhabited

/-- A bubble button. -/
inductive Btn where
  /-- Highlight the selection in the current colour. -/
  | highlight
  /-- The colour swatch with the chevron (opens the colour picker). -/
  | color
  /-- Add or edit the note attached to the highlight. -/
  | comment
  /-- Delete the highlight. -/
  | delete
  deriving DecidableEq, Repr, Inhabited

/-- Name of a button (canvas tag `b:NAME`, status line). -/
def Btn.name : Btn → String
  | .highlight => "highlight"
  | .color => "color"
  | .comment => "comment"
  | .delete => "delete"

/-- The viewer command a button runs (`none`: the colour button only opens the picker). -/
def Btn.cmd? : Btn → Option Menu.Cmd
  | .highlight => some .highlight
  | .color => none
  | .comment => some .addNote
  | .delete => some .deleteMark

/-- Border plus padding around the buttons (1 + 2 px). -/
def pad : Rat := 3

/-- Button height (`--editor-toolbar-height`). -/
def btnH : Rat := 28

/-- Height of a bubble. -/
def height : Rat := btnH + 2 * pad

/-- Width of a divider with its margins (1 px line, 2 px each side). -/
def divider : Rat := 5

/-- Width of a button: 28 px, the colour button 4 + 16 + 4 + 12 + 4 px. -/
def Btn.width : Btn → Rat
  | .color => 40
  | _ => btnH

/-- Buttons of a bubble, left to right. -/
def Kind.btns : Kind → List Btn
  | .float => [.highlight]
  | .edit => [.color, .comment, .delete]

/-- The buttons with their horizontal ranges `(x0, x1)` relative to the bubble's left edge;
dividers between them. -/
def Kind.layout (k : Kind) : List (Btn × Rat × Rat) :=
  (k.btns.foldl (fun (acc : List (Btn × Rat × Rat) × Rat) b =>
    let x := if acc.1.isEmpty then acc.2 else acc.2 + divider
    (acc.1 ++ [(b, x, x + b.width)], x + b.width)) ([], pad)).1

/-- The x positions (relative) of the divider lines. -/
def Kind.dividers (k : Kind) : List Rat :=
  (k.layout.drop 1).map fun (_, x0, _) => x0 - divider / 2

/-- Width of a bubble. -/
def Kind.width (k : Kind) : Rat :=
  match k.layout.getLast? with
  | some (_, _, x1) => x1 + pad
  | none => 2 * pad

/-- The button of bubble `k` placed at `r` under the canvas point `(x, y)`. -/
def hit (k : Kind) (r : Rect) (x y : Rat) : Option Btn :=
  if !(r.contains x y) then none
  else (k.layout.find? fun (_, x0, x1) => decide (r.x0 + x0 ≤ x) && decide (x < r.x0 + x1)).map
    (·.1)

/-! ## Colour picker -/

/-- Swatch diameter in the picker. -/
def swatch : Rat := 16

/-- Gap between the picker's swatches. -/
def pickerGap : Rat := 11

/-- Padding above and below the picker's swatches. -/
def pickerPad : Rat := 8

/-- Width and height of the picker. -/
def pickerW : Rat := Btn.color.width + 4

/-- See `pickerW`. -/
def pickerH : Rat :=
  2 * pickerPad + (Color.all.length : Rat) * swatch + ((Color.all.length - 1 : Nat) : Rat) * pickerGap

/-- The picker of the edit bubble placed at `b`: under its colour button (4 px below the
bubble), above the bubble when it does not fit below `area`. -/
def pickerRect (b : Rect) (area : Rect) : Rect :=
  let x0 := b.x0 + pad - 2
  let below := b.y1 + 4
  let y0 := if below + pickerH ≤ area.y1 then below else b.y0 - 4 - pickerH
  ⟨x0, y0, x0 + pickerW, y0 + pickerH⟩

/-- Centre of each swatch of the picker `p`. -/
def pickerSwatches (p : Rect) : List (Color × Rat × Rat) :=
  (List.range Color.all.length).zip Color.all |>.map fun (i, c) =>
    (c, p.x0 + pickerW / 2, p.y0 + pickerPad + swatch / 2 + (i : Rat) * (swatch + pickerGap))

/-- The colour of the picker row under `(x, y)` (each row reaches half a gap above and below
its swatch). -/
def pickerHit (p : Rect) (x y : Rat) : Option Color :=
  if !(p.contains x y) then none
  else (pickerSwatches p).find? (fun (_, _, cy) =>
      decide (cy - (swatch + pickerGap) / 2 ≤ y) && decide (y < cy + (swatch + pickerGap) / 2)) |>.map
    (·.1)

/-! ## Highlight pop-over -/

namespace Popover

/-- Width of the pop-over (PDF.js `--editor-toolbar-min-width`). -/
def width : Rat := 220

/-- Height of the pop-over. -/
def height : Rat := 190

/-- Horizontal padding. -/
def padX : Rat := 10

/-- Baseline centre of the "Highlight color" title. -/
def titleY : Rat := 20

/-- Centre of the swatch row. -/
def swatchY : Rat := 50

/-- Diameter of a pop-over swatch. -/
def swatchD : Rat := 24

/-- Centre x of swatch `i` (spread over the width, PDF.js `space-between`). -/
def swatchX (i : Nat) : Rat :=
  padX + swatchD / 2 + (i : Rat) * ((width - 2 * padX - swatchD) / 4)

/-- Centre of the "Thickness" label. -/
def thickY : Rat := 92

/-- Centre of the slider row (with the small and large example dots). -/
def sliderY : Rat := 118

/-- Left end of the slider track (after the 8 px dot). -/
def sliderX0 : Rat := padX + 8 + 10

/-- Right end of the slider track (before the 24 px dot). -/
def sliderX1 : Rat := width - padX - 24 - 10

/-- y of the divider. -/
def dividerY : Rat := 148

/-- Centre of the "Show all" row. -/
def toggleY : Rat := 170

/-- The "Show all" switch. -/
def toggleRect : Rect := ⟨width - padX - 32, toggleY - 8, width - padX, toggleY + 8⟩

/-- Smallest thickness (PDF.js `editorFreeHighlightThickness` `min`). -/
def minThick : Nat := 8

/-- Largest thickness. -/
def maxThick : Nat := 24

/-- Default thickness (PDF.js `HighlightEditor._DEFAULT_THICKNESS`). -/
def defaultThick : Nat := 12

/-- `v` clamped into `[minThick, maxThick]`. -/
def clampThick (v : Nat) : Nat := max minThick (min maxThick v)

/-- x of the slider thumb for thickness `v`. -/
def thumbX (v : Nat) : Rat :=
  sliderX0 + ((clampThick v - minThick : Nat) : Rat) * (sliderX1 - sliderX0) /
    ((maxThick - minThick : Nat) : Rat)

/-- The thickness for slider position `x` (nearest step, clamped). -/
def thicknessAt (x : Rat) : Nat :=
  let t := (x - sliderX0) * ((maxThick - minThick : Nat) : Rat) / (sliderX1 - sliderX0)
  clampThick (minThick + (t + 1 / 2).floor.toNat)

/-- What a click in the pop-over hits. -/
inductive Hit where
  /-- A colour swatch. -/
  | color (c : Color)
  /-- The thickness slider (its row). -/
  | slider
  /-- The "Show all" row (the switch or its label). -/
  | toggle
  deriving DecidableEq, Repr, Inhabited

/-- The part of the pop-over under `(x, y)` (pop-over coordinates). -/
def hit (x y : Rat) : Option Hit :=
  if decide (swatchY - swatchD / 2 - 4 ≤ y) && decide (y ≤ swatchY + swatchD / 2 + 4) then
    ((List.range Color.all.length).zip Color.all).find? (fun (i, _) =>
      decide (swatchX i - swatchD / 2 - 4 ≤ x) && decide (x ≤ swatchX i + swatchD / 2 + 4))
      |>.map (Hit.color ·.2)
  else if decide (sliderY - 10 ≤ y) && decide (y ≤ sliderY + 10) &&
      decide (sliderX0 - 8 ≤ x) && decide (x ≤ sliderX1 + 8) then some .slider
  else if decide (toggleY - 12 ≤ y) && decide (y ≤ toggleY + 12) && decide (padX ≤ x) &&
      decide (x ≤ width - padX) then some .toggle
  else none

/-- Left edge of the pop-over for the toolbar button at window x `bx` of width `bw` in a
window `ww` wide: right-aligned with the button (as in PDF.js), kept 4 px inside the window. -/
def left (bx bw ww : Rat) : Rat :=
  clampInto 4 (ww - 4) width (bx + bw - width)

end Popover

/-! ## Tool state -/

/-- The Highlight tool and the floating toolbars' state. -/
structure Ui where
  /-- The Highlight tool is active (a selection is highlighted on mouse-up). -/
  tool : Bool := false
  /-- The Highlight pop-over is open. -/
  popover : Bool := false
  /-- Free-highlight thickness (`Popover.minThick`–`maxThick`). -/
  thickness : Nat := Popover.defaultThick
  /-- Highlights are shown ("Show all"). -/
  showAll : Bool := true
  /-- The edit bubble's colour picker is open. -/
  picker : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- The toolbar's Highlight button: with a selection, highlight it (`true`; the state stays);
else toggle the tool, the pop-over with it. -/
def Ui.toolClick (u : Ui) (hasSel : Bool) : Ui × Bool :=
  if hasSel then (u, true)
  else if u.tool then ({ u with tool := false, popover := false }, false)
  else ({ u with tool := true, popover := true }, false)

/-- Edit → Highlight tool: toggles the tool (and its pop-over) whatever is selected. -/
def Ui.toggleTool (u : Ui) : Ui :=
  if u.tool then { u with tool := false, popover := false } else { u with tool := true, popover := true }

/-- Escape: closes the colour picker and the pop-over (the tool stays active). -/
def Ui.escape (u : Ui) : Ui := { u with picker := false, popover := false }

/-- Sets the thickness (clamped). -/
def Ui.setThickness (u : Ui) (v : Nat) : Ui := { u with thickness := Popover.clampThick v }

/-- Whether a mouse-up that leaves a text selection highlights it at once (tool active). -/
def Ui.highlightOnRelease (u : Ui) (hasSel : Bool) : Bool := u.tool && hasSel

/-- The bubble to show: the float bubble for a text selection on the shown page, else the
edit bubble for a selected highlight on the shown page while highlights are shown. -/
def kindFor (selHere markHere : Bool) (u : Ui) : Option Kind :=
  if selHere then some .float else if markHere && u.showAll then some .edit else none

/-- Escape closes the pop-over and the picker. -/
theorem Ui.escape_closes (u : Ui) : u.escape.popover = false ∧ u.escape.picker = false :=
  ⟨rfl, rfl⟩

/-- After Edit → Highlight tool the pop-over is open exactly when the tool is active. -/
theorem Ui.toggleTool_popover (u : Ui) : u.toggleTool.popover = u.toggleTool.tool := by
  unfold Ui.toggleTool; split <;> rfl

/-! ## Checks -/

#guard lastPoint [⟨10, 10, 100, 20⟩, ⟨10, 22, 60, 32⟩] == some (60, 32)
#guard lastPoint [⟨10, 22, 60, 32⟩, ⟨70, 22, 90, 32⟩, ⟨10, 10, 300, 20⟩] == some (90, 32)
#guard lastPoint [] == none
#guard unionAll [⟨10, 10, 100, 20⟩, ⟨5, 22, 60, 32⟩] == some ⟨5, 10, 100, 32⟩
-- Layouts: float = one button; edit = colour | comment | delete.
#guard Kind.float.layout == [(.highlight, 3, 31)] && Kind.float.width == 34
#guard Kind.edit.layout == [(.color, 3, 43), (.comment, 48, 76), (.delete, 81, 109)]
#guard Kind.edit.width == 112 && Kind.edit.dividers == [91 / 2, 157 / 2] && height == 34
-- Placement: right edge at the last point, 6 px below; clamped; flipped above at the bottom.
private def area : Rect := ⟨0, 0, 1000, 800⟩
#guard place [⟨100, 100, 400, 120⟩, ⟨100, 122, 300, 142⟩] 112 34 area == some ⟨188, 148, 300, 182⟩
#guard place [⟨0, 100, 50, 120⟩] 112 34 area == some ⟨0, 126, 112, 160⟩
#guard place [⟨500, 700, 990, 780⟩] 112 34 area == some ⟨878, 660, 990, 694⟩
#guard place [] 112 34 area == none
-- Hit-testing the edit bubble at (188, 148).
private def eb : Rect := ⟨188, 148, 300, 182⟩
#guard hit .edit eb 200 160 == some .color && hit .edit eb 250 160 == some .comment &&
  hit .edit eb 280 160 == some .delete && hit .edit eb 233 160 == none &&
  hit .edit eb 150 160 == none && hit .edit eb 200 190 == none
#guard Btn.highlight.cmd? == some .highlight && Btn.delete.cmd? == some .deleteMark &&
  Btn.comment.cmd? == some .addNote && Btn.color.cmd? == none
-- The picker: under the bubble, or above it near the bottom; rows map to colours.
#guard pickerH == 140 && pickerRect eb area == ⟨189, 186, 233, 326⟩
#guard (pickerRect ⟨188, 700, 300, 734⟩ area).y0 == 556
#guard pickerHit (pickerRect eb area) 211 202 == some .yellow &&
  pickerHit (pickerRect eb area) 211 (202 + 27 * 4) == some .red &&
  pickerHit (pickerRect eb area) 300 202 == none
-- The pop-over: swatches, slider, switch; thickness mapping.
#guard (List.range 5).map Popover.swatchX == [22, 66, 110, 154, 198]
#guard Popover.hit 22 50 == some (.color .yellow) && Popover.hit 198 50 == some (.color .red) &&
  Popover.hit 44 50 == none && Popover.hit 100 118 == some .slider &&
  Popover.hit 190 170 == some .toggle && Popover.hit 100 20 == none
#guard Popover.thumbX 8 == Popover.sliderX0 && Popover.thumbX 24 == Popover.sliderX1 &&
  Popover.thumbX 99 == Popover.sliderX1
#guard Popover.thicknessAt 0 == 8 && Popover.thicknessAt 500 == 24 &&
  (List.range 30).all fun v => Popover.thicknessAt (Popover.thumbX v) == Popover.clampThick v
#guard Popover.left 1660 32 1900 == 1472 && Popover.left 100 32 1900 == 4
-- Tool state.
#guard ({} : Ui).toolClick true == ({}, true)
#guard (({} : Ui).toolClick false).1.tool && (({} : Ui).toolClick false).1.popover
#guard ((({} : Ui).toolClick false).1.toolClick false).1 == {}
#guard ({ tool := true, popover := true, picker := true } : Ui).escape ==
  { tool := true, popover := false, picker := false }
#guard (({} : Ui).setThickness 3).thickness == 8 && (({} : Ui).setThickness 30).thickness == 24
#guard !({} : Ui).highlightOnRelease true && ({ tool := true } : Ui).highlightOnRelease true
#guard kindFor true true {} == some .float && kindFor false true {} == some .edit &&
  kindFor false true { showAll := false } == none && kindFor false false {} == none

end SafePdf.Shell.App.Bubble
