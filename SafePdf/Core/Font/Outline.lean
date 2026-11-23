import SafePdf.Core.Content.GState

/-!
# Glyph outlines: the common type (Plan.md §6 Phase 7, task 7.3a)

Plan.md §6 Phase 7: "glyph outlines through the same path code". The three embedded font
formats produce their outlines in this one type, in **glyph space** (font units for TrueType,
charstring units for Type 1 and CFF — the font's `/FontMatrix` maps them to text space):

* TrueType (`Font.TrueType.TTFont.glyphOutline`): quadratic contours (`quadTo`), composites
  already resolved by `TTFont.outline`;
* Type 1 (`Font.Type1.Font1.outline`) and CFF / Type 2 (`Font.CFF.CFFFont.outline`): cubic
  path operators recorded by the charstring interpreters (`curveTo`), `seac` composites.

The rasterizer (`Core.Raster.Glyph`) maps an outline through the glyph's text rendering matrix
into a 7.2a device path (quadratics by exact degree elevation).

## The builder

`PathAcc` is the path recorder the charstring interpreters drive: the segments so far (at most
`maxOutlineSegs`, **by construction** — `PathAcc.push` fails past the cap, so a hostile
charstring cannot build an unbounded path), the current point, and whether a subpath is open.
`moveTo` closes an open subpath first (filling closes implicitly; stroking a glyph needs the
explicit close, and both Type 1 `closepath` and Type 2's implicit closing mean "closed").
Coordinates are `Fixed` (10⁻⁶ glyph units), relative moves add with the saturating
`Fixed.add`.
-/

namespace SafePdf.Core.Font.Outline

open SafePdf.Core.Content

/-- Most segments one glyph outline may have (local cap; a larger outline is rejected: the
glyph draws nothing). -/
def maxOutlineSegs : Nat := 65536

/-- One outline segment in glyph space. -/
inductive OSeg where
  /-- Start a subpath. -/
  | moveTo (p : Point)
  /-- Straight line to `p`. -/
  | lineTo (p : Point)
  /-- Quadratic Bézier (TrueType) with control `c`, ending at `p`. -/
  | quadTo (c p : Point)
  /-- Cubic Bézier with controls `c1`, `c2`, ending at `p`. -/
  | curveTo (c1 c2 p : Point)
  /-- Close the current subpath. -/
  | close
  deriving DecidableEq, Repr, Inhabited

/-- A glyph outline: at most `maxOutlineSegs` segments (by its type). -/
abbrev Outline := {a : Array OSeg // a.size ≤ maxOutlineSegs}

/-- The empty outline. -/
def Outline.empty : Outline := ⟨#[], Nat.zero_le _⟩

instance : Inhabited Outline := ⟨Outline.empty⟩

/-- Make an outline from segments, `none` past the cap. -/
def Outline.ofArray (a : Array OSeg) : Option Outline :=
  if h : a.size ≤ maxOutlineSegs then some ⟨a, h⟩ else none

/-- Concatenate two outlines (a `seac` composite), `none` past the cap. -/
def Outline.append (o p : Outline) : Option Outline := Outline.ofArray (o.1 ++ p.1)

/-- Translate a point. -/
def Point.shift (dx dy : Fixed) (p : Point) : Point := ⟨Fixed.add p.x dx, Fixed.add p.y dy⟩

/-- Translate a segment. -/
def OSeg.shift (dx dy : Fixed) : OSeg → OSeg
  | .moveTo p => .moveTo (Point.shift dx dy p)
  | .lineTo p => .lineTo (Point.shift dx dy p)
  | .quadTo c p => .quadTo (Point.shift dx dy c) (Point.shift dx dy p)
  | .curveTo c1 c2 p =>
    .curveTo (Point.shift dx dy c1) (Point.shift dx dy c2) (Point.shift dx dy p)
  | .close => .close

/-- Translate an outline (the size is unchanged). -/
def Outline.shift (dx dy : Fixed) (o : Outline) : Outline :=
  ⟨o.1.map (OSeg.shift dx dy), by simp only [Array.size_map]; exact o.2⟩

/-- The points of a segment (controls included). -/
def OSeg.points : OSeg → List Point
  | .moveTo p | .lineTo p => [p]
  | .quadTo c p => [c, p]
  | .curveTo c1 c2 p => [c1, c2, p]
  | .close => []

/-- Number of points (controls included) of an outline. -/
def Outline.numPoints (o : Outline) : Nat := o.1.foldl (fun n s => n + s.points.length) 0

/-- The control-point bounding box `(xMin, yMin, xMax, yMax)` in raw `Fixed` units
(`none` for an outline without points). It contains the outline (Béziers lie in the hull of
their controls). -/
def Outline.bbox (o : Outline) : Option (Int × Int × Int × Int) :=
  o.1.foldl (fun acc s => s.points.foldl (fun acc p =>
    match acc with
    | none => some (p.x.raw, p.y.raw, p.x.raw, p.y.raw)
    | some (a, b, c, d) => some (min a p.x.raw, min b p.y.raw, max c p.x.raw, max d p.y.raw))
    acc) none

/-- The bounding box in whole glyph units (exact for integral outlines). -/
def Outline.bboxUnits (o : Outline) : Option (Int × Int × Int × Int) :=
  o.bbox.map fun (a, b, c, d) => (a / fixedScale, b / fixedScale, c / fixedScale, d / fixedScale)

/-! ## The path recorder -/

/-- The path recorder of the charstring interpreters (see the module doc). -/
structure PathAcc where
  /-- Segments recorded so far (bounded by `maxOutlineSegs`). -/
  segs : Outline := Outline.empty
  /-- Current point. -/
  cur : Point := ⟨Fixed.zero, Fixed.zero⟩
  /-- A subpath is open (a `moveTo` was recorded and not closed). -/
  isOpen : Bool := false

instance : Inhabited PathAcc := ⟨{}⟩

/-- Append a segment, failing past `maxOutlineSegs`. -/
def PathAcc.push (a : PathAcc) (s : OSeg) : Except String PathAcc :=
  if h : a.segs.1.size < maxOutlineSegs then
    .ok { a with segs := ⟨a.segs.1.push s, by simp only [Array.size_push]; omega⟩ }
  else .error "glyph outline too large"

/-- The point `cur + (dx, dy)`. -/
def PathAcc.rel (a : PathAcc) (dx dy : Fixed) : Point := Point.shift dx dy a.cur

/-- Close the open subpath, if any. -/
def PathAcc.close (a : PathAcc) : Except String PathAcc :=
  if a.isOpen then do
    let a ← a.push .close
    .ok { a with isOpen := false }
  else .ok a

/-- Relative move: closes the open subpath, starts a new one. -/
def PathAcc.rmoveTo (a : PathAcc) (dx dy : Fixed) : Except String PathAcc := do
  let a ← a.close
  let p := a.rel dx dy
  let a ← a.push (.moveTo p)
  .ok { a with cur := p, isOpen := true }

/-- Relative line. A drawing operator without a preceding move starts at the current point. -/
def PathAcc.rlineTo (a : PathAcc) (dx dy : Fixed) : Except String PathAcc := do
  let a ← if a.isOpen then .ok a else do
    let a ← a.push (.moveTo a.cur)
    .ok { a with isOpen := true }
  let p := a.rel dx dy
  let a ← a.push (.lineTo p)
  .ok { a with cur := p }

/-- Relative cubic: controls `cur + d1`, `c1 + d2`, end `c2 + d3`. -/
def PathAcc.rcurveTo (a : PathAcc) (dx1 dy1 dx2 dy2 dx3 dy3 : Fixed) : Except String PathAcc := do
  let a ← if a.isOpen then .ok a else do
    let a ← a.push (.moveTo a.cur)
    .ok { a with isOpen := true }
  let c1 := a.rel dx1 dy1
  let c2 := Point.shift dx2 dy2 c1
  let p := Point.shift dx3 dy3 c2
  let a ← a.push (.curveTo c1 c2 p)
  .ok { a with cur := p }

/-- Absolute cubic (flex): controls and end given. -/
def PathAcc.curveTo (a : PathAcc) (c1 c2 p : Point) : Except String PathAcc := do
  let a ← if a.isOpen then .ok a else do
    let a ← a.push (.moveTo a.cur)
    .ok { a with isOpen := true }
  let a ← a.push (.curveTo c1 c2 p)
  .ok { a with cur := p }

/-- Every outline a recorder holds respects the cap (by construction). -/
theorem PathAcc.size_le (a : PathAcc) : a.segs.1.size ≤ maxOutlineSegs := a.segs.2

/-- Pushing grows the outline by exactly one segment. -/
theorem PathAcc.push_size {a b : PathAcc} {s : OSeg} (h : a.push s = .ok b) :
    b.segs.1.size = a.segs.1.size + 1 := by
  unfold PathAcc.push at h
  split at h
  · cases h; simp
  · cases h

private def pt (x y : Int) : Point := ⟨Fixed.ofInt x, Fixed.ofInt y⟩

#guard
  match (do
    let a ← ({} : PathAcc).rmoveTo (Fixed.ofInt 10) Fixed.zero
    let a ← a.rlineTo (Fixed.ofInt 300) (Fixed.ofInt 700)
    let a ← a.rlineTo (Fixed.ofInt 300) (Fixed.ofInt (-700))
    a.close : Except String PathAcc) with
  | .ok a => a.segs.1 == #[.moveTo (pt 10 0), .lineTo (pt 310 700), .lineTo (pt 610 0), .close] &&
      a.segs.bboxUnits == some (10, 0, 610, 700) && a.segs.numPoints == 3
  | .error _ => false
#guard (Outline.ofArray (Array.replicate (maxOutlineSegs + 1) .close)).isNone
#guard ((Outline.ofArray #[.moveTo (pt 1 2)]).map fun o => (o.shift (Fixed.ofInt 5) Fixed.zero).bboxUnits)
  == some (some (6, 2, 6, 2))

end SafePdf.Core.Font.Outline
