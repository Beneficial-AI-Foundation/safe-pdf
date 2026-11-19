import SafePdf.Core.Content.GState

/-!
# Display list (Plan.md §6 Phase 5, §3 C6)

The typed output of the content-stream interpreter (task 5.2): one flat sequence of display
items per page. It is the single source for SVG export (5.4), text extraction (Phase 6) and
the rasterizer (Phase 7); because extraction and rendering read the same items, "extracted =
displayed" (C6) becomes a property of this one structure.

## Design decisions

* **Self-contained items.** Every painting item carries the graphics-state snapshot it needs
  (colour and alpha, line style and CTM for strokes, the clip), so consumers never replay the
  graphics state. Snapshots are cheap: they share the interpreter's persistent values.
* **Geometry in page space** (see `Core.Content.GState`): paths are already transformed by
  the CTM. Strokes keep the CTM in `StrokeStyle.ctm` because line width and dashes are in
  user space (the pen is the CTM image of a user-space disc).
* **Fill-and-stroke is two items.** `B`/`B*`/`b`/`b*` produce `fillPath` then `strokePath`,
  which ISO 32000-2 §8.5.3.1 states is equivalent; `Paint.items` is the one place that does
  it, so 5.2 and 5.3 share it.
* **Clip items are informational.** `W`/`W*` emit a `clip` item at the point the clip takes
  effect (after the painting operator), but every painting item already carries its full
  clip, so a renderer may ignore `clip` items; text extraction uses the carried clip to tell
  clipped-away text (C6).
* **Glyph runs are unpositioned.** A run records the bytes shown by one `Tj`/`'`/`"`/`TJ`
  (with the `TJ` adjustments), the font reference, the §9.3 parameters, `Tm` at the start of
  the run and the CTM. The font reference identifies the font *object* (`FontId`, task 6.7a:
  its indirect reference, or the content whose resources hold it), not only its resource name,
  so a form's `/F1` and the page's `/F1` stay apart. Glyph positions need font metrics (Phase 6). Consecutive shows in one
  text object start where the previous ended, which also needs metrics: 5.2 therefore takes
  the advance computation as a parameter (Phase 6 supplies real widths; a zero-advance stub
  suffices for M5), so `tm` is always the absolute text matrix. `tm` and `ctm` are kept
  apart (rather than pre-multiplied) because `Matrix.mul` rounds and is not associative;
  `GlyphRun.startMatrix` gives the composed text rendering matrix at the run start.
* **Images by reference.** Image XObjects are referenced by resource name and object number
  (data decoded later, through the quarantine for DCT/JPX); inline images carry their
  parameter dictionary and raw bytes (bounded by the content stream). Form XObjects are not
  items: the interpreter expands them in place, under fuel.
* **Unknown operators** become `unsupported op`, logged for the coverage report (M5), never a
  failure.
* **Length bound.** `DisplayList` is a plain `Array`; that its length is at most the number
  of operators processed times `Paint.maxItems` is 5.2's theorem, not a type invariant.
-/

namespace SafePdf.Core.Content

open SafePdf

/-- Snapshot for filling: colour and alpha. -/
structure FillStyle where
  /-- Non-stroking colour. -/
  color : Color
  /-- Non-stroking alpha. -/
  alpha : Comp
  deriving DecidableEq, Repr, Inhabited

/-- Snapshot for stroking: colour, alpha, line style (user space) and the CTM mapping user
space to page space. -/
structure StrokeStyle where
  /-- Stroking colour. -/
  color : Color
  /-- Stroking alpha. -/
  alpha : Comp
  /-- Width, caps, joins, miter limit, dashes in user space. -/
  line : LineStyle
  /-- CTM at painting time. -/
  ctm : Matrix
  deriving DecidableEq, Repr, Inhabited

/-- The fill snapshot of a graphics state. -/
def GState.fillStyle (g : GState) : FillStyle := ⟨g.fillColor, g.fillAlpha⟩

/-- The stroke snapshot of a graphics state. -/
def GState.strokeStyle (g : GState) : StrokeStyle :=
  ⟨g.strokeColor, g.strokeAlpha, g.line, g.ctm⟩

/-- One element of a text-showing operator: a string, or a `TJ` adjustment in thousandths of
text space (positive moves left/down). `Tj` is a single `str`. -/
inductive TextPart where
  /-- Bytes of a string operand (character codes, decoded by the font in Phase 6). -/
  | str (bytes : List UInt8)
  /-- A `TJ` number. -/
  | adjust (thousandths : Fixed)
  deriving DecidableEq, Repr, Inhabited

/-- One text-showing operation with everything needed to position and paint its glyphs. -/
structure GlyphRun where
  /-- Font (resource name, object identity) and size (`Tf`, or an ExtGState `/Font`). -/
  font : FontRef
  /-- `Tm` at the start of the run (text space → user space). -/
  tm : Matrix
  /-- CTM (user space → page space). -/
  ctm : Matrix
  /-- `Tc`. -/
  charSpacing : Fixed
  /-- `Tw`. -/
  wordSpacing : Fixed
  /-- `Tz`, percent. -/
  horizScaling : Fixed
  /-- `Ts`. -/
  rise : Fixed
  /-- `Tr`; `invisible`/`clip` runs paint nothing (C6: extraction must know). -/
  renderMode : TextRenderMode
  /-- The shown strings and adjustments. -/
  parts : List TextPart
  /-- Fill snapshot (used by modes that fill). -/
  fill : FillStyle
  /-- Stroke snapshot (used by modes that stroke). -/
  stroke : StrokeStyle
  deriving DecidableEq, Repr, Inhabited

/-- Text rendering matrix at the start of the run (ISO 32000-2 §9.4.4):
`[Tfs·Th 0 0 Tfs 0 Ts] × Tm × CTM`, evaluated left to right. -/
def GlyphRun.startMatrix (r : GlyphRun) : Matrix :=
  let th := Fixed.div r.horizScaling (Fixed.ofInt 100)
  let p : Matrix := ⟨Fixed.mul r.font.size th, Fixed.zero, Fixed.zero, r.font.size,
    Fixed.zero, r.rise⟩
  Matrix.mul (Matrix.mul p r.tm) r.ctm

/-- Where an image's data comes from. -/
inductive ImageSource where
  /-- An image XObject: resource name and its indirect object `num gen`. -/
  | xobject (name : Name) (num gen : Nat)
  /-- An inline image (`BI … ID … EI`): its (abbreviation-expanded) parameters and raw,
  still-encoded data. -/
  | inline (params : Dict) (data : ByteArray)

instance : Inhabited ImageSource := ⟨.xobject ⟨[]⟩ 0 0⟩

/-- A display item: one painting or clipping event, in content-stream order. -/
inductive DisplayItem where
  /-- Fill a page-space path. -/
  | fillPath (path : Path) (rule : FillRule) (style : FillStyle) (clip : Clip)
  /-- Stroke a page-space path. -/
  | strokePath (path : Path) (style : StrokeStyle) (clip : Clip)
  /-- The clip was intersected with `path` (informational; see the module doc). -/
  | clip (path : Path) (rule : FillRule)
  /-- Show text. -/
  | glyphRun (run : GlyphRun) (clip : Clip)
  /-- Paint an image into the unit square mapped by `ctm`; `fill` is the colour of stencil
  masks (`/ImageMask true`). -/
  | image (src : ImageSource) (ctm : Matrix) (fill : FillStyle) (clip : Clip)
  /-- `sh`: paint a shading resource over the clip (placeholder until shadings are
  rendered). -/
  | shading (name : Name) (ctm : Matrix) (clip : Clip)
  /-- An operator the interpreter does not handle (bytes of the operator name). -/
  | unsupported (op : List UInt8)

instance : Inhabited DisplayItem := ⟨.unsupported []⟩

/-- The display list of a page (or form). -/
abbrev DisplayList := Array DisplayItem

/-- Path-painting operators (ISO 32000-2 §8.5.3.1 Table 59), excluding `n`. -/
inductive Paint where
  /-- `f`, `F`, `f*`. -/
  | fill (rule : FillRule)
  /-- `S`, `s` (closing is done on the path). -/
  | stroke
  /-- `B`, `B*`, `b`, `b*`. -/
  | fillStroke (rule : FillRule)
  deriving DecidableEq, Repr, Inhabited

/-- Maximum number of items one painting operator produces. -/
def Paint.maxItems : Nat := 2

/-- The items a painting operator produces for `path` in state `g`; fill-and-stroke is a
fill followed by a stroke (§8.5.3.1). -/
def Paint.items (p : Paint) (path : Path) (g : GState) : List DisplayItem :=
  match p with
  | .fill rule => [.fillPath path rule g.fillStyle g.clip]
  | .stroke => [.strokePath path g.strokeStyle g.clip]
  | .fillStroke rule =>
    [.fillPath path rule g.fillStyle g.clip, .strokePath path g.strokeStyle g.clip]

/-- One painting operator yields at most `Paint.maxItems` items. -/
theorem Paint.items_length_le (p : Paint) (path : Path) (g : GState) :
    (p.items path g).length ≤ Paint.maxItems := by
  cases p <;> simp [items, maxItems]

/-- Painting never yields an empty list. -/
theorem Paint.items_ne_nil (p : Paint) (path : Path) (g : GState) : p.items path g ≠ [] := by
  cases p <;> simp [items]

/-- Constructor name of an item (for logs, coverage and tests). -/
def DisplayItem.kind : DisplayItem → String
  | .fillPath .. => "fillPath"
  | .strokePath .. => "strokePath"
  | .clip .. => "clip"
  | .glyphRun .. => "glyphRun"
  | .image .. => "image"
  | .shading .. => "shading"
  | .unsupported _ => "unsupported"

/-! ## Samples, one per constructor -/

private def sampleSquare : Path :=
  ⟨#[.moveTo ⟨Fixed.zero, Fixed.zero⟩, .lineTo ⟨Fixed.ofInt 10, Fixed.zero⟩,
     .lineTo ⟨Fixed.ofInt 10, Fixed.ofInt 10⟩, .lineTo ⟨Fixed.zero, Fixed.ofInt 10⟩,
     .closePath]⟩

private def sampleRun : GlyphRun :=
  { font := { name := Name.ofString "F1", size := Fixed.ofInt 12 }, tm := Matrix.translate (Fixed.ofInt 72)
      (Fixed.ofInt 700), ctm := Matrix.identity, charSpacing := Fixed.zero,
    wordSpacing := Fixed.zero, horizScaling := Fixed.ofInt 100, rise := Fixed.zero,
    renderMode := .fill, parts := [.str "Hi".toUTF8.toList, .adjust (Fixed.ofInt (-250))],
    fill := ({} : GState).fillStyle, stroke := ({} : GState).strokeStyle }

#guard ((Paint.fill .nonzero).items sampleSquare {}).map DisplayItem.kind == ["fillPath"]
#guard (Paint.stroke.items sampleSquare {}).map DisplayItem.kind == ["strokePath"]
#guard ((Paint.fillStroke .evenOdd).items sampleSquare {}).map DisplayItem.kind
    == ["fillPath", "strokePath"]
#guard (DisplayItem.clip sampleSquare .evenOdd).kind == "clip"
#guard (DisplayItem.glyphRun sampleRun []).kind == "glyphRun"
#guard sampleRun.startMatrix
    == ⟨Fixed.ofInt 12, Fixed.zero, Fixed.zero, Fixed.ofInt 12, Fixed.ofInt 72,
        Fixed.ofInt 700⟩
#guard (DisplayItem.image (.xobject (Name.ofString "Im0") 12 0) Matrix.identity
    ({} : GState).fillStyle []).kind == "image"
#guard (DisplayItem.image (.inline [] (ByteArray.mk #[0, 255])) Matrix.identity
    ({} : GState).fillStyle []).kind == "image"
#guard (DisplayItem.shading (Name.ofString "Sh0") Matrix.identity []).kind == "shading"
#guard (DisplayItem.unsupported "BX".toUTF8.toList).kind == "unsupported"
#guard (#[DisplayItem.unsupported []] : DisplayList).size == 1

end SafePdf.Core.Content
