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
  it, so 5.2 and 5.3 share it. With a translucent or blended stroke the two are bracketed by a
  non-isolated knockout group (task 7.3i, as MuPDF: the fill does not show through the
  stroke), so one painting operator yields at most `Paint.maxItems` = 4 items.
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
* **Transparency (task 7.3c, ISO 32000-2 §11).** Constant alpha, the blend mode (`/BM`) and
  the soft mask (`/SMask`) are part of every fill/stroke snapshot (`FillStyle`,
  `StrokeStyle`: glyph runs and images carry them through their snapshots). A soft mask is
  defined once, where the ExtGState sets it, by a nested `softMask id info items` item
  (`id` is unique in the page's list; items reference it by `smask = some id`). A
  transparency group form is bracketed by `groupBegin g` … `groupEnd` (flat, so extraction
  sees the text inside groups). `sh` items carry the fill snapshot too (task 7.3f: `ca`,
  blend mode, soft mask).
* **Resources independent of the page (task 7.3f).** Items that name resources record where
  they live, resolved by the runner in the resources of the content being run (page or form):
  image XObjects by object number; `sh` by `ResRef` (the indirect object, or the form whose
  own `/Resources` hold a direct entry); pattern colours by `FillStyle.pattern` /
  `StrokeStyle.pattern` (`PatternUse`: the `ResRef` and the **base matrix** of the using
  content, §8.7.3); an inline image's resource-name `/ColorSpace` is replaced by the
  definition from the current resources. So loaders never need the page's resources alone,
  and `DisplayList.foldDeep` reaches items nested in soft masks.
* **Unknown operators** become `unsupported op`, logged for the coverage report (M5), never a
  failure.
* **Length bound.** `DisplayList` is a plain `Array`; that its length is at most the number
  of operators processed times `Paint.maxItems` is 5.2's theorem, not a type invariant.
-/

namespace SafePdf.Core.Content

open SafePdf

/-- Where a named resource used by an item lives (task 7.3f), so that consumers resolve it
independently of the page: the runner (5.2b) resolves the name in the resources of the content
being run when it emits the item. -/
inductive ResRef where
  /-- Not resolved (resource-free runs), or a direct entry of the **page's** resources: look
  the name up in the page's `/Resources`. -/
  | page
  /-- The resource entry is the indirect reference `num gen`: the object itself. -/
  | ref (num gen : Nat)
  /-- A direct entry of the own `/Resources` of form XObject `num gen`: look the name up
  there. -/
  | form (num gen : Nat)
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- A pattern colour as it is used (task 7.3f, ISO 32000-2 §8.7.3): where the pattern resource
lives, and the **base matrix**, the CTM that maps the default coordinate space of the page or
form in which the pattern is used to page space (a form's `/Matrix` × the CTM at its `Do`;
the identity for page content). The pattern matrix maps pattern space to that space, so it is
composed with `base`. -/
structure PatternUse where
  /-- Where the pattern resource (named by the colour) lives. -/
  res : ResRef := .page
  /-- Default space of the using content → page space. -/
  base : Matrix := Matrix.identity
  /-- For an uncoloured (PaintType 2) pattern: the colour in the underlying space that the
  `SCN`/`scn` setting this pattern gave (`c₁ … cₙ /P scn`, §8.7.3.3), as a device colour;
  `none` without colour operands. -/
  under : Option Color := none
  deriving DecidableEq, Repr

/-- Snapshot for filling: colour and alpha. -/
structure FillStyle where
  /-- Non-stroking colour. -/
  color : Color
  /-- Non-stroking alpha. -/
  alpha : Comp
  /-- Blend mode (task 7.3c). -/
  blend : BlendMode := .normal
  /-- Soft mask: identifier of a `DisplayItem.softMask` item (task 7.3c). -/
  smask : Option Nat := none
  /-- For a pattern colour: where its pattern lives and the base matrix (task 7.3f; set by
  the runner, `none` from the resource-free interpreter). -/
  pattern : Option PatternUse := none
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
  /-- Blend mode (task 7.3c). -/
  blend : BlendMode := .normal
  /-- Soft mask: identifier of a `DisplayItem.softMask` item (task 7.3c). -/
  smask : Option Nat := none
  /-- For a pattern colour: where its pattern lives and the base matrix (task 7.3f). -/
  pattern : Option PatternUse := none
  deriving DecidableEq, Repr, Inhabited

/-- The fill snapshot of a graphics state (no pattern use: the runner adds it). -/
def GState.fillStyle (g : GState) : FillStyle :=
  ⟨g.fillColor, g.fillAlpha, g.blendMode, g.softMask, none⟩

/-- The stroke snapshot of a graphics state (no pattern use: the runner adds it). -/
def GState.strokeStyle (g : GState) : StrokeStyle :=
  ⟨g.strokeColor, g.strokeAlpha, g.line, g.ctm, g.blendMode, g.softMask, none⟩

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

/-- How a soft mask is derived from its group (ISO 32000-2 §11.5.2, Table 142 `/S`). -/
inductive SoftMaskKind where
  /-- `/Luminosity`: the luminosity of the group composited over the backdrop `/BC`. -/
  | luminosity
  /-- `/Alpha`: the group's alpha (shape × opacity). -/
  | alpha
  deriving DecidableEq, Repr, Inhabited

/-- A soft-mask dictionary (§11.6.5.2), as far as rendering needs it. `/TR` (transfer
function) is not recorded: the identity is used (documented gap). -/
structure SoftMaskInfo where
  /-- `/S`. -/
  kind : SoftMaskKind
  /-- `/BC` as a device colour (1, 3 or 4 components: gray, RGB, CMYK); black by default.
  Only used by luminosity masks. -/
  backdrop : Color := .gray Comp.zero
  /-- The mask group's `/BBox` in page space (outside it the mask is the backdrop's
  luminosity, or 0 for alpha masks). -/
  bbox : Option Path := none
  deriving DecidableEq, Repr, Inhabited

/-- A transparency group (a form XObject with `/Group << /S /Transparency >>`, §11.6.6,
§8.10.3) as it is composited: the graphics state at the `Do` supplies alpha (`ca`), blend
mode and soft mask; inside the group they are reset to their initial values. -/
structure GroupInfo where
  /-- The group's `/BBox` in page space. -/
  bbox : Option Path := none
  /-- `/I`. -/
  isolated : Bool := false
  /-- `/K`. -/
  knockout : Bool := false
  /-- Constant alpha the group is composited with (`ca` at the `Do`). -/
  alpha : Comp := Comp.one
  /-- Blend mode the group is composited with. -/
  blend : BlendMode := .normal
  /-- Soft mask (`DisplayItem.softMask` identifier) the group is composited through. -/
  smask : Option Nat := none
  deriving DecidableEq, Repr, Inhabited

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
  /-- `sh`: paint shading resource `name` (living where `res` says, task 7.3f) over the clip,
  with the fill snapshot's alpha (`ca`), blend mode and soft mask (task 7.3f; its colour is
  unused). -/
  | shading (name : Name) (res : ResRef) (ctm : Matrix) (fill : FillStyle) (clip : Clip)
  /-- An operator the interpreter does not handle (bytes of the operator name). -/
  | unsupported (op : List UInt8)
  /-- Start of a transparency group (task 7.3c): the items up to the matching `groupEnd` are
  composited together, then onto the backdrop with the group's alpha, blend mode and soft
  mask. Groups nest like brackets (the runner emits both ends around one form). -/
  | groupBegin (g : GroupInfo)
  /-- End of the innermost open transparency group. -/
  | groupEnd
  /-- Definition of soft mask `id` (task 7.3c), set by an ExtGState `/SMask`: `items` are the
  mask group's (`/G`) items, in the coordinates in effect at the `gs`. They are **not**
  painted on the page: painting items whose style carries `smask = some id` are composited
  through the mask. Nested, so consumers that do not know masks (text extraction, SVG) skip the
  mask's contents automatically. -/
  | softMask (id : Nat) (info : SoftMaskInfo) (items : Array DisplayItem)

instance : Inhabited DisplayItem := ⟨.unsupported []⟩

/-- The display list of a page (or form). -/
abbrev DisplayList := Array DisplayItem

/-- Fold `f` over the items of a list and, depth first, over the items of nested `softMask`
items (after the `softMask` item itself), up to `fuel` levels of nesting (the runner nests
soft masks at most `Limits.maxXObjectDepth` deep; deeper items are not visited). Used by
resource loaders (task 7.3f) so that images and shadings inside soft-mask groups are found. -/
def DisplayList.foldDeep {α : Type} (f : α → DisplayItem → α) : Nat → α → DisplayList → α
  | 0, acc, items => items.foldl f acc
  | n + 1, acc, items => items.foldl (fun acc it =>
      match it with
      | .softMask _ _ inner => DisplayList.foldDeep f n (f acc it) inner
      | _ => f acc it) acc

/-- Path-painting operators (ISO 32000-2 §8.5.3.1 Table 59), excluding `n`. -/
inductive Paint where
  /-- `f`, `F`, `f*`. -/
  | fill (rule : FillRule)
  /-- `S`, `s` (closing is done on the path). -/
  | stroke
  /-- `B`, `B*`, `b`, `b*`. -/
  | fillStroke (rule : FillRule)
  deriving DecidableEq, Repr, Inhabited

/-- Maximum number of items one painting operator produces (task 7.3i: 4, a fill and a
stroke inside a knockout group). -/
def Paint.maxItems : Nat := 4

/-- Whether fill-and-stroke in state `g` needs its knockout group (task 7.3i, MuPDF 1.25.1
`pdf-op-run.c` `pdf_show_path`): not when the stroke's alpha is 0 (it paints nothing) or 1
with `Normal` (it covers the fill exactly where it paints). -/
def Paint.needsKnockout (g : GState) : Bool :=
  !(g.strokeAlpha == Comp.zero || (g.strokeAlpha == Comp.one && g.blendMode == .normal))

/-- The group bracketing fill-and-stroke (task 7.3i): non-isolated, knockout, alpha 1,
`Normal`, so the stroke composites over the backdrop of the fill, not over the fill. -/
def Paint.knockoutGroup : GroupInfo := { isolated := false, knockout := true }

/-- The items a painting operator produces for `path` in state `g`; fill-and-stroke is a
fill followed by a stroke (§8.5.3.1), bracketed by a knockout group when the stroke is
translucent or blended (`needsKnockout`, ISO 32000-2 §11.7.4.4 note: the stroke must not
show the fill through it). -/
def Paint.items (p : Paint) (path : Path) (g : GState) : List DisplayItem :=
  match p with
  | .fill rule => [.fillPath path rule g.fillStyle g.clip]
  | .stroke => [.strokePath path g.strokeStyle g.clip]
  | .fillStroke rule =>
    if Paint.needsKnockout g then
      [.groupBegin Paint.knockoutGroup, .fillPath path rule g.fillStyle g.clip,
        .strokePath path g.strokeStyle g.clip, .groupEnd]
    else [.fillPath path rule g.fillStyle g.clip, .strokePath path g.strokeStyle g.clip]

/-- One painting operator yields at most `Paint.maxItems` items. -/
theorem Paint.items_length_le (p : Paint) (path : Path) (g : GState) :
    (p.items path g).length ≤ Paint.maxItems := by
  cases p
  · simp [items, maxItems]
  · simp [items, maxItems]
  · simp only [items]; split <;> simp [maxItems]

/-- Painting never yields an empty list. -/
theorem Paint.items_ne_nil (p : Paint) (path : Path) (g : GState) : p.items path g ≠ [] := by
  cases p
  · simp [items]
  · simp [items]
  · simp only [items]; split <;> simp

/-- Constructor name of an item (for logs, coverage and tests). -/
def DisplayItem.kind : DisplayItem → String
  | .fillPath .. => "fillPath"
  | .strokePath .. => "strokePath"
  | .clip .. => "clip"
  | .glyphRun .. => "glyphRun"
  | .image .. => "image"
  | .shading .. => "shading"
  | .unsupported _ => "unsupported"
  | .groupBegin _ => "groupBegin"
  | .groupEnd => "groupEnd"
  | .softMask .. => "softMask"

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
#guard ((Paint.fillStroke .nonzero).items sampleSquare
    { strokeAlpha := Comp.ofFixed (Fixed.div (Fixed.ofInt 1) (Fixed.ofInt 2)) }).map DisplayItem.kind
    == ["groupBegin", "fillPath", "strokePath", "groupEnd"]
#guard ((Paint.fillStroke .nonzero).items sampleSquare { blendMode := .multiply }).map
    DisplayItem.kind == ["groupBegin", "fillPath", "strokePath", "groupEnd"]
#guard ((Paint.fillStroke .nonzero).items sampleSquare
    { strokeAlpha := Comp.zero, blendMode := .multiply }).map DisplayItem.kind
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
#guard (DisplayItem.shading (Name.ofString "Sh0") .page Matrix.identity ({} : GState).fillStyle []).kind
    == "shading"
#guard (DisplayItem.unsupported "BX".toUTF8.toList).kind == "unsupported"
#guard (#[DisplayItem.unsupported []] : DisplayList).size == 1
#guard (DisplayItem.groupBegin {}).kind == "groupBegin"
#guard DisplayItem.groupEnd.kind == "groupEnd"
#guard (DisplayItem.softMask 3 { kind := .luminosity } #[.groupEnd]).kind == "softMask"
#guard ({ ({} : GState) with blendMode := .multiply, softMask := some 4 }).fillStyle.smask
    == some 4

#guard (DisplayList.foldDeep (fun n (_ : DisplayItem) => n + 1) 2 0
    #[.groupEnd, .softMask 1 { kind := .alpha } #[.groupEnd, .softMask 2 { kind := .alpha } #[.groupEnd]]])
  == 5
#guard (DisplayList.foldDeep (fun n (_ : DisplayItem) => n + 1) 1 0
    #[.groupEnd, .softMask 1 { kind := .alpha } #[.groupEnd, .softMask 2 { kind := .alpha } #[.groupEnd]]])
  == 4
end SafePdf.Core.Content
