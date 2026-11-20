import SafePdf.Core.Raster.Clip
import SafePdf.Core.Text
import SafePdf.Core.Font.Outline
import SafePdf.Core.Raster.Image
import SafePdf.Core.Raster.Transparency
import SafePdf.Core.Raster.Shading

/-!
# Glyph rendering: outlines through the path rasterizer (task 7.3a)

Plan.md §6 Phase 7 ("glyph outlines through the same path code"; "Proven: totality, resource
bounds"), ISO 32000-2 §9.4.4 (text rendering matrix), §9.3.6 (text rendering modes), §9.6–9.7
(simple and composite fonts), §9.9 (embedded font programs).

## Pipeline

1. **Glyph sources** (`GlyphSource`, `loadSources`): per font of the page (keyed by
   `Text.FontKey`, exactly as `Text.loadFonts` keys its `FontTable`), the embedded program
   and the code → glyph map:
   * simple `/Type1`, `/MMType1`: the `/FontFile` program (`Font.Type1.Font1.outline`, by
     glyph name through the font's encoding: `/Encoding` with `/Differences` over the
     built-in one), else a `/FontFile3 /Type1C` program (`Font.CFF.CFFFont.outline`, glyph
     name → GID through the charset, else the CFF's own encoding);
   * simple `/TrueType`: `/FontFile2` (`TTFont.glyphOfCode` with the font's symbolic flag and
     encoding, §9.6.6.4; `TTFont.glyphOutline`);
   * `/Type0`: CID = the code's big-endian value (as `Text` positions it), a `/CIDFontType0`
     descendant with `/FontFile3` (CID → GID through the CFF charset), or a
     `/CIDFontType2` descendant with `/FontFile2` (CID → GID through `/CIDToGIDMap`).
   The font matrix (`GlyphSource.matrix`, glyph space → text space) is the Type 1 or CFF
   `/FontMatrix`, `1/unitsPerEm` for TrueType, and for CID-keyed CFF the uniform scale of the
   effective matrix's `a` entry (`CFFFont.matrixAOf`: the Font DICT matrix composed with the
   Top DICT matrix; only `a` is kept by 6.2, so skewed Font DICT matrices are not rendered
   exactly — recorded as a gap).
   **Not rendered** (draw nothing): fonts without an embedded program (the standard 14 and
   other non-embedded fonts — MuPDF substitutes URW fonts; we ship none: a gap), Type 3 fonts
   (running their charprocs through the interpreter is out of scope), OpenType-wrapped CFF,
   glyphs a font rejects.
2. **Positions** come from `Text.layoutParts` with the page's `FontTable` (the same widths,
   `Tc`, `Tw`, `Tz`, `TJ` adjustments the display list was built with), so rendering and
   extraction place every glyph at the same offset `tx` (C6).
3. **Transform** (§9.4.4): glyph space → device subpixels by
   `FontMatrix × [Tfs·Th 0 0 Tfs tx Trise] × Tm × CTM × view`, exact over `ℚ`, each point
   rounded once (`Fill.FPt.ofPt`). TrueType quadratics become cubics by exact degree elevation
   in device space (`c1 = p0 + 2/3(q − p0)`, `c2 = p + 2/3(q − p)`; affine maps commute with
   elevation).
4. **Painting**: all glyphs of a run form one device path, filled once with the nonzero rule
   (7.2a), stroked once (7.2b, line style and CTM of the run's stroke snapshot), composited
   once per paint through the run's clip (7.2c). Glyph contours of one font share an
   orientation, so overlapping glyphs stay filled under nonzero. Render modes: 0 fill,
   1 stroke, 2 fill then stroke, 3 nothing, 4–6 as 0–2, 7 nothing. **Gap**: modes 4–7 should
   also add the glyphs to the clip of the enclosing text object; the display list does not
   model text clipping yet (5.2), so the clip side effect is not applied.
5. **Outline cache** (`Cache`): outlines (glyph space, so reusable at any size and position)
   keyed by `(FontKey, GKey)`, at most `glyphCacheCap` entries (most recent first, the oldest
   dropped); a missing outline is cached too.

## Bounds

Every outline has at most `Outline.maxOutlineSegs` segments (by its type; the charstring
interpreters keep their stack, nesting and fuel bounds); the device path of one run has at
most `maxRunSegs` segments (`runPath_size_le`: further glyphs of the run are not drawn — a
documented degradation, never an error); the cache holds at most `glyphCacheCap` outlines
(`Cache.insert_length_le`); the rendered page keeps its `4 · w · h` bytes (`renderPage_size`).
The fill and stroke work of a run is then 7.2a/7.2b's bound for a path of at most
`maxRunSegs` segments.

## Wiring (driver and hook)

`renderPage` is a complete page renderer: path items through `Clip.renderItem`, glyph runs
here, in display-list order. `renderDocPage` runs it on a page of an opened document. To paint
text from `Clip.renderPaths` instead, see `runMasks` (a stateless per-run hook).
-/

namespace SafePdf.Core.Raster.Glyph

open SafePdf SafePdf.Core
open SafePdf.Core.Content
open SafePdf.Core.Raster.Geom
open SafePdf.Core.Raster.Fill
open SafePdf.Core.Font.Outline (Outline OSeg)
open SafePdf.Core.Text (FontKey FontTable FontInfo)

/-! ## 1. Glyph sources -/

/-- A glyph of a font program: its GID (CFF, TrueType) or its name (Type 1). -/
inductive GKey where
  /-- Glyph id. -/
  | gid (n : Nat)
  /-- Glyph name. -/
  | name (s : String)
  deriving DecidableEq, Repr, Inhabited

/-- What rendering needs from a font: code → glyph, glyph → outline (glyph space), glyph
space → text space. -/
structure GlyphSource where
  /-- The glyph a character code selects. -/
  glyphOf : List UInt8 → Option GKey
  /-- The outline of a glyph, glyph space. -/
  outline : GKey → Option Outline
  /-- The font matrix of a glyph (glyph space → text space). -/
  matrix : GKey → Aff
  /-- Short description (program kind), for diagnostics. -/
  desc : String

/-- A font that draws nothing (no embedded program, Type 3, unsupported). -/
def GlyphSource.none (desc : String) : GlyphSource :=
  ⟨fun _ => .none, fun _ => .none, fun _ => Aff.id, desc⟩

/-- A one-byte code. -/
def oneByte : List UInt8 → Option UInt8
  | [b] => some b
  | _ => .none

/-- A simple font with a Type 1 program: glyphs by name through `enc`. -/
def type1Source (f : Font.Type1.Font1) (enc : Font.Encoding) : GlyphSource where
  glyphOf c := (oneByte c).bind fun b => (enc.glyph b.toNat).map .name
  outline
    | .name n => f.outline n
    | .gid _ => .none
  matrix _ := Aff.ofMatrix f.fontMatrix
  desc := "Type1 FontFile"

/-- A simple font with a CFF program: name through `enc` → GID through the charset, else the
code through the CFF's own encoding (as `Text.cffCodeAdvance`). -/
def cffSource (f : Font.CFF.CFFFont) (enc : Font.Encoding) : GlyphSource where
  glyphOf c := (oneByte c).bind fun b =>
    match (enc.glyph b.toNat).bind f.gidOfName? with
    | some g => some (.gid g)
    | .none => (f.gidOfCode b).map .gid
  outline
    | .gid g => f.outline g
    | .name _ => .none
  matrix _ := Aff.ofMatrix f.fontMatrix
  desc := "Type1C FontFile3"

/-- The uniform scale matrix `[s 0 0 s 0 0]`. -/
def uscale (s : Rat) : Aff := Aff.scale s s

/-- A CIDFont with a CFF program: CID = the code's value, GID through the charset. -/
def cidCFFSource (f : Font.CFF.CFFFont) : GlyphSource where
  glyphOf c := (f.gidOfCID (Font.CMap.beValue c)).map .gid
  outline
    | .gid g => f.outline g
    | .name _ => .none
  matrix
    | .gid g => if f.isCID then uscale (decimalToRat (f.matrixAOf g)) else Aff.ofMatrix f.fontMatrix
    | .name _ => Aff.ofMatrix f.fontMatrix
  desc := "CIDFontType0C FontFile3"

/-- The TrueType font matrix: `1 / unitsPerEm`. -/
def ttMatrix (f : Font.TrueType.TTFont) : Aff := uscale (1 / (f.unitsPerEm : Rat))

/-- A simple TrueType font (§9.6.6.4). -/
def ttSource (f : Font.TrueType.TTFont) (symbolic : Bool) (enc : Font.Encoding) : GlyphSource where
  glyphOf c := (oneByte c).bind fun b => (f.glyphOfCode b symbolic enc).map .gid
  outline
    | .gid g => f.glyphOutline g
    | .name _ => .none
  matrix _ := ttMatrix f
  desc := "TrueType FontFile2"

/-- A `/CIDFontType2` font: CID = the code's value, GID through `/CIDToGIDMap`. -/
def cidTTSource (f : Font.TrueType.TTFont) (m : Text.CIDToGID) : GlyphSource where
  glyphOf c := (m.gid (Font.CMap.beValue c)).map .gid
  outline
    | .gid g => f.glyphOutline g
    | .name _ => .none
  matrix _ := ttMatrix f
  desc := "CIDFontType2 FontFile2"

/-- The glyph source of a font object (see the module doc). -/
def buildSource {σ : Type} (limits : Limits) (src : Source σ) (s0 : σ) (fontObj : PdfObject) :
    GlyphSource × σ :=
  let resolve := fun o => (Run.resolve src s0 o).1
  let fd : Dict := match resolve fontObj with
    | .dict d => d
    | _ => []
  let subtype := (Text.nameStr? (Font.getR resolve fd "Subtype")).getD ""
  if subtype == "Type0" then
    let desc : Dict :=
      match Font.getR resolve fd "DescendantFonts" with
      | some (.array (d :: _)) =>
        match resolve d with
        | .dict dd => dd
        | _ => []
      | _ => []
    let dsub := (Text.nameStr? (Font.getR resolve desc "Subtype")).getD ""
    if dsub == "CIDFontType0" then
      match Text.loadCFF limits src s0 resolve desc ["CIDFontType0C", "Type1C"] with
      | (some f, s) => (cidCFFSource f, s)
      | (.none, s) => (GlyphSource.none "Type0 (no program)", s)
    else if dsub == "CIDFontType2" then
      match Text.loadTT limits src s0 resolve desc with
      | (some f, s) =>
        let (m, s) := Text.loadCIDToGID src s desc
        (cidTTSource f m, s)
      | (.none, s) => (GlyphSource.none "Type0 (no program)", s)
    else (GlyphSource.none "Type0 (unknown descendant)", s0)
  else if subtype == "Type1" || subtype == "MMType1" then
    match Text.loadType1 limits src s0 resolve fd with
    | (some f, s) =>
      (type1Source f (Font.SimpleMetrics.ofDict resolve fd (some f.encoding)).encoding, s)
    | (.none, s) =>
      match Text.loadCFF limits src s resolve fd ["Type1C"] with
      | (some f, s) =>
        (cffSource f (Font.SimpleMetrics.ofDict resolve fd (some (Text.cffEncoding f))).encoding, s)
      | (.none, s) => (GlyphSource.none s!"{subtype} (not embedded)", s)
  else if subtype == "TrueType" then
    match Text.loadTT limits src s0 resolve fd with
    | (some f, s) =>
      (ttSource f (Text.isSymbolic resolve fd) (Font.SimpleMetrics.ofDict resolve fd .none).encoding, s)
    | (.none, s) => (GlyphSource.none "TrueType (not embedded)", s)
  else (GlyphSource.none s!"{subtype} (not rendered)", s0)

/-- Glyph sources by font key (the keys of `Text.FontTable`). -/
abbrev SourceTable := List (FontKey × GlyphSource)

/-- The source of a font reference: by its key, else the page's font of that name (as
`Text.FontTable.get`). -/
def SourceTable.get (t : SourceTable) (f : FontRef) : Option GlyphSource :=
  match t.lookup (Text.fontKey f) with
  | some g => some g
  | .none => t.lookup (.res 0 f.name)

/-- **Glyph sources of a page**: every font `Text.scanFonts` collects from the page resources,
each font object built once, at most `Text.maxFonts` (as `Text.loadFonts`). -/
def loadSources {σ : Type} (limits : Limits) (src : Source σ) (s : σ) (res : Dict) :
    SourceTable × σ :=
  let (es, s) := Text.scanFonts src (Text.maxFormFonts + 1) [(0, res)] [] [] s
  let (t, _, s) := es.foldl (fun (acc : SourceTable × Nat × σ) (e : Text.FontEntry) =>
    let (t, k, s) := acc
    let (key, keys, o) := e
    let add (g : GlyphSource) : SourceTable :=
      t ++ (keys.filter fun k' => (t.lookup k').isNone).map fun k' => (k', g)
    match t.lookup key with
    | some g => (add g, k, s)
    | .none =>
      if Text.maxFonts ≤ k then acc
      else
        let (g, s') := buildSource limits src s o
        (add g, k + 1, s')) (([] : SourceTable), 0, s)
  (t, s)

/-! ## 2. Outline cache -/

/-- Most outlines cached per page (local constant). -/
def glyphCacheCap : Nat := 512

/-- Outlines by `(font, glyph)`, most recent first (a missing outline is cached as `none`). -/
structure Cache where
  /-- The entries. -/
  entries : List ((FontKey × GKey) × Option Outline) := []
  /-- Lookups answered from the cache. -/
  hits : Nat := 0

/-- Insert an entry, dropping the oldest beyond `glyphCacheCap`. -/
def Cache.insert (c : Cache) (k : FontKey × GKey) (o : Option Outline) : Cache :=
  { c with entries := ((k, o) :: c.entries).take glyphCacheCap }

/-- The cache never holds more than `glyphCacheCap` outlines. -/
theorem Cache.insert_length_le (c : Cache) (k : FontKey × GKey) (o : Option Outline) :
    (c.insert k o).entries.length ≤ glyphCacheCap := by
  simp only [Cache.insert, List.length_take]; exact Nat.min_le_left _ _

/-- The outline of a glyph, from the cache or computed (and inserted). -/
def Cache.outline (c : Cache) (fk : FontKey) (gs : GlyphSource) (g : GKey) :
    Option Outline × Cache :=
  match c.entries.lookup (fk, g) with
  | some o => (o, { c with hits := c.hits + 1 })
  | .none =>
    let o := gs.outline g
    (o, c.insert (fk, g) o)

/-! ## 3. Outlines in device space -/

/-- `p + 2/3 (q − p)`. -/
def twoThirds (p q : Pt) : Pt := ⟨p.x + 2 / 3 * (q.x - p.x), p.y + 2 / 3 * (q.y - p.y)⟩

/-- One outline segment through `m` (glyph space → device pixels), with the device current
point before and after it; `lim` clamps the subpixel coordinates. -/
def segToD (lim : Int) (m : Aff) (cur : Pt) : OSeg → DSeg × Pt
  | .moveTo p =>
    let q := m.apply (ptOfPoint p)
    (.moveTo (FPt.ofPt q lim), q)
  | .lineTo p =>
    let q := m.apply (ptOfPoint p)
    (.lineTo (FPt.ofPt q lim), q)
  | .quadTo c p =>
    let qc := m.apply (ptOfPoint c)
    let q := m.apply (ptOfPoint p)
    (.curveTo (FPt.ofPt (twoThirds cur qc) lim) (FPt.ofPt (twoThirds q qc) lim) (FPt.ofPt q lim), q)
  | .curveTo c1 c2 p =>
    let q := m.apply (ptOfPoint p)
    (.curveTo (FPt.ofPt (m.apply (ptOfPoint c1)) lim) (FPt.ofPt (m.apply (ptOfPoint c2)) lim)
      (FPt.ofPt q lim), q)
  | .close => (.closePath, cur)

/-- An outline as a device path: one device segment per outline segment. -/
def outlineToD (lim : Int) (m : Aff) (o : Outline) : DPath :=
  (o.1.foldl (fun (acc : DPath × Pt) s =>
    let r := segToD lim m acc.2 s
    (acc.1.push r.1, r.2)) (#[], ⟨0, 0⟩)).1

private theorem foldl_segToD_size (lim : Int) (m : Aff) (l : List OSeg) :
    ∀ (acc : DPath × Pt), (l.foldl (fun (acc : DPath × Pt) s =>
      let r := segToD lim m acc.2 s
      (acc.1.push r.1, r.2)) acc).1.size = acc.1.size + l.length := by
  induction l with
  | nil => intro acc; simp
  | cons s rest ih =>
    intro acc
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]; simp only [Array.size_push]; omega

/-- **Size law**: the device path of an outline has as many segments as the outline (so at
most `Outline.maxOutlineSegs`). -/
theorem outlineToD_size (lim : Int) (m : Aff) (o : Outline) :
    (outlineToD lim m o).size = o.1.size := by
  unfold outlineToD
  rw [← Array.foldl_toList, foldl_segToD_size]
  simp

/-! ## 4. Glyph runs -/

/-- Most device segments of one glyph run (local constant; further glyphs of the run are not
drawn). -/
def maxRunSegs : Nat := 1048576

/-- Append a glyph's device path unless the run would exceed `maxRunSegs`. -/
def addGlyph (acc d : DPath) : DPath := if acc.size + d.size ≤ maxRunSegs then acc ++ d else acc

/-- `addGlyph` keeps the run within `maxRunSegs`. -/
theorem addGlyph_size_le (acc d : DPath) (h : acc.size ≤ maxRunSegs) :
    (addGlyph acc d).size ≤ maxRunSegs := by
  unfold addGlyph; split
  · simp only [Array.size_append]; omega
  · exact h

/-- The text-space matrix of a glyph at offset `tx`: `[Tfs·Th 0 0 Tfs tx Trise]`. -/
def glyphPlacement (r : GlyphRun) (tx : Fixed) : Aff :=
  let th := Fixed.toRat r.horizScaling / 100
  let tfs := Fixed.toRat r.font.size
  ⟨tfs * th, 0, 0, tfs, Fixed.toRat tx, Fixed.toRat r.rise⟩

/-- One step of `runPath`: the glyph of a laid-out code appended to the run's path. -/
def glyphStep (lim : Int) (fk : FontKey) (gs : GlyphSource) (r : GlyphRun) (rm : Aff)
    (acc : DPath × Cache) (e : List UInt8 × Fixed × Fixed) : DPath × Cache :=
  match gs.glyphOf e.1 with
  | .none => acc
  | some g =>
    match acc.2.outline fk gs g with
    | (.none, c) => (acc.1, c)
    | (some o, c) =>
      let m := gs.matrix g * glyphPlacement r e.2.1 * rm
      (addGlyph acc.1 (outlineToD lim m o), c)

/-- **The device path of a glyph run** through `view` (page → device pixels): every laid-out
code's glyph outline (positions from `Text.layoutParts` with the font's `FontInfo`), at most
`maxRunSegs` segments; and the updated cache. -/
def runPath (cfg : Fill.Config) (view : Aff) (fi : FontInfo) (fk : FontKey) (gs : GlyphSource)
    (r : GlyphRun) (cache : Cache) : DPath × Cache :=
  let entries := Text.layoutParts fi (Text.runTextState r) r.font.size Fixed.zero r.parts
  let rm := Aff.ofMatrix r.tm * Aff.ofMatrix r.ctm * view
  entries.foldl (glyphStep (cfg.coordLimit : Int) fk gs r rm) (#[], cache)

private theorem foldl_glyphStep_le (lim : Int) (fk : FontKey) (gs : GlyphSource) (r : GlyphRun)
    (rm : Aff) (l : List (List UInt8 × Fixed × Fixed)) :
    ∀ (acc : DPath × Cache), acc.1.size ≤ maxRunSegs →
      (l.foldl (glyphStep lim fk gs r rm) acc).1.size ≤ maxRunSegs := by
  induction l with
  | nil => intro acc h; exact h
  | cons e rest ih =>
    intro acc h
    simp only [List.foldl_cons]
    apply ih
    unfold glyphStep
    split
    · exact h
    · split
      · exact h
      · exact addGlyph_size_le _ _ h

/-- **Run bound**: the device path of a run has at most `maxRunSegs` segments. -/
theorem runPath_size_le (cfg : Fill.Config) (view : Aff) (fi : FontInfo) (fk : FontKey)
    (gs : GlyphSource) (r : GlyphRun) (cache : Cache) :
    (runPath cfg view fi fk gs r cache).1.size ≤ maxRunSegs :=
  foldl_glyphStep_le _ _ _ _ _ _ _ (by simp [maxRunSegs])

/-- Whether a render mode fills (0, 2, 4, 6). -/
def TextRenderMode.fills : TextRenderMode → Bool
  | .fill | .fillStroke | .fillClip | .fillStrokeClip => true
  | _ => false

/-- Whether a render mode strokes (1, 2, 5, 6). -/
def TextRenderMode.strokes : TextRenderMode → Bool
  | .stroke | .fillStroke | .strokeClip | .fillStrokeClip => true
  | _ => false

/-- The page's fonts for rendering: positions (`Text.FontTable`) and outlines. -/
structure PageFonts where
  /-- Widths and code splitting (as text extraction). -/
  fonts : FontTable
  /-- Glyph programs. -/
  sources : SourceTable
  /-- Decoded image XObjects (task 7.3b). -/
  images : Image.ImageTable := {}
  /-- Shadings and shading patterns of the page (task 7.3d). -/
  shadings : Shading.ShadingTable := {}

/-- **Per-run hook**: the coverage masks of a glyph run inside the device window `win`, in
painting order, each with its colour, alpha and counted work: the fill (modes 0, 2, 4, 6) then
the stroke (modes 1, 2, 5, 6); nothing for modes 3 and 7 or a font without outlines. -/
def runMasks (cfg : Fill.Config) (view : Aff) (win : IRect) (pf : PageFonts) (cache : Cache)
    (r : GlyphRun) : List (Mask × Color × Comp × Nat) × Cache :=
  if !r.renderMode.paints then ([], cache) else
  match pf.sources.get r.font with
  | .none => ([], cache)
  | some gs =>
    let (dp, cache) := runPath cfg view (pf.fonts.get r.font) (Text.fontKey r.font) gs r cache
    if dp.size = 0 then ([], cache) else
    let fillM : List (Mask × Color × Comp × Nat) :=
      if TextRenderMode.fills r.renderMode then
        let f := fillEdgesCounted (flatten cfg win dp) .nonzero win cfg
        [(f.1, r.fill.color, r.fill.alpha, f.2)]
      else []
    let strokeM : List (Mask × Color × Comp × Nat) :=
      if TextRenderMode.strokes r.renderMode then
        let geo := Stroke.Geo.make (Stroke.userToSub view r.stroke.ctm)
          (Fixed.toRat r.stroke.line.width) cfg
        let es := Stroke.strokeDPath cfg geo r.stroke.line dp
        [(fillEdges es .nonzero win cfg, r.stroke.color, r.stroke.alpha, 0)]
      else []
    (fillM ++ strokeM, cache)

/-! ## 5. Pages -/

/-- Rendering state: the path renderer's state and the outline cache. -/
structure TState where
  /-- Page buffer, clip cache, counted work. -/
  rs : Clip.RState
  /-- Outline cache. -/
  cache : Cache := {}
  /-- Transparency layers and soft masks (task 7.3c). -/
  tx : Transparency.TxState := {}

/-- Paint a list of masks through one clip (cache and work of `clipMaskC` charged once). -/
def paintAll (W H : Nat) (cm : Option Mask) (cc : Clip.ClipCache) (s : Nat) (st : Clip.RState) :
    List (Mask × Color × Comp × Nat) → Clip.RState
  | [] => { st with cache := cc, steps := st.steps + s }
  | (m, col, a, w) :: rest =>
    paintAll W H cm cc 0 (Clip.paintMask W H st cm m col a cc (s + w)) rest

/-- Render one display item: glyph runs here, everything else by `Clip.renderItem`. -/
def renderItemG (cfg : Fill.Config) (m : Aff) (W H : Nat) (stroke : Clip.StrokeFn) (pf : PageFonts)
    (st : TState) : DisplayItem → TState
  | .glyphRun r clip =>
    if !r.renderMode.paints then st else
    let c := Clip.clipMaskC cfg m W H st.rs.cache clip
    let (ms, cache) := runMasks cfg m (Clip.itemWindow W H c.1) pf st.cache r
    { st with rs := paintAll W H c.1 c.2.1 c.2.2 st.rs ms, cache }
  | .image src ctm fill clip => { st with rs := Image.renderImage cfg m W H pf.images st.rs src ctm fill clip }
  | .shading name ctm clip => { st with rs := Shading.renderShading cfg m W H pf.shadings st.rs name ctm clip }
  | .fillPath p rule style clip => { st with rs := Shading.renderFill cfg m W H pf.shadings st.rs p rule style clip }
  | it => { st with rs := Clip.renderItem cfg m W H stroke st.rs it }

/-- `paintAll` preserves the buffer size. -/
theorem paintAll_size (W H : Nat) (cm : Option Mask) (cc : Clip.ClipCache) :
    ∀ (s : Nat) (st : Clip.RState) (l : List (Mask × Color × Comp × Nat)),
      (paintAll W H cm cc s st l).buf.size = st.buf.size
  | _, _, [] => rfl
  | s, st, (m, col, a, w) :: rest => by
    simp only [paintAll]
    rw [paintAll_size W H cm cc 0 _ rest]
    simp only [Clip.paintMask, Clip.composite_size]

/-- One item preserves the buffer size. -/
theorem renderItemG_size (cfg : Fill.Config) (m : Aff) (W H : Nat) (stroke : Clip.StrokeFn)
    (pf : PageFonts) (st : TState) (it : DisplayItem) :
    (renderItemG cfg m W H stroke pf st it).rs.buf.size = st.rs.buf.size := by
  cases it with
  | glyphRun r clip =>
    simp only [renderItemG]
    split
    · rfl
    · exact paintAll_size _ _ _ _ _ _ _
  | image src ctm fill clip => simp only [renderItemG]; exact Image.renderImage_size _ _ _ _ _ _ _ _ _ _
  | shading name ctm clip => simp only [renderItemG]; exact Shading.renderShading_size _ _ _ _ _ _ _ _ _
  | fillPath p rule style clip => simp only [renderItemG]; exact Shading.renderFill_size _ _ _ _ _ _ _ _ _ _
  | _ => simp only [renderItemG]; exact Clip.renderItem_size _ _ _ _ _ _ _

/-- `renderItemG` keeps the transparency state. -/
theorem renderItemG_tx (cfg : Fill.Config) (m : Aff) (W H : Nat) (stroke : Clip.StrokeFn)
    (pf : PageFonts) (st : TState) (it : DisplayItem) :
    (renderItemG cfg m W H stroke pf st it).tx = st.tx := by
  cases it <;> simp only [renderItemG] <;> (try split) <;> rfl

/-- The transparency driver's view of `TState` (task 7.3c). -/
def painterG (cfg : Fill.Config) (m : Aff) (W H : Nat) (stroke : Clip.StrokeFn) (pf : PageFonts) :
    Transparency.Painter TState where
  buf := (·.rs.buf)
  setBuf := fun st b => { st with rs := { st.rs with buf := b } }
  tx := (·.tx)
  setTx := fun st t => { st with tx := t }
  paint := renderItemG cfg m W H stroke pf

/-- `painterG` is lawful. -/
theorem painterG_lawful (cfg : Fill.Config) (m : Aff) (W H : Nat) (stroke : Clip.StrokeFn)
    (pf : PageFonts) : (painterG cfg m W H stroke pf).Lawful where
  buf_setBuf := fun _ _ => rfl
  tx_setBuf := fun _ _ => rfl
  buf_setTx := fun _ _ => rfl
  tx_setTx := fun _ _ => rfl
  paint_size := renderItemG_size cfg m W H stroke pf
  paint_tx := renderItemG_tx cfg m W H stroke pf

private theorem foldl_renderItemG_size (cfg : Fill.Config) (m : Aff) (W H : Nat)
    (stroke : Clip.StrokeFn) (pf : PageFonts) (l : List DisplayItem) :
    ∀ (st : TState), (l.foldl (renderItemG cfg m W H stroke pf) st).rs.buf.size =
      st.rs.buf.size := by
  induction l with
  | nil => intro st; rfl
  | cons it rest ih => intro st; simp only [List.foldl, ih, renderItemG_size]

/-- Render a display list (paths and glyph runs) onto a white `W × H` page through `m`. -/
def renderItems (cfg : Fill.Config) (m : Aff) (W H : Nat) (pf : PageFonts) (items : DisplayList)
    (stroke : Clip.StrokeFn := Clip.defaultStroke) : TState :=
  items.foldl (Transparency.renderTx (painterG cfg m W H stroke pf) W H Transparency.maxMaskDepth)
    { rs := { buf := Clip.whiteBuf W H } }

/-- **Render a page** (paths and text) at zoom `zoom` and user rotation `rot`, onto its
CropBox (as `Clip.renderPaths`, plus glyph runs). -/
def renderPage (page : Doc.Page) (zoom : Rat) (rot : Doc.Rotation) (pf : PageFonts)
    (items : DisplayList) (cfg : Fill.Config := {}) (stroke : Clip.StrokeFn := Clip.defaultStroke) :
    Clip.Image :=
  let r := rotAdd page.rotate rot
  let bx := Box.ofRect page.cropBox
  let sz := Clip.pageSize cfg.maxPageSide zoom r bx
  ⟨sz.1, sz.2, (renderItems cfg (viewMatrix zoom r bx) sz.1 sz.2 pf items stroke).rs.buf⟩

/-- **Buffer shape** of a rendered page: `4 · w · h` bytes. -/
theorem renderPage_size (page : Doc.Page) (zoom : Rat) (rot : Doc.Rotation) (pf : PageFonts)
    (items : DisplayList) (cfg : Fill.Config) (stroke : Clip.StrokeFn) :
    (renderPage page zoom rot pf items cfg stroke).data.size =
      4 * (renderPage page zoom rot pf items cfg stroke).w *
        (renderPage page zoom rot pf items cfg stroke).h := by
  simp only [renderPage, renderItems]
  exact Transparency.renderTx_items_size _ (painterG_lawful ..) _ _ _ items _
    (by simp [painterG, Clip.whiteBuf, ByteArray.size]) rfl

/-- **Render a page of an opened document**: decode its content, build the display list with
the fonts' advances (`Text.extractDocPage`), load the glyph programs, render. Total; charges
`budget` for every decoded stream. -/
def renderDocPage (limits : Limits) (doc : Doc.Doc) (page : Doc.Page) (zoom : Rat)
    (rot : Doc.Rotation) (budget : Filter.Budget) (cfg : Fill.Config := Fill.Config.ofLimits limits) :
    (Except Error Clip.Image) × Filter.Budget :=
  match Text.extractDocPage limits doc page budget with
  | (.error e, b) => (.error e, b)
  | (.ok pt, b) =>
    let (srcs, b) := loadSources limits (Text.docSource limits doc) b (page.resources.getD [])
    let (imgs, b) := Image.loadImages limits (Text.docSource limits doc) b (page.resources.getD []) pt.items
    let (shs, b) := Shading.loadShadings limits (Text.docSource limits doc) b (page.resources.getD []) pt.items
    (.ok (renderPage page zoom rot ⟨pt.fonts, srcs, imgs, shs⟩ pt.items cfg), b)

/-! ## 6. Checks -/

private def pt (x y : Int) : Point := ⟨Fixed.ofInt x, Fixed.ofInt y⟩

-- A unit-square outline scaled ×10 into device pixels: exactly 100 px.
#guard
  match Outline.ofArray #[.moveTo (pt 0 0), .lineTo (pt 1 0), .lineTo (pt 1 1), .lineTo (pt 0 1),
    .close] with
  | some o => (fillDPath (outlineToD 1073741824 (Aff.scale 10 10) o) .nonzero ⟨0, 0, 20, 20⟩).total
      == 100 * 255
  | none => false
-- A quadratic (parabola) segment: the area under it is 2/3 of its box (within 1%).
#guard
  match Outline.ofArray #[.moveTo (pt 0 0), .quadTo (pt 1 2) (pt 2 0), .close] with
  | some o =>
    let t := (fillDPath (outlineToD 1073741824 (Aff.scale 10 10) o) .nonzero ⟨0, 0, 40, 40⟩).total
    -- area 2/3 · 20 · 10 = 133.3 px
    13333 * 255 * 99 ≤ t * 10000 && t * 10000 ≤ 13333 * 255 * 101
  | none => false
#guard (Cache.insert {} (.res 0 ⟨[]⟩, .gid 1) none).entries.length == 1
#guard TextRenderMode.fills .fillStrokeClip && !TextRenderMode.fills .stroke &&
  TextRenderMode.strokes .fillStroke && !TextRenderMode.strokes .invisible

end SafePdf.Core.Raster.Glyph
