import SafePdf.Core.Raster.Tiling
import SafePdf.Core.Raster.Image
import SafePdf.Core.Text

/-!
# Type 3 fonts in the rasterizer (task 7.3j)

Plan.md §6 Phase 7 ("glyphs"; "Proven: totality, resource bounds"), §4 **S3**. ISO 32000-2
§9.6.4 (Type 3 fonts: `/FontMatrix`, `/FontBBox`, `/CharProcs`, `/Encoding`, `/Resources`),
§9.6.5 (glyph descriptions: `d0` — coloured, `d1` — uncoloured, painted with the current
colour as a mask), §9.4.4 (text rendering matrix). Behaviour follows MuPDF 1.25.1
(`source/fitz/font.c` `fz_prepare_t3_glyph`, `fz_render_t3_glyph_pixmap`; `pdf-type3.c`).

## Loading (`loadFont`)

A Type 3 font is loaded once per page from its font object: the exact `/FontMatrix` (over
`ℚ`, from the PDF decimals; default `[0.001 0 0 0.001 0 0]`), `/FontBBox`, `/Encoding`
(`Font.SimpleMetrics.ofDict`, as text extraction reads it), the font's `/Resources` (else the
page's, as MuPDF), `/CharProcs`. For every code `0 … 255` whose glyph name has a charproc, the
charproc stream is decoded and **run once** through the 5.2b runner (`Run.runOps`, a fresh
machine with identity CTM, so its display items are in **glyph space**; nesting fuel
`Limits.maxXObjectDepth`; the charproc's object on the visited path; resource owner the font
object, so `ResRef.form` entries resolve in the font's `/Resources`). A glyph name used by
several codes is run once (`T3Font.glyphs` holds the shared glyph per code: the cache per
(font, code)). The first `d0`/`d1` decides the kind: `d0` → **coloured** (the items' own
colours); `d1` or none → **masked** (MuPDF: `FZ_DEVFLAG_MASK`, or treated as masked).

Bounds (S3): at most `maxGlyphOps` operators per charproc, at most 256 charprocs per font
(one per distinct glyph name of the codes), at most `maxType3Fonts` fonts per page, and all
charprocs together run under the **shared page budget** (`Tiling.Budget`: what the page,
the annotations and the tiling cells left of `Limits.maxOpsPerPage` and the form cap). An
exhausted budget leaves the remaining glyphs empty.

**Glyph box** (`GBox`, glyph space): the bound of the items (fill paths; strokes widened by
`width · (|a|+|b|+|c|+|d|) · max(1, miterLimit)` of their CTM; images: the unit square
through their CTM), as MuPDF's bbox device; when an item has no finite bound (glyph runs,
shadings, soft masks) the `d1` box, else the `/FontBBox`, else the whole window.

## Rendering (`renderRun`)

Each laid-out code of a glyph run (`Text.layoutParts` with the font's `FontInfo`: the same
positions as extraction, C6) is drawn with the matrix
`T = FontMatrix × [Tfs·Th 0 0 Tfs tx Trise] × Tm × CTM × view` (exact over `ℚ`). The glyph
is rendered with the caller's **cell painter** (the full item painter at one depth less,
`Glyph.cellPainterD`; nested Type 3 glyphs and tiling cells share the depth cap, depth 0 =
paths only) as a premultiplied layer over the device box of `GBox` widened by one pixel (as
`fz_render_t3_glyph_pixmap`) ∩ the run's clip window (`Tiling.cellLayer`: rendered over
white and over black, coverage `α` recovered exactly). A **masked** glyph keeps only `α` and
takes the run's fill colour (`Tiling.layerLoop` with the colour: the charproc's colour
operators are ignored, image masks are painted as stencils of that colour). The layer is
blitted (`Tiling.blit`) through the run's clip mask with the fill alpha. Render modes: 3 and
7 paint nothing; every other mode paints the glyph once with the fill colour (MuPDF
renders Type 3 glyphs as filled; stroke and clip effects of modes 1, 2, 4–6 are not
applied — a documented gap, as are pattern fill colours on masked glyphs, which paint with
the pattern's device placeholder colour).

Layers larger than `maxGlyphLayerPixels` are not drawn (degradation, never an error).
`renderRun_size`: the page buffer keeps its size.

## Gaps

* No bitmap cache of rendered glyphs (MuPDF caches per subpixel position): every instance is
  rendered (two small renders); charproc display lists are cached.
* Fonts used by text inside charprocs are not loaded (such text is positioned with the
  runner's environment fonts); tiling patterns used inside charprocs are not loaded.
-/

namespace SafePdf.Core.Raster.Type3

open SafePdf SafePdf.Core
open SafePdf.Core.Raster.Geom
open SafePdf.Core.Raster.Fill (IRect Mask)
open SafePdf.Core.Content (Fixed Comp Color Source Matrix DisplayList DisplayItem Env St Frame
  GlyphRun Path Segment)
open SafePdf.Core.Text (FontInfo)

/-! ## 1. Caps -/

/-- Most operators run per charproc (local cap; candidate for `Limits`). -/
def maxGlyphOps : Nat := 100000

/-- Most Type 3 fonts loaded per page (local cap). -/
def maxType3Fonts : Nat := 64

/-- Largest layer (device pixels) rendered for one glyph instance (local cap). -/
def maxGlyphLayerPixels : Nat := 1 <<< 22

/-! ## 2. Glyphs and fonts -/

/-- A glyph-space box: empty (nothing painted), a rectangle `(x0, y0, x1, y1)`, or unbounded
(the window). -/
inductive GBox where
  /-- Nothing to paint. -/
  | empty
  /-- A rectangle, `x0 ≤ x1`, `y0 ≤ y1`. -/
  | box (x0 y0 x1 y1 : Rat)
  /-- No finite bound known. -/
  | all
  deriving DecidableEq, Repr, Inhabited

/-- Union of two boxes. -/
def GBox.union : GBox → GBox → GBox
  | .empty, b | b, .empty => b
  | .all, _ | _, .all => .all
  | .box a b c d, .box e f g h => .box (min a e) (min b f) (max c g) (max d h)

/-- The box of a list of points. -/
def GBox.ofPts (ps : List Pt) : GBox :=
  ps.foldl (fun acc p => acc.union (.box p.x p.y p.x p.y)) .empty

/-- Widen a box by `r` on every side. -/
def GBox.widen (r : Rat) : GBox → GBox
  | .box a b c d => .box (a - r) (b - r) (c + r) (d + r)
  | g => g

/-- A charproc run into glyph space. -/
structure T3Glyph where
  /-- The display items (glyph space). -/
  items : DisplayList
  /-- `d0`: the items' own colours; otherwise a mask painted with the fill colour. -/
  colored : Bool
  /-- The glyph box (glyph space). -/
  bbox : GBox
  /-- **Image glyphs** (bitmap fonts): when every item is an unclipped inline image (stencil
  masks, or any image in a coloured glyph), the decoded images with their CTMs (glyph space),
  drawn directly (`drawImages`); empty otherwise. -/
  images : Array (Image.Pixmap × Matrix) := #[]

/-- A loaded Type 3 font. -/
structure T3Font where
  /-- `/FontMatrix` (glyph space → text space), exact. -/
  matrix : Aff
  /-- The glyph of each code `0 … 255` (`none`: no charproc). -/
  glyphs : Array (Option T3Glyph)
  /-- Downscale cap for images (`Limits.maxImagePixels`). -/
  imageCap : Nat := 0

/-- The decoded images of an image glyph (`T3Glyph.images`): every item an inline image
without clip, decodable, a stencil mask unless the glyph is coloured; else `#[]`. -/
def imageGlyph (limits : Limits) (colored : Bool) (items : DisplayList) :
    Array (Image.Pixmap × Matrix) :=
  let r := items.foldl (fun (acc : Option (Array (Image.Pixmap × Matrix))) it =>
    match acc, it with
    | some a, .image (.inline params data) ctm _ [] =>
      match Image.decodeInline limits [] params data with
      | .ok pm => if pm.stencil || colored then some (a.push (pm, ctm)) else none
      | .error _ => none
    | _, _ => none) (some #[])
  match r with
  | some a => a
  | none => #[]

/-! ## 3. Loading -/

/-- An exact number (`int` or `real`). -/
def ratOf : PdfObject → Option Rat
  | .int i => some (i : Rat)
  | .real d => some (decimalToRat d)
  | _ => none

/-- A list of exact numbers (array elements resolved by `resolve`). -/
def ratsOf (resolve : PdfObject → PdfObject) : Option PdfObject → Option (List Rat)
  | some (.array xs) => xs.mapM fun x => ratOf (resolve x)
  | _ => none

/-- The `/FontMatrix` (default `[0.001 0 0 0.001 0 0]`). -/
def fontMatrix (resolve : PdfObject → PdfObject) (fd : Dict) : Aff :=
  match ratsOf resolve (Font.getR resolve fd "FontMatrix") with
  | some [a, b, c, d, e, f] => ⟨a, b, c, d, e, f⟩
  | _ => Aff.scale (1 / 1000) (1 / 1000)

/-- A normalised non-degenerate box from four numbers. -/
def boxOf : Option (List Rat) → GBox
  | some [a, b, c, d] =>
    if a = c ∨ b = d then .empty else .box (min a c) (min b d) (max a c) (max b d)
  | _ => .empty

/-- The points of a path. -/
def pathPts (p : Path) : List Pt :=
  p.segs.toList.flatMap fun
    | .moveTo q | .lineTo q => [ptOfPoint q]
    | .curveTo a b q => [ptOfPoint a, ptOfPoint b, ptOfPoint q]
    | .closePath => []

/-- `|q|`. -/
def absQ (q : Rat) : Rat := if q < 0 then -q else q

/-- The glyph-space box of one item (see the module doc); `.all` when unbounded. -/
def itemBox : DisplayItem → GBox
  | .fillPath p _ _ _ => GBox.ofPts (pathPts p)
  | .strokePath p st _ =>
    let m := Aff.ofMatrix st.ctm
    let ml := Fixed.toRat st.line.miterLimit
    let r := absQ (Fixed.toRat st.line.width) * (absQ m.a + absQ m.b + absQ m.c + absQ m.d) *
      (if ml < 1 then 1 else ml)
    (GBox.ofPts (pathPts p)).widen r
  | .image _ ctm _ _ =>
    let m := Aff.ofMatrix ctm
    GBox.ofPts [m.apply ⟨0, 0⟩, m.apply ⟨1, 0⟩, m.apply ⟨0, 1⟩, m.apply ⟨1, 1⟩]
  | .clip .. | .groupBegin _ | .groupEnd | .unsupported _ => .empty
  | _ => .all

/-- The glyph box: the items' bound, else (unbounded) the `d1` box, else `/FontBBox`, else
unbounded. -/
def glyphBox (items : DisplayList) (d1 fontBBox : GBox) : GBox :=
  match items.foldl (fun (acc : GBox) it => acc.union (itemBox it)) GBox.empty with
  | .all =>
    match d1, fontBBox with
    | .box .., _ => d1
    | _, .box .. => fontBBox
    | _, _ => .all
  | b => b

/-- The kind of a charproc: `(coloured, d1 box)` from its first `d0`/`d1` operator (`d0` →
coloured; `d1` or none → masked). -/
def kindOf (resolve : PdfObject → PdfObject) (ops : Array Content.Op) : Bool × GBox :=
  match ops.find? (fun o => o.op == [100, 48] || o.op == [100, 49]) with
  | some o =>
    if o.op == [100, 48] then (true, .empty)
    else (false, boxOf (ratsOf resolve (some (.array (o.operands.drop 2)))))
  | none => (false, .empty)

/-- **Run one charproc** (object `n g`) under the budget: `ops` capped at
`min bud.ops maxGlyphOps`, forms at `bud.forms`; the budget is charged what ran. -/
def runGlyph {σ ω : Type} (env : Env σ ω) (s : σ) (obs : ω) (bud : Tiling.Budget)
    (res : Dict) (owner : Nat) (fbb : GBox) (n g : Nat) :
    Option T3Glyph × σ × ω × Tiling.Budget :=
  let src := env.src
  match src.fetch s n g with
  | (.ok (.stream st), s) =>
    match src.decode s n st with
    | (.ok bytes, s) =>
      let lim := env.cfg.limits
      let cap := min bud.ops maxGlyphOps
      let env' : Env σ ω :=
        { env with cfg := { env.cfg with limits := { lim with maxOpsPerPage := cap } },
                   maxForms := bud.forms }
      let t := Content.Ops.tokenize { lim with maxOpsPerPage := cap } bytes
      let (colored, d1) := kindOf (fun o => (Content.Run.resolve src s o).1) t.ops
      let r := Content.Run.runOps env' lim.maxXObjectDepth ⟨res, [n], owner, 0, Matrix.identity⟩
        (St.init s obs) t.ops
      (some { items := r.items, colored, bbox := glyphBox r.items d1 fbb,
              images := imageGlyph lim colored r.items }, r.s, r.obs,
        { ops := bud.ops - r.ops, forms := bud.forms - r.forms })
    | (.error _, s) => (none, s, obs, bud)
  | (_, s) => (none, s, obs, bud)

/-- Accumulator of `loadFont`: glyphs by name, by code, the states and the budget. -/
structure LoadAcc (σ ω : Type) where
  /-- Charprocs already run, by glyph name. -/
  byName : List (String × Option T3Glyph)
  /-- Glyph per code so far. -/
  glyphs : Array (Option T3Glyph)
  /-- Source state. -/
  s : σ
  /-- Observer state. -/
  obs : ω
  /-- Budget left. -/
  bud : Tiling.Budget

/-- **Load a Type 3 font** from its font object (see the module doc); `none` unless it is a
`/Type3` font dictionary with `/CharProcs`. `pageRes`: the resources used when the font has
none. -/
def loadFont {σ ω : Type} (env : Env σ ω) (s : σ) (obs : ω) (bud : Tiling.Budget)
    (pageRes : Dict) (fontObj : PdfObject) : Option T3Font × σ × ω × Tiling.Budget :=
  let src := env.src
  let resolve := fun o => (Content.Run.resolve src s o).1
  let owner := match fontObj with
    | .ref n _ => n
    | _ => 0
  match resolve fontObj with
  | .dict fd =>
    if Text.nameStr? (Font.getR resolve fd "Subtype") != some "Type3" then (none, s, obs, bud) else
    let (procs, s) := match Dict.get? fd (Content.Run.nm "CharProcs") with
      | some o => Content.Run.dictOf src s o
      | none => ([], s)
    let (res, s) := match Dict.get? fd (Content.Run.nm "Resources") with
      | some o => Content.Run.dictOf src s o
      | none => (pageRes, s)
    let enc := (Font.SimpleMetrics.ofDict resolve fd none).encoding
    let fbb := boxOf (ratsOf resolve (Font.getR resolve fd "FontBBox"))
    let acc := (List.range 256).foldl (fun (acc : LoadAcc σ ω) code =>
      match enc.glyph code with
      | none => { acc with glyphs := acc.glyphs.push none }
      | some nm =>
        match acc.byName.lookup nm with
        | some g => { acc with glyphs := acc.glyphs.push g }
        | none =>
          let (g, s, obs, bud) := match Dict.get? procs (Content.Run.nm nm) with
            | some (.ref n gen) =>
              if acc.bud.ops = 0 then (none, acc.s, acc.obs, acc.bud)
              else runGlyph env acc.s acc.obs acc.bud res owner fbb n gen
            | _ => (none, acc.s, acc.obs, acc.bud)
          { byName := (nm, g) :: acc.byName, glyphs := acc.glyphs.push g, s, obs, bud })
      ⟨[], Array.mkEmpty 256, s, obs, bud⟩
    (some { matrix := fontMatrix resolve fd, glyphs := acc.glyphs,
            imageCap := env.cfg.limits.maxImagePixels }, acc.s, acc.obs, acc.bud)
  | _ => (none, s, obs, bud)

/-- The items of every glyph of a font (for the image and shading loaders). -/
def T3Font.allItems (f : T3Font) : DisplayList :=
  f.glyphs.foldl (fun acc g => match g with
    | some g => acc ++ g.items
    | none => acc) #[]

/-! ## 4. Rendering -/

/-- The text-space matrix of a glyph at offset `tx`: `[Tfs·Th 0 0 Tfs tx Trise]` (as
`Glyph.glyphPlacement`). -/
def placement (r : GlyphRun) (tx : Fixed) : Aff :=
  let th := Fixed.toRat r.horizScaling / 100
  let tfs := Fixed.toRat r.font.size
  ⟨tfs * th, 0, 0, tfs, Fixed.toRat tx, Fixed.toRat r.rise⟩

/-- A full-coverage mask over `r`. -/
def fullMask (r : IRect) : Mask :=
  { x0 := r.x0, y0 := r.y0, w := r.width, h := r.height,
    data := ByteArray.mk (Array.replicate (r.width * r.height) 255) }

/-- The device rectangle of a glyph box through `T`, widened by one pixel, inside `win`
(`none`: nothing to paint). -/
def glyphRect (T : Aff) (win : IRect) : GBox → Option IRect
  | .empty => none
  | .all => some win
  | .box a b c d =>
    let r := Tiling.devRect T (a, b, c, d)
    some (IRect.inter ⟨r.x0 - 1, r.y0 - 1, r.x1 + 1, r.y1 + 1⟩ win)

/-- **Place an image inside a Type 3 glyph** (`Image.place` without grid fitting): MuPDF's
draw device does not grid-fit images while it renders a Type 3 glyph
(`FZ_DRAWDEV_FLAGS_TYPE3` in `fz_draw_fill_image_mask`/`fz_transform_pixmap`); grid fitting
every small glyph bitmap outward to whole pixels would embolden bitmap fonts. Otherwise the
same steps as `Image.place` (smooth): area-averaging downscale, then the sampling plan. -/
def placeNoFit (cap W H : Nat) (pm0 : Image.Pixmap) (dev : Aff) (cm : Option Mask)
    (rgb : Nat × Nat × Nat) (alpha : Nat) (buf : ByteArray) : ByteArray × Nat :=
  if dev.det = 0 then (buf, 0) else
  let down := Image.downscales cap pm0 dev true
  let pm := if down then
      Image.boxDown pm0 (Image.targetSide (dev.a * dev.a + dev.b * dev.b) pm0.w)
        (Image.targetSide (dev.c * dev.c + dev.d * dev.d) pm0.h)
    else pm0
  let A := Aff.inv dev * ⟨(pm.w : Rat), 0, 0, -(pm.h : Rat), 0, (pm.h : Rat)⟩
  let r := Image.placeRect W H dev cm
  let P := Image.mkPlan pm dev A cm rgb alpha true
  let cd := match cm with | some c => c.data | none => ByteArray.empty
  let cx := match cm with | some c => c.x0 | none => 0
  let cy := match cm with | some c => c.y0 | none => 0
  let cw := match cm with | some c => c.w | none => 0
  (Image.rowLoop P cd W A r cx cy cw r.height r.y0 buf,
    r.width * r.height + if down then pm0.w * pm0.h else 0)

/-- `placeNoFit` preserves the buffer size. -/
theorem placeNoFit_size (cap W H : Nat) (pm : Image.Pixmap) (dev : Aff) (cm : Option Mask)
    (rgb : Nat × Nat × Nat) (alpha : Nat) (buf : ByteArray) :
    (placeNoFit cap W H pm dev cm rgb alpha buf).1.size = buf.size := by
  unfold placeNoFit
  split
  · rfl
  · exact Image.rowLoop_size _ _ _ _ _ _ _ _ _ _ _

/-! ### Axis-aligned stencils: exact area coverage

pdfTeX bitmap fonts draw every glyph as a stencil mask much larger than its device size
(600 dpi PK bitmaps shown at screen resolution). MuPDF scales such a glyph bitmap to its exact
fractional device rectangle with a box filter (`fz_transform_pixmap` → `fz_scale_pixmap`),
which anti-aliases its edges; sampling (`Image.place`) would drop thin stems. For an
axis-aligned image matrix, `stencilMask` computes for every device pixel the **area-weighted
mean** of the stencil's coverage over the pixel (separable: per axis, each sample's device
interval split over the pixel cells it overlaps, weights in units of `2⁻¹⁶` px; sample
boundaries `p₀ + (p₁ − p₀)·k / n`, floored). -/

/-- One device pixel in fixed point (`2¹⁶`). -/
def fxOne : Int := 65536

/-- `q` in fixed point (`2¹⁶`), rounded. -/
def toFx (q : Rat) : Int := (q * 65536 + 1 / 2).floor

/-- Most device pixels along an axis of an exactly filtered stencil (local cap; larger images
go through `placeNoFit`). -/
def maxStencilSide : Nat := 4096

/-- `⌊a / b⌋` for `b > 0` (Euclidean on `Int`, `b` positive). -/
def fdivI (a b : Int) : Int := Int.fdiv a b

/-- Per-axis weights: the first device cell `lo` and, for each of the `n` cells, the samples
overlapping it with their overlap (`2⁻¹⁶` px units); samples `0 … ns − 1` span
`[p₀, p₁]` (fixed point, either order). -/
def axisWeights (p0 p1 : Int) (ns : Nat) : Int × Array (List (Nat × Nat)) :=
  let lo := fdivI (min p0 p1) fxOne
  let hi := fdivI (max p0 p1 + fxOne - 1) fxOne
  let n := (hi - lo).toNat
  let bnd := fun (k : Nat) => p0 + fdivI ((p1 - p0) * (k : Int)) (max 1 (ns : Int))
  let cells := (List.range ns).foldl (fun (cells : Array (List (Nat × Nat))) k =>
    let s0 := min (bnd k) (bnd (k + 1))
    let s1 := max (bnd k) (bnd (k + 1))
    let c0 := fdivI s0 fxOne
    let c1 := fdivI (s1 + fxOne - 1) fxOne
    (List.range (c1 - c0).toNat).foldl (fun cells (d : Nat) =>
      let X := c0 + d
      let ov := min s1 ((X + 1) * fxOne) - max s0 (X * fxOne)
      if ov ≤ 0 then cells else cells.modify (X - lo).toNat (fun l => (k, ov.toNat) :: l))
      cells) (Array.replicate n [])
  (lo, cells)

/-- **Exact coverage mask of an axis-aligned stencil** `pm` placed by `dev` (`b = c = 0`):
`none` when the matrix is not axis-aligned or the device rectangle exceeds
`maxStencilSide` along an axis. -/
def stencilMask (pm : Image.Pixmap) (dev : Aff) : Option Mask :=
  if dev.b ≠ 0 ∨ dev.c ≠ 0 then none else
  -- image space: column i ↔ u = i / w; row j ↔ v = 1 − j / h
  let (lx, wx) := axisWeights (toFx dev.e) (toFx (dev.e + dev.a)) pm.w
  let (ly, wy) := axisWeights (toFx (dev.f + dev.d)) (toFx dev.f) pm.h
  let nx := wx.size
  let ny := wy.size
  if maxStencilSide < nx ∨ maxStencilSide < ny then none else
  let alpha := fun (i j : Nat) => Clip.getB pm.data (4 * (j * pm.w + i) + 3)
  -- horizontally filtered rows: hrow j X = Σ wx · α
  let hrows : Array (Array Nat) := (Array.range pm.h).map fun j =>
    wx.map fun l => l.foldl (fun s (i, w) => s + w * alpha i j) 0
  let data := (List.range ny).foldl (fun (acc : ByteArray) Y =>
    let l := (wy[Y]?).getD []
    (List.range nx).foldl (fun (acc : ByteArray) X =>
      let s := l.foldl (fun s (j, w) => s + w * (((hrows[j]?).getD #[])[X]?).getD 0) 0
      acc.push (Image.u8 ((s + 2147483648) / 4294967296))) acc) (ByteArray.mk (Array.mkEmpty (nx * ny)))
  some { x0 := lx, y0 := ly, w := nx, h := ny, data }

/-- Draw one image of an image glyph through `dev` (image space → device): an axis-aligned
stencil by its exact coverage mask (`stencilMask`, composited through the clip mask `cm` with
colour `uc` and alpha `al`), anything else by `placeNoFit`. -/
def drawImage (cap W H : Nat) (cm : Option Mask) (al : Nat) (uc : Nat × Nat × Nat)
    (pm : Image.Pixmap) (dev : Aff) (b : ByteArray) : ByteArray × Nat :=
  match (if pm.stencil then stencilMask pm dev else none) with
  | some mk =>
    let r := (IRect.inter ⟨mk.x0, mk.y0, mk.x0 + mk.w, mk.y0 + mk.h⟩ (Clip.itemWindow W H cm))
    (Clip.composite b W mk cm r uc al, pm.w * pm.h + mk.w * mk.h)
  | none => placeNoFit cap W H pm dev cm uc al b

/-- `drawImage` preserves the buffer size. -/
theorem drawImage_size (cap W H : Nat) (cm : Option Mask) (al : Nat) (uc : Nat × Nat × Nat)
    (pm : Image.Pixmap) (dev : Aff) (b : ByteArray) :
    (drawImage cap W H cm al uc pm dev b).1.size = b.size := by
  unfold drawImage
  split
  · exact Clip.composite_size _ _ _ _ _ _ _
  · exact placeNoFit_size _ _ _ _ _ _ _ _ _

/-- Draw the images of an image glyph (`T3Glyph.images`) through `T` (glyph → device):
each by `drawImage` with its CTM × `T`, the clip mask `cm`, stencil colour `uc`, alpha `al`. -/
def drawImages (cap W H : Nat) (cm : Option Mask) (al : Nat) (uc : Nat × Nat × Nat) (T : Aff)
    (imgs : List (Image.Pixmap × Matrix)) (acc : ByteArray × Nat) : ByteArray × Nat :=
  imgs.foldl (fun acc (pm, ctm) =>
    let q := drawImage cap W H cm al uc pm (Aff.ofMatrix ctm * T) acc.1
    (q.1, acc.2 + q.2)) acc

/-- `drawImages` preserves the buffer size. -/
theorem drawImages_size (cap W H : Nat) (cm : Option Mask) (al : Nat) (uc : Nat × Nat × Nat)
    (T : Aff) (imgs : List (Image.Pixmap × Matrix)) :
    ∀ (acc : ByteArray × Nat), (drawImages cap W H cm al uc T imgs acc).1.size = acc.1.size := by
  induction imgs with
  | nil => intro acc; rfl
  | cons x rest ih =>
    intro acc
    simp only [drawImages, List.foldl_cons] at ih ⊢
    rw [ih]; exact drawImage_size _ _ _ _ _ _ _ _ _

/-- **Draw one glyph instance** with glyph → device matrix `T` into the page buffer `b`
(`W × H`): an image glyph by `drawImages` (cap `cap`); otherwise its layer (cell painter
`paint`) over its device box ∩ `win`, blitted through the clip mask `cm` (or full coverage)
with alpha byte `al`; a masked glyph takes the colour `uc`. Returns the buffer and the counted
work. -/
def drawGlyph (paint : Tiling.CellPainter) (cap W H : Nat) (win : IRect) (cm : Option Mask)
    (al : Nat) (uc : Nat × Nat × Nat) (T : Aff) (g : T3Glyph) (b : ByteArray) : ByteArray × Nat :=
  if T.det = 0 ∨ g.items.size = 0 then (b, 0) else
  if 0 < g.images.size then drawImages cap W H cm al uc T g.images.toList (b, 0) else
  match glyphRect T win g.bbox with
  | none => (b, 0)
  | some r =>
    if r.width = 0 ∨ r.height = 0 ∨ maxGlyphLayerPixels < r.width * r.height then (b, 0) else
    let pat : Tiling.Tiling := ⟨0, 1, (Fixed.zero, Fixed.zero, Fixed.zero, Fixed.zero), 1, 1,
      Matrix.identity, [], g.items⟩
    let (L, s) := Tiling.cellLayer paint T pat (if g.colored then none else some uc) r
    let mk := match cm with
      | some m => m
      | none => fullMask r
    let q := Tiling.blit W r mk al L 0 0 b
    (q.1, s + q.2)

/-- `drawGlyph` preserves the buffer size. -/
theorem drawGlyph_size (paint : Tiling.CellPainter) (cap W H : Nat) (win : IRect)
    (cm : Option Mask) (al : Nat) (uc : Nat × Nat × Nat) (T : Aff) (g : T3Glyph) (b : ByteArray) :
    (drawGlyph paint cap W H win cm al uc T g b).1.size = b.size := by
  unfold drawGlyph
  split
  · rfl
  · split
    · exact drawImages_size _ _ _ _ _ _ _ _ _
    · split
      · rfl
      · split
        · rfl
        · simp only [Tiling.blit_size]

/-- One axis of `subpixelAdjust`: `x + r` split into `⌊·⌋` and the fraction, the fraction's
`⌊· · 256⌋` masked by `q` (MuPDF's quantisation). -/
def quantAxis (x : Rat) (q : Nat) (r : Rat) : Rat :=
  let y := x + r
  let pix := y.floor
  let fr := ((y - pix) * 256).floor.toNat
  (pix : Rat) + ((Nat.land fr q : Nat) : Rat) / 256

/-- **Glyph position quantisation** (MuPDF `fz_subpixel_adjust`, applied to every glyph it
renders through its glyph cache, Type 3 included): the translation of the device text
rendering matrix `trm` is snapped to `1/4` px along the baseline (`1/8` below 24 px, none from
48 px) and, for an axis-aligned matrix, to whole pixels across it (from 8 px; `1/4` px from
4 px, `1/8` below). Sizes compare `|det trm|` with the squares of the thresholds. -/
def subpixelAdjust (trm : Aff) : Aff :=
  let det := absQ (trm.a * trm.d - trm.b * trm.c)
  let (q, r) : Nat × Rat :=
    if 48 * 48 ≤ det then (0, 1 / 2) else if 24 * 24 ≤ det then (128, 1 / 4) else (192, 1 / 8)
  let (qmin, rmin) : Nat × Rat :=
    if 8 * 8 ≤ det then (0, 1 / 2) else if 4 * 4 ≤ det then (128, 1 / 4) else (192, 1 / 8)
  let (hq, hr) := if trm.a = 0 ∧ trm.d = 0 then (qmin, rmin) else (q, r)
  let (vq, vr) := if trm.b = 0 ∧ trm.c = 0 then (qmin, rmin) else (q, r)
  { trm with e := quantAxis trm.e hq hr, f := quantAxis trm.f vq vr }

/-- One laid-out code of a run: its glyph (if any) drawn at its offset (the text rendering
matrix quantised as MuPDF's, `subpixelAdjust`). -/
def glyphStep (paint : Tiling.CellPainter) (W H : Nat) (win : IRect) (cm : Option Mask) (al : Nat)
    (uc : Nat × Nat × Nat) (f : T3Font) (r : GlyphRun) (rm : Aff)
    (acc : ByteArray × Nat) (e : List UInt8 × Fixed × Fixed) : ByteArray × Nat :=
  match e.1 with
  | [c] =>
    match f.glyphs[c.toNat]? with
    | some (some g) =>
      let q := drawGlyph paint f.imageCap W H win cm al uc (f.matrix * subpixelAdjust (placement r e.2.1 * rm)) g
        acc.1
      (q.1, acc.2 + q.2)
    | _ => acc
  | _ => acc

private theorem foldl_glyphStep_size (paint : Tiling.CellPainter) (W H : Nat) (win : IRect)
    (cm : Option Mask) (al : Nat) (uc : Nat × Nat × Nat) (f : T3Font) (r : GlyphRun) (rm : Aff)
    (l : List (List UInt8 × Fixed × Fixed)) :
    ∀ (acc : ByteArray × Nat),
      (l.foldl (glyphStep paint W H win cm al uc f r rm) acc).1.size = acc.1.size := by
  induction l with
  | nil => intro acc; rfl
  | cons e rest ih =>
    intro acc
    simp only [List.foldl_cons]
    rw [ih]
    unfold glyphStep
    split
    · split
      · exact drawGlyph_size _ _ _ _ _ _ _ _ _ _ _
      · rfl
    · rfl

/-- **Render a glyph run of a Type 3 font** (see the module doc) onto the page state `st`
(`W × H`, page → device `m`), glyphs drawn by the cell painter `paint`, positions from the
run's `FontInfo` `fi`. Modes 3 and 7 paint nothing. -/
def renderRun (cfg : Fill.Config) (paint : Tiling.CellPainter) (m : Aff) (W H : Nat)
    (fi : FontInfo) (f : T3Font) (st : Clip.RState) (r : GlyphRun) (clip : Content.Clip) :
    Clip.RState :=
  if !r.renderMode.paints then st else
  let c := Clip.clipMaskC cfg m W H st.cache clip
  let win := Clip.itemWindow W H c.1
  let entries := Text.layoutParts fi (Text.runTextState r) r.font.size Fixed.zero r.parts
  let rm := Aff.ofMatrix r.tm * Aff.ofMatrix r.ctm * m
  let q := entries.foldl (glyphStep paint W H win c.1 (Clip.compByte r.fill.alpha)
    (Clip.deviceRGB r.fill.color) f r rm) (st.buf, 0)
  { buf := q.1, cache := c.2.1, steps := st.steps + c.2.2 + q.2 }

/-- **Rendering a Type 3 run preserves the buffer size.** -/
theorem renderRun_size (cfg : Fill.Config) (paint : Tiling.CellPainter) (m : Aff) (W H : Nat)
    (fi : FontInfo) (f : T3Font) (st : Clip.RState) (r : GlyphRun) (clip : Content.Clip) :
    (renderRun cfg paint m W H fi f st r clip).buf.size = st.buf.size := by
  unfold renderRun
  split
  · rfl
  · exact foldl_glyphStep_size _ _ _ _ _ _ _ _ _ _ _ _

/-! ## 5. Checks -/

#guard GBox.union (.box 0 0 1 1) (.box (-1) 2 0 3) == .box (-1) 0 1 3
#guard GBox.union .empty .all == .all
#guard boxOf (some [3, -1, 48, 63]) == .box 3 (-1) 48 63
#guard boxOf (some [0, 0, 0, 5]) == .empty
#guard glyphBox #[.image (.inline [] ByteArray.empty) ⟨Fixed.ofInt 2, Fixed.zero, Fixed.zero,
    Fixed.ofInt 3, Fixed.ofInt 1, Fixed.ofInt 1⟩ { color := .gray Comp.zero, alpha := Comp.one } []]
    .empty .empty == .box 1 1 3 4
#guard glyphBox #[.shading (Name.ofString "S") .page Matrix.identity
    { color := .gray Comp.zero, alpha := Comp.one } []] (.box 0 0 5 5) .empty == .box 0 0 5 5
#guard (fullMask ⟨0, 0, 3, 2⟩).data.size == 6

end SafePdf.Core.Raster.Type3
