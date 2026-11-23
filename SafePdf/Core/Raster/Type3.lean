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

Each laid-out code of a glyph run (`Text.layoutParts` with the font's `FontInfo`, the
advances truncated to multiples of `1/1000` em as MuPDF's integer metrics table, `truncWidth`)
is drawn with the matrix
`T = FontMatrix × [Tfs·Th 0 0 Tfs tx Trise] × Tm × CTM × view` (exact over `ℚ`). The glyph
is rendered with the caller's **cell painter** (the full item painter at one depth less,
`Glyph.cellPainterD`; nested Type 3 glyphs and tiling cells share the depth cap, depth 0 =
paths only) as a premultiplied layer over the device box of `GBox` widened by one pixel (as
`fz_render_t3_glyph_pixmap`) ∩ the run's clip window (`Tiling.cellLayer`: rendered over
white and over black, coverage `α` recovered exactly). A **masked** glyph keeps only `α` and
takes the run's fill colour (`Tiling.layerLoop` with the colour: the charproc's colour
operators are ignored, image masks are painted as stencils of that colour). The layer is
blitted (`Tiling.blit`) through the run's clip mask with the fill alpha. Render modes (task
7.3l, `passes`, as MuPDF): 3 and 7 paint nothing; fill modes paint the glyph with the fill
colour and alpha; stroke modes paint the glyph **filled** with the stroke colour and alpha
(MuPDF's `fz_render_stroked_glyph` falls back to the filled glyph for non-FreeType fonts);
modes 2 and 6 paint both, fill first. Gaps: the clip effect of modes 4–7; the knockout group
MuPDF opens for mode 2/6 when the stroke alpha is neither 0 nor 1 (here the stroke pass is
composited over the fill pass); pattern colours on masked glyphs paint with the pattern's
device placeholder colour.

**Image glyphs** (bitmap fonts: every item an inline image, `T3Glyph.images`) skip the layer:
a stencil is scaled as MuPDF does (task 7.3k, `mupdfStencil`: power-of-two subsampling, then
`fz_scale_pixmap`'s smoothstep weights) and composited directly; the masks are cached per run
for the page by (font, code, scale, sub-pixel phase) (`GlyphCache`, task 7.3l, held in
`Glyph.TState`), the subsampled bitmaps per loaded font (`StencilSrc`, lazily).

Layers larger than `maxGlyphLayerPixels` are not drawn (degradation, never an error).
`renderRun_size`: the page buffer keeps its size.

## Gaps

* The glyph bitmap cache holds image glyphs only (page-wide; tiling cells start their own);
  other glyphs are rendered per instance (two small renders); charproc display lists are
  cached per font.
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

/-- MuPDF's `fz_mul255(a, b)`: `x = a·b + 128; (x + (x >> 8)) >> 8` (arithmetic shifts). -/
def mul255 (a b : Int) : Int :=
  let x := a * b + 128
  Int.fdiv (x + Int.fdiv x 256) 256

/-- The largest power-of-two subsampling `l ≤ 6` with `W >> l ≥ w + 2` and `H >> l ≥ h + 2`
(`fz_get_pixmap_from_image`; `0` when `w` or `h` is `0`). -/
def l2factor (W H w h : Nat) : Nat :=
  if w = 0 ∨ h = 0 then 0 else
  (List.range 6).foldl (fun l _ =>
    if w + 2 ≤ W >>> (l + 1) ∧ h + 2 ≤ H >>> (l + 1) then l + 1 else l) 0

/-- **Subsampled stencil coverage** (`fz_decomp_image_from_stream` with `l2extra = l`): the
`⌈W/2ˡ⌉ × ⌈H/2ˡ⌉` coverage bytes of stencil `pm` with `/Decode` kind `inv` (`[1 0]`). The raw
sample is `a` (`[1 0]`) or `255 − a` (default) for the decoded coverage `a`. -/
def subsampleStencil (pm : Image.Pixmap) (inv : Bool) (l : Nat) : Nat × Nat × ByteArray :=
  let f := 1 <<< l
  let sw := (pm.w + f - 1) / f
  let sh := (pm.h + f - 1) / f
  let raw := fun (i j : Nat) =>
    let a := Clip.getB pm.data (4 * (j * pm.w + i) + 3)
    if inv then a else 255 - a
  let data := (List.range sh).foldl (fun (acc : ByteArray) by_ =>
    let ys := min f (pm.h - by_ * f)
    (List.range sw).foldl (fun (acc : ByteArray) bx =>
      let xs := min f (pm.w - bx * f)
      let s := (List.range ys).foldl (fun s yy =>
        (List.range xs).foldl (fun s xx => s + raw (bx * f + xx) (by_ * f + yy)) s) 0
      let v1 : Int := 255 - ((s / max 1 (xs * ys) : Nat) : Int)
      let v2 : Int := if inv then max 0 (min 255 (255 + mul255 v1 (-255))) else v1
      acc.push v2.toNat.toUInt8) acc) (ByteArray.mk (Array.mkEmpty (sw * sh)))
  (sw, sh, data)


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

/-- A stencil whose sample pipeline MuPDF's scaler reproduces (`mupdfStencil`): its `/Decode`
kind (`stencilDecode`) and its subsampled coverage for each factor `l = 0 … 6`, computed lazily
once per loaded font (a `Thunk`, so every run of the page shares it). -/
structure StencilSrc where
  /-- `/Decode [1 0]`. -/
  inv : Bool
  /-- `subsampleStencil pm inv l` for `l = 0 … 6`. -/
  subs : Array (Thunk (Nat × Nat × ByteArray))

/-- The stencil source of `pm` with `/Decode` kind `inv`. -/
def StencilSrc.ofPixmap (pm : Image.Pixmap) (inv : Bool) : StencilSrc :=
  ⟨inv, (Array.range 7).map fun l => Thunk.mk fun _ => subsampleStencil pm inv l⟩

/-- The subsampled coverage for factor `l` (computed directly past the table). -/
def StencilSrc.sub (s : StencilSrc) (pm : Image.Pixmap) (l : Nat) : Nat × Nat × ByteArray :=
  match s.subs[l]? with
  | some t => t.get
  | none => subsampleStencil pm s.inv l

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
  drawn directly (`drawImages`); empty otherwise. The third component: the stencil's source for
  MuPDF's scaler (`StencilSrc`), when its `/Decode` is standard. -/
  images : Array (Image.Pixmap × Matrix × Option StencilSrc) := #[]

/-- A loaded Type 3 font. -/
structure T3Font where
  /-- `/FontMatrix` (glyph space → text space), exact. -/
  matrix : Aff
  /-- The glyph of each code `0 … 255` (`none`: no charproc). -/
  glyphs : Array (Option T3Glyph)
  /-- Downscale cap for images (`Limits.maxImagePixels`). -/
  imageCap : Nat := 0
  /-- The font's number among the page's loaded Type 3 fonts (`Glyph.loadType3`): its identity
  in the page-wide glyph cache. -/
  uid : Nat := 0

/-- An exact number (`int` or `real`). -/
def ratOf : PdfObject → Option Rat
  | .int i => some (i : Rat)
  | .real d => some (decimalToRat d)
  | _ => none

/-- A list of exact numbers (array elements resolved by `resolve`). -/
def ratsOf (resolve : PdfObject → PdfObject) : Option PdfObject → Option (List Rat)
  | some (.array xs) => xs.mapM fun x => ratOf (resolve x)
  | _ => none

/-- The `/Decode` kind of an inline stencil mask: `some false` for the default `[0 1]`,
`some true` for `[1 0]`, `none` for anything else (MuPDF's sample pipeline is then not
reproduced, see `mupdfStencil`). -/
def stencilDecode (params : Dict) : Option Bool :=
  match Dict.get? params (Content.Run.nm "Decode") with
  | none => some false
  | some o =>
    match ratsOf id (some o) with
    | some [a, b] => if a = 0 ∧ b = 1 then some false else if a = 1 ∧ b = 0 then some true else none
    | _ => none

/-- The decoded images of an image glyph (`T3Glyph.images`): every item an inline image
without clip, decodable, a stencil mask unless the glyph is coloured; else `#[]`. -/
def imageGlyph (limits : Limits) (colored : Bool) (items : DisplayList) :
    Array (Image.Pixmap × Matrix × Option StencilSrc) :=
  let r := items.foldl (fun (acc : Option (Array (Image.Pixmap × Matrix × Option StencilSrc))) it =>
    match acc, it with
    | some a, .image (.inline params data) ctm _ [] =>
      match Image.decodeInline limits [] params data with
      | .ok pm =>
        if pm.stencil || colored then
          some (a.push (pm, ctm, (stencilDecode params).map (StencilSrc.ofPixmap pm)))
        else none
      | .error _ => none
    | _, _ => none) (some #[])
  match r with
  | some a => a
  | none => #[]

/-! ## 3. Loading -/

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
  | .clip .. | .groupBegin _ | .groupEnd | .unsupported _
  | .actualTextBegin _ | .actualTextEnd => .empty
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

/-! ### Downscaled stencils: MuPDF's image scaler (task 7.3k)

MuPDF 1.25.1 draws an image mask inside a Type 3 glyph (`fz_draw_fill_image_mask`, draw device
flag `FZ_DRAWDEV_FLAGS_TYPE3`: no grid fitting) as follows, for the image → device matrix `m`
(fitz image space: row 0 at the top):

1. `fz_get_pixmap_from_image`: the requested size `w = ⌊√(a² + b²)⌋`, `h = ⌊√(c² + d²)⌋`
   (clamped to the image size); the **power-of-two subsampling** factor `l` is the largest
   `l ≤ 6` with `W >> l ≥ w + 2` and `H >> l ≥ h + 2`. The 1-bit samples are unpacked to
   `0`/`255`, averaged over `2ˡ × 2ˡ` blocks (`fz_subsample_pixblock`: truncating mean, the
   stray right column and bottom row of blocks averaged over their real size), inverted (image
   mask: `0` = paint) and passed through `/Decode` (`fz_decode_tile`: `v ↦ 255 + mul255(v, −255)`
   for `[1 0]`). `subsampleStencil` reproduces this from the decoded pixmap's alpha bytes.
2. When the true size `dx = ⌊|a|⌋`, `dy = ⌊|d|⌋` is below the subsampled size on both axes
   (`fz_default_image_scale`) and the matrix is axis-aligned (`b = c = 0`), the pixmap is scaled
   by `fz_scale_pixmap_cached(pix, m.e, m.f, m.a, m.d)` (`draw-scale-simple.c`): per axis,
   integer weights from `make_weights` with the smoothstep filter `fz_scale_filter_simple`
   (`1 + (2x − 3)x²` on `[0, 1)`), each `(int)(256 · f · F + 0.5)`, normalised by
   `check_weights`; rows are filtered first into bytes `(128 + Σ w·s) >> 8`, then columns the
   same way. The scaled pixmap lands on whole pixels and is painted 1 : 1.

`weightsAt` is the exact reference over `ℚ` (MuPDF's formulas); the renderer uses
`weightsAtI` (positions on a `2⁻²⁰` grid, filter in `2⁻²⁴` fixed point, natural numbers only).
MuPDF evaluates them in `float`, so a weight whose `256 · f + 0.5` falls within rounding of an
integer can differ by one (a documented deviation, as is the single-column case, where MuPDF
reads its re-ordered vertical weights sequentially). On the pdfTeX bitmap-font page of
`gen_tex_pages.py` the coverage of every glyph equals `mutool draw`'s (task 7.3k). Other cases (rotated or skewed images, upscaling, unusual
`/Decode` arrays) keep the exact area filter (`stencilMask`) or `placeNoFit`. -/

/-- MuPDF's smoothstep scale filter `fz_scale_filter_simple`: `1 + (2x − 3)x²` below 1, else 0
(`x ≥ 0`). -/
def simpleFilter (x : Rat) : Rat := if 1 ≤ x then 0 else 1 + (2 * x - 3) * x * x

/-- MuPDF's `check_weights`: the weights `ws` (source index, weight; increasing index) of
destination pixel `j` of `w`, sub-pixel offset `x`, real width `wf`: the first largest weight
absorbs `256 − Σ` for inner pixels, when `Σ > 256`, or for a fully covered edge pixel. -/
def checkWeightsB (ws : List (Nat × Int)) (j w : Nat) (xSmall wSmall : Bool) :
    List (Nat × Int) :=
  let sum := ws.foldl (fun s p => s + p.2) 0
  -- index (in `ws`) of the first maximum
  let mx := (ws.foldl (fun (acc : Nat × Int × Nat) p =>
    let (k, best, at_) := acc
    if best < p.2 then (k + 1, p.2, k) else (k + 1, best, at_)) (0, -256, 0)).2.2
  let adj := ((j ≠ 0 ∧ j + 1 ≠ w) ∨ 256 < sum) ∨ (j = 0 ∧ xSmall ∧ sum ≠ 256) ∨
    (j + 1 = w ∧ wSmall ∧ sum ≠ 256)
  if adj then ws.modify mx (fun p => (p.1, p.2 + (256 - sum))) else ws

/-- `checkWeightsB` with the edge tests `x < 0.0001` and `w − wf < 0.0001` (MuPDF's
`check_weights`). -/
def checkWeights (ws : List (Nat × Int)) (j w : Nat) (x wf : Rat) : List (Nat × Int) :=
  checkWeightsB ws j w (decide (x < 1 / 10000)) (decide ((w : Rat) - wf < 1 / 10000))

/-- MuPDF's `make_weights` for destination pixel `j` (one axis): `srcW` source samples scaled
to the real width `dstW` (`dstWInt` whole pixels) at sub-pixel offset `x`. -/
def weightsAt (srcW : Nat) (x dstW : Rat) (dstWInt j : Nat) : List (Nat × Int) :=
  let sw : Rat := srcW
  let FG : Rat × Rat := if dstW < sw then (dstW / sw, 1) else (1, sw / dstW)
  let F := FG.1
  let G := FG.2
  let window := 1 / F
  let centre := ((j : Rat) - x + 1 / 2) * sw / dstW - 1 / 2
  let l := (centre - window).ceil
  let r := (centre + window).floor
  let ws := (List.range (r - l + 1).toNat).filterMap fun (k : Nat) =>
    let i : Int := l + (k : Int)
    if i < 0 ∨ (srcW : Int) ≤ i then none else
    let dist := absQ (((j : Rat) - x + 1 / 2 - ((i : Rat) + 1 / 2) * dstW / sw) * G)
    let wt := (simpleFilter dist * F * 256 + 1 / 2).floor
    if wt = 0 then none else some (i.toNat, wt)
  let ws := if ws.isEmpty then
      [((max 0 (min (centre.floor) ((srcW : Int) - 1))).toNat, 1)] else ws
  checkWeights ws j dstWInt x dstW

/-- Bits of the dyadic grid of `weightsAtI` (`2⁻²⁰` px, finer than MuPDF's `float` positions:
`float` page coordinates between 128 and 256 px have a resolution of `2⁻¹⁶`). -/
def wBits : Nat := 20

/-- `q` on the grid `2⁻ʷᴮⁱᵗˢ`, rounded. -/
def toDy (q : Rat) : Int := (q * ((1 <<< wBits : Nat) : Rat) + 1 / 2).floor

/-- **`weightsAt` in fixed point** (the hot path): inputs on the grid `2⁻ʷᴮⁱᵗˢ`
(`x = X / 2ᵏ ∈ [0, 1)`, `dstW = N / 2ᵏ > 0`), the filter evaluated in `2⁻²⁴` fixed point with
natural numbers (below `2⁶³`, i.e. machine words in compiled code, for device extents up to
`2¹¹` px) — about the precision of MuPDF's own `float` evaluation. With `P = |((2j+1)·2ᵏ − 2X)·srcW − (2i+1)·N|` the filter distance is `P / Q`
(`Q = 2·srcW·2ᵏ` scaling down, `2N` up). A weight can differ from the exact `weightsAt` by one
only when `256·f·F + ½` lies within about `2⁻¹⁴` of an integer (`Tests/RasterGlyph.lean`
measures the agreement). Callers keep `srcW, dstWInt ≤ maxStencilSide`. -/
def weightsAtI (srcW : Nat) (X N : Nat) (dstWInt j : Nat) : List (Nat × Int) :=
  let K : Nat := 1 <<< wBits
  let sw : Nat := srcW
  let down := N < sw * K
  -- `A = ((2j+1)·2ᵏ − 2X)·srcW` can be negative (`x > ½` at `j = 0`): kept shifted by
  -- `c = 2·2ᵏ·srcW` as a natural number (`Ac = A + c`, compared with `(2i+1)·N + c`)
  let c : Nat := 2 * K * sw
  let Ac : Nat := ((2 * j + 3) * K - 2 * X) * sw
  let A : Int := (Ac : Int) - c
  -- centre = (A − N) / 2N; window = sw·K / N (down) or 1
  let win2 : Int := if down then 2 * (sw : Int) * K else 2 * (N : Int)
  let l : Int := -Int.fdiv (-(A - N - win2)) (2 * (N : Int))
  let r : Int := Int.fdiv (A - N + win2) (2 * (N : Int))
  let Q : Nat := if down then 2 * sw * K else 2 * N
  let one : Nat := 1 <<< 24
  let den : Nat := if down then K * sw * one else one
  let mulN : Nat := if down then 256 * N else 256
  let ws := (List.range (r - l + 1).toNat).filterMap fun (k : Nat) =>
    let i : Int := l + (k : Int)
    if i < 0 ∨ (sw : Int) ≤ i then none else
    let B := (2 * i.toNat + 1) * N + c
    let P := if B ≤ Ac then Ac - B else B - Ac
    if Q ≤ P then none else
    let d := (P <<< 24) / Q
    let s := one - (((((3 * one - 2 * d) * d) >>> 24) * d) >>> 24)
    let wt := (mulN * s + den / 2) / den
    if wt = 0 then none else some (i.toNat, (wt : Int))
  let ws := if ws.isEmpty then
      [((max 0 (min (Int.fdiv (A - N) (2 * (N : Int))) ((sw : Int) - 1))).toNat, 1)]
    else ws
  checkWeightsB ws j dstWInt (X * 10000 < K) (((dstWInt : Int) * K - N) * 10000 < K)

/-- `(v >> 8)` stored as an `unsigned char` (wraps modulo 256, as MuPDF's cast). -/
def u8wrap (v : Int) : UInt8 := (Int.emod (Int.fdiv v 256) 256).toNat.toUInt8

/-- One axis of `fz_scale_pixmap_cached`: the clamped extent `w` (`(−1, 0) ↦ −1`,
`(0, 1) ↦ 1`) placed at `x`: `(flip, first whole pixel, whole pixels, sub-pixel offset, |w|)`. -/
def axisSetup (x w0 : Rat) : Bool × Int × Nat × Rat × Rat :=
  let w := if w0 ≤ -1 then w0 else if w0 < 0 then -1 else if w0 < 1 then 1 else w0
  if w < 0 then
    let w := -w
    let d := (x - w).floor
    let t := x.ceil
    (true, d, (t - d).toNat, t - x, w)
  else
    let d := x.floor
    let xf := x - d
    (false, d, (xf + w).ceil.toNat, xf, w)

/-- Weighted byte sum `(128 + Σ w · s(i)) >> 8` (wrapped). -/
def wsum (ws : List (Nat × Int)) (s : Nat → Nat) : UInt8 :=
  u8wrap (ws.foldl (fun acc p => acc + p.2 * (s p.1 : Int)) 128)

/-- **MuPDF's scaled stencil mask** (see the section doc): `none` unless `pm` is a stencil
with the source `src0` (`StencilSrc`), `dev` (PDF image space → device) is axis-aligned and downscales on
both axes, and the result is at most `maxStencilSide` pixels along each axis. -/
def mupdfStencil (pm : Image.Pixmap) (src0 : StencilSrc) (dev : Aff) : Option Mask :=
  if dev.b ≠ 0 ∨ dev.c ≠ 0 ∨ dev.a = 0 ∨ dev.d = 0 then none else
  -- fitz image space (row 0 at the top): `[1 0 0 −1 0 1] × dev`
  let ma := dev.a
  let md := -dev.d
  let me := dev.e + dev.c
  let mf := dev.f + dev.d
  if (1 <<< 24 : Nat) < absQ ma ∨ (1 <<< 24 : Nat) < absQ md ∨ (1 <<< 24 : Nat) < absQ me ∨
    (1 <<< 24 : Nat) < absQ mf then none else
  let dx := (absQ ma).floor.toNat
  let dy := (absQ md).floor.toNat
  let l := l2factor pm.w pm.h (min dx pm.w) (min dy pm.h)
  let sub := src0.sub pm l
  let sw := sub.1
  let sh := sub.2.1
  let src := sub.2.2
  if ¬ (dx < sw ∧ dy < sh) then none else
  let ax := axisSetup me ma
  let ay := axisSetup mf md
  let dwi := ax.2.2.1
  let dhi := ay.2.2.1
  if maxStencilSide < dwi ∨ maxStencilSide < dhi ∨ maxStencilSide < sw ∨ maxStencilSide < sh then
    none else
  let xX := (min (toDy ax.2.2.2.1) ((1 <<< wBits : Nat) - 1)).toNat
  let xN := (max 1 (toDy ax.2.2.2.2)).toNat
  let yX := (min (toDy ay.2.2.2.1) ((1 <<< wBits : Nat) - 1)).toNat
  let yN := (max 1 (toDy ay.2.2.2.2)).toNat
  let cols : Array (List (Nat × Int)) :=
    (Array.range dwi).map fun j => weightsAtI sw xX xN dwi j
  let rows : Array (List (Nat × Int)) :=
    (Array.range dhi).map fun j => weightsAtI sh yX yN dhi j
  let px := fun (i j : Nat) => Clip.getB src (j * sw + i)
  -- horizontally scaled logical rows (`flip_y`: fed bottom-up); one source column: copied
  let temp : ByteArray := (List.range sh).foldl (fun (acc : ByteArray) r =>
    let sr := if ay.1 then sh - 1 - r else r
    (List.range dwi).foldl (fun (acc : ByteArray) c =>
      let j := if ax.1 then dwi - 1 - c else c
      acc.push (if sw = 1 then (px 0 sr).toUInt8 else wsum ((cols[j]?).getD []) (px · sr)))
      acc) (ByteArray.mk (Array.mkEmpty (sh * dwi)))
  let data := (List.range dhi).foldl (fun (acc : ByteArray) k =>
    (List.range dwi).foldl (fun (acc : ByteArray) c =>
      acc.push (if sh = 1 then (Clip.getB temp c).toUInt8
        else wsum ((rows[k]?).getD []) (fun i => Clip.getB temp (i * dwi + c)))) acc)
    (ByteArray.mk (Array.mkEmpty (dhi * dwi)))
  some { x0 := ax.2.1, y0 := ay.2.1, w := dwi, h := dhi, data }

/-- The coverage mask of a stencil image of a glyph, when one is computed directly: MuPDF's
scaler (`mupdfStencil`) when it applies, else the exact area filter (`stencilMask`) for an
axis-aligned matrix; `none` for non-stencils and other matrices. -/
def stencilCoverage (pm : Image.Pixmap) (dec : Option StencilSrc) (dev : Aff) : Option Mask :=
  if !pm.stencil then none else
  match dec.bind (fun s => mupdfStencil pm s dev) with
  | some mk => some mk
  | none => stencilMask pm dev

/-- Draw one image of an image glyph through `dev` (image space → device) given its coverage
mask `mk?` (`stencilCoverage`, possibly from the glyph cache): the mask composited through the
clip mask `cm` with colour `uc` and alpha `al`; without one, the image by `placeNoFit`. -/
def drawImageWith (cap W H : Nat) (cm : Option Mask) (al : Nat) (uc : Nat × Nat × Nat)
    (pm : Image.Pixmap) (dev : Aff) (mk? : Option Mask) (b : ByteArray) : ByteArray × Nat :=
  match mk? with
  | some mk =>
    let r := (IRect.inter ⟨mk.x0, mk.y0, mk.x0 + mk.w, mk.y0 + mk.h⟩ (Clip.itemWindow W H cm))
    (Clip.composite b W mk cm r uc al, mk.w * mk.h)
  | none => placeNoFit cap W H pm dev cm uc al b

/-- `drawImageWith` preserves the buffer size. -/
theorem drawImageWith_size (cap W H : Nat) (cm : Option Mask) (al : Nat) (uc : Nat × Nat × Nat)
    (pm : Image.Pixmap) (dev : Aff) (mk? : Option Mask) (b : ByteArray) :
    (drawImageWith cap W H cm al uc pm dev mk? b).1.size = b.size := by
  unfold drawImageWith
  split
  · exact Clip.composite_size _ _ _ _ _ _ _
  · exact placeNoFit_size _ _ _ _ _ _ _ _ _

/-- Draw one image of an image glyph through `dev` (image space → device): a stencil by its
coverage mask (`stencilCoverage`: MuPDF's scaler, else the exact area filter), anything else
by `placeNoFit` (`drawImageWith`). `dec`: the stencil's `/Decode` kind. -/
def drawImage (cap W H : Nat) (cm : Option Mask) (al : Nat) (uc : Nat × Nat × Nat)
    (pm : Image.Pixmap) (dec : Option StencilSrc) (dev : Aff) (b : ByteArray) : ByteArray × Nat :=
  let q := drawImageWith cap W H cm al uc pm dev (stencilCoverage pm dec dev) b
  (q.1, q.2 + pm.w * pm.h)

/-- `drawImage` preserves the buffer size. -/
theorem drawImage_size (cap W H : Nat) (cm : Option Mask) (al : Nat) (uc : Nat × Nat × Nat)
    (pm : Image.Pixmap) (dec : Option StencilSrc) (dev : Aff) (b : ByteArray) :
    (drawImage cap W H cm al uc pm dec dev b).1.size = b.size :=
  drawImageWith_size _ _ _ _ _ _ _ _ _ _

/-- Draw the images of an image glyph (`T3Glyph.images`) through `T` (glyph → device):
each by `drawImage` with its CTM × `T`, the clip mask `cm`, stencil colour `uc`, alpha `al`. -/
def drawImages (cap W H : Nat) (cm : Option Mask) (al : Nat) (uc : Nat × Nat × Nat) (T : Aff)
    (imgs : List (Image.Pixmap × Matrix × Option StencilSrc)) (acc : ByteArray × Nat) :
    ByteArray × Nat :=
  imgs.foldl (fun acc (pm, ctm, dec) =>
    let q := drawImage cap W H cm al uc pm dec (Aff.ofMatrix ctm * T) acc.1
    (q.1, acc.2 + q.2)) acc

/-- `drawImages` preserves the buffer size. -/
theorem drawImages_size (cap W H : Nat) (cm : Option Mask) (al : Nat) (uc : Nat × Nat × Nat)
    (T : Aff) (imgs : List (Image.Pixmap × Matrix × Option StencilSrc)) :
    ∀ (acc : ByteArray × Nat), (drawImages cap W H cm al uc T imgs acc).1.size = acc.1.size := by
  induction imgs with
  | nil => intro acc; rfl
  | cons x rest ih =>
    intro acc
    simp only [drawImages, List.foldl_cons] at ih ⊢
    rw [ih]; exact drawImage_size _ _ _ _ _ _ _ _ _ _

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

/-! ### Glyph bitmap cache

MuPDF caches rendered glyphs per (font, glyph, matrix, sub-pixel phase) (`fz_render_glyph`).
Here the coverage masks of an image glyph's stencils (`stencilCoverage`) are cached **for the
whole page** (task 7.3l; the cache lives in `Glyph.TState`): the key is the loaded font
(`T3Font.uid`), the code, the linear part `a b c d` of the glyph → device matrix and the
fractional part of its (quantised) translation; an integer translation moves the masks by whole
pixels (exactly: MuPDF's scaler places its output at `⌊x⌋` and depends on `x − ⌊x⌋` only).
Bounded: at most `maxGlyphCache` entries and `maxGlyphCacheBytes` mask bytes (further entries
are not stored). -/

/-- Most cached glyph instances per page (local cap). -/
def maxGlyphCache : Nat := 4096

/-- Most mask bytes held by the glyph cache per page (local cap, 16 MiB). -/
def maxGlyphCacheBytes : Nat := 1 <<< 24

/-- The key of a cached glyph instance (besides its code): the font's `T3Font.uid`, the linear
part of the glyph → device matrix and the sub-pixel phase of its translation. -/
structure CacheKey where
  /-- `T3Font.uid` of the font. -/
  font : Nat
  /-- Linear part of the glyph → device matrix. -/
  a : Rat
  /-- Linear part of the glyph → device matrix. -/
  b : Rat
  /-- Linear part of the glyph → device matrix. -/
  c : Rat
  /-- Linear part of the glyph → device matrix. -/
  d : Rat
  /-- Sub-pixel phase `e − ⌊e⌋`. -/
  fe : Rat
  /-- Sub-pixel phase `f − ⌊f⌋`. -/
  ff : Rat
  deriving BEq

/-- Cached stencil masks of image glyphs: per code, `(key, masks)` (one optional mask per image
of the glyph, placed for the phase, i.e. translation `−⌊e⌋, −⌊f⌋`). -/
structure GlyphCache where
  /-- Entries by code (`0 … 255`). -/
  slots : Array (List (CacheKey × Array (Option Mask)))
  /-- Number of entries. -/
  count : Nat
  /-- Mask bytes held. -/
  bytes : Nat

/-- The empty cache. -/
def GlyphCache.empty : GlyphCache := ⟨Array.replicate 256 [], 0, 0⟩

instance : Inhabited GlyphCache := ⟨GlyphCache.empty⟩

/-- The masks cached for code `c` under key `k`. -/
def GlyphCache.find? (gc : GlyphCache) (c : Nat) (k : CacheKey) : Option (Array (Option Mask)) :=
  (((gc.slots[c]?).getD []).find? (fun e => e.1 == k)).map (·.2)

/-- Bytes of a list of optional masks. -/
def masksBytes (m : Array (Option Mask)) : Nat :=
  m.foldl (fun s o => s + match o with | some mk => mk.data.size | none => 0) 0

/-- Add an entry (dropped when the cache is full: `maxGlyphCache` entries or
`maxGlyphCacheBytes` bytes). -/
def GlyphCache.insert (gc : GlyphCache) (c : Nat) (k : CacheKey) (m : Array (Option Mask)) :
    GlyphCache :=
  let nb := masksBytes m
  if maxGlyphCache ≤ gc.count ∨ maxGlyphCacheBytes < gc.bytes + nb then gc else
  ⟨gc.slots.modify c (fun l => (k, m) :: l), gc.count + 1, gc.bytes + nb⟩

/-- The cache never holds more than `maxGlyphCache` entries. -/
theorem GlyphCache.insert_count_le (gc : GlyphCache) (c : Nat) (k : CacheKey)
    (m : Array (Option Mask)) (h : gc.count ≤ maxGlyphCache) :
    (gc.insert c k m).count ≤ maxGlyphCache := by
  unfold GlyphCache.insert
  dsimp only
  split
  · exact h
  · next hn => dsimp only; omega

/-- The cache never holds more than `maxGlyphCacheBytes` mask bytes. -/
theorem GlyphCache.insert_bytes_le (gc : GlyphCache) (c : Nat) (k : CacheKey)
    (m : Array (Option Mask)) (h : gc.bytes ≤ maxGlyphCacheBytes) :
    (gc.insert c k m).bytes ≤ maxGlyphCacheBytes := by
  unfold GlyphCache.insert
  dsimp only
  split
  · exact h
  · next hn => dsimp only; omega

/-- A mask moved by whole pixels. -/
def shiftMask (mk : Mask) (dx dy : Int) : Mask := { mk with x0 := mk.x0 + dx, y0 := mk.y0 + dy }

/-- Draw the images of an image glyph through `T` with their coverage masks `mks` (computed for
`T` minus the integer translation `(ix, iy)`, so moved by it); an image without a mask is drawn
by `placeNoFit` through its CTM × `T`. -/
def drawImagesC (cap W H : Nat) (cm : Option Mask) (al : Nat) (uc : Nat × Nat × Nat) (T : Aff)
    (ix iy : Int) (imgs : List ((Image.Pixmap × Matrix × Option StencilSrc) × Option Mask))
    (acc : ByteArray × Nat) : ByteArray × Nat :=
  imgs.foldl (fun acc e =>
    let q := drawImageWith cap W H cm al uc e.1.1 (Aff.ofMatrix e.1.2.1 * T)
      (e.2.map (shiftMask · ix iy)) acc.1
    (q.1, acc.2 + q.2)) acc

/-- `drawImagesC` preserves the buffer size. -/
theorem drawImagesC_size (cap W H : Nat) (cm : Option Mask) (al : Nat) (uc : Nat × Nat × Nat)
    (T : Aff) (ix iy : Int) (imgs : List ((Image.Pixmap × Matrix × Option StencilSrc) × Option Mask)) :
    ∀ (acc : ByteArray × Nat),
      (drawImagesC cap W H cm al uc T ix iy imgs acc).1.size = acc.1.size := by
  induction imgs with
  | nil => intro acc; rfl
  | cons x rest ih =>
    intro acc
    simp only [drawImagesC, List.foldl_cons] at ih ⊢
    rw [ih]; exact drawImageWith_size _ _ _ _ _ _ _ _ _ _

/-- The coverage masks of an image glyph for glyph → device matrix `T0`, with the work done. -/
def glyphMasks (g : T3Glyph) (T0 : Aff) : Array (Option Mask) × Nat :=
  (g.images.map fun e => stencilCoverage e.1 e.2.2 (Aff.ofMatrix e.2.1 * T0),
    g.images.foldl (fun s e => s + e.1.w * e.1.h) 0)

/-- **Draw an image glyph** with glyph → device matrix `T` through the cache `gc` (font
`uid`, code `c`): masks looked up by (font, code, linear part, phase) or computed and stored. -/
def drawCached (cap W H : Nat) (cm : Option Mask) (al : Nat) (uc : Nat × Nat × Nat) (T : Aff)
    (uid c : Nat) (g : T3Glyph) (gc : GlyphCache) (b : ByteArray) : ByteArray × Nat × GlyphCache :=
  let ix := T.e.floor
  let iy := T.f.floor
  let fe := T.e - ix
  let ff := T.f - iy
  let k : CacheKey := { font := uid, a := T.a, b := T.b, c := T.c, d := T.d, fe, ff }
  let r : Array (Option Mask) × Nat × GlyphCache := match gc.find? c k with
    | some m => (m, 0, gc)
    | none =>
      let q := glyphMasks g { T with e := fe, f := ff }
      (q.1, q.2, gc.insert c k q.1)
  let q := drawImagesC cap W H cm al uc T ix iy (g.images.toList.zip r.1.toList) (b, r.2.1)
  (q.1, q.2, r.2.2)

/-- `drawCached` preserves the buffer size. -/
theorem drawCached_size (cap W H : Nat) (cm : Option Mask) (al : Nat) (uc : Nat × Nat × Nat)
    (T : Aff) (uid c : Nat) (g : T3Glyph) (gc : GlyphCache) (b : ByteArray) :
    (drawCached cap W H cm al uc T uid c g gc b).1.size = b.size :=
  drawImagesC_size _ _ _ _ _ _ _ _ _ _ _

/-- One laid-out code of a run: its glyph (if any) drawn at its offset (the text rendering
matrix quantised as MuPDF's, `subpixelAdjust`); image glyphs through the run's glyph cache
(`drawCached`, the page's cache), others by `drawGlyph`. The accumulator: buffer, work, cache. -/
def glyphStep (paint : Tiling.CellPainter) (W H : Nat) (win : IRect) (cm : Option Mask) (al : Nat)
    (uc : Nat × Nat × Nat) (f : T3Font) (r : GlyphRun) (rm : Aff)
    (acc : ByteArray × Nat × GlyphCache) (e : List UInt8 × Fixed × Fixed) :
    ByteArray × Nat × GlyphCache :=
  match e.1 with
  | [c] =>
    match f.glyphs[c.toNat]? with
    | some (some g) =>
      let T := f.matrix * subpixelAdjust (placement r e.2.1 * rm)
      if 0 < g.images.size ∧ T.det ≠ 0 ∧ 0 < g.items.size then
        let q := drawCached f.imageCap W H cm al uc T f.uid c.toNat g acc.2.2 acc.1
        (q.1, acc.2.1 + q.2.1, q.2.2)
      else
        let q := drawGlyph paint f.imageCap W H win cm al uc T g acc.1
        (q.1, acc.2.1 + q.2, acc.2.2)
    | _ => acc
  | _ => acc

private theorem foldl_glyphStep_size (paint : Tiling.CellPainter) (W H : Nat) (win : IRect)
    (cm : Option Mask) (al : Nat) (uc : Nat × Nat × Nat) (f : T3Font) (r : GlyphRun) (rm : Aff)
    (l : List (List UInt8 × Fixed × Fixed)) :
    ∀ (acc : ByteArray × Nat × GlyphCache),
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
      · dsimp only
        split
        · exact drawCached_size _ _ _ _ _ _ _ _ _ _ _ _
        · exact drawGlyph_size _ _ _ _ _ _ _ _ _ _ _
      · rfl
    · rfl

/-- MuPDF's Type 3 advance: `pdf_load_type3_font` stores `/Widths` × `FontMatrix.a` × 1000 in
its integer metrics table (`pdf_add_hmtx`), truncating the advance to a multiple of `1/1000`
of the font size (toward zero). Positions of glyphs drawn here follow it; text extraction
truncates the same way (`Text.type3TruncWidth`, task 7.3l), so this is idempotent on the
`FontInfo` of a Type 3 font and kept for fonts built elsewhere. -/
def truncWidth (w : Fixed) : Fixed := Text.type3TruncWidth w

/-- The paint passes of a Type 3 run (task 7.3l), as MuPDF's `pdf_flush_text` with a cacheable
Type 3 font: fill modes paint the glyphs with the fill colour and alpha (`fz_fill_text`), stroke
modes with the stroke colour and alpha (`fz_stroke_text`, whose `fz_render_stroked_glyph` renders
a Type 3 glyph filled, not outlined); fill-and-stroke modes paint both, fill first. Modes 3 and 7
paint nothing. -/
def passes (r : GlyphRun) : List (Color × Comp) :=
  let f := (r.fill.color, r.fill.alpha)
  let k := (r.stroke.color, r.stroke.alpha)
  match r.renderMode with
  | .fill | .fillClip => [f]
  | .stroke | .strokeClip => [k]
  | .fillStroke | .fillStrokeClip => [f, k]
  | .invisible | .clip => []

/-- **Render a glyph run of a Type 3 font** (see the module doc) onto the page state `st`
(`W × H`, page → device `m`), glyphs drawn by the cell painter `paint`, positions from the
run's `FontInfo` `fi` (advances truncated as MuPDF's, `truncWidth`), once per paint pass
(`passes`: fill and/or stroke colour), image glyphs through the page's glyph cache `gc`
(returned updated). -/
def renderRun (cfg : Fill.Config) (paint : Tiling.CellPainter) (m : Aff) (W H : Nat)
    (fi : FontInfo) (f : T3Font) (st : Clip.RState) (gc : GlyphCache) (r : GlyphRun)
    (clip : Content.Clip) : Clip.RState × GlyphCache :=
  if !r.renderMode.paints then (st, gc) else
  let c := Clip.clipMaskC cfg m W H st.cache clip
  let win := Clip.itemWindow W H c.1
  let fi' : FontInfo := { fi with width := fun code => truncWidth (fi.width code) }
  let entries := Text.layoutParts fi' (Text.runTextState r) r.font.size Fixed.zero r.parts
  let rm := Aff.ofMatrix r.tm * Aff.ofMatrix r.ctm * m
  let q := (passes r).foldl (fun (acc : ByteArray × Nat × GlyphCache) (pc : Color × Comp) =>
    entries.foldl (glyphStep paint W H win c.1 (Clip.compByte pc.2) (Clip.deviceRGB pc.1) f r rm)
      acc) (st.buf, 0, gc)
  ({ buf := q.1, cache := c.2.1, steps := st.steps + c.2.2 + q.2.1 }, q.2.2)

private theorem foldl_passes_size (paint : Tiling.CellPainter) (W H : Nat) (win : IRect)
    (cm : Option Mask) (f : T3Font) (r : GlyphRun) (rm : Aff)
    (entries : List (List UInt8 × Fixed × Fixed)) (ps : List (Color × Comp)) :
    ∀ (acc : ByteArray × Nat × GlyphCache),
      (ps.foldl (fun (acc : ByteArray × Nat × GlyphCache) (pc : Color × Comp) =>
        entries.foldl (glyphStep paint W H win cm (Clip.compByte pc.2) (Clip.deviceRGB pc.1) f r rm)
          acc) acc).1.size = acc.1.size := by
  induction ps with
  | nil => intro acc; rfl
  | cons p rest ih =>
    intro acc
    simp only [List.foldl_cons]
    rw [ih]
    exact foldl_glyphStep_size _ _ _ _ _ _ _ _ _ _ _ _

/-- **Rendering a Type 3 run preserves the buffer size.** -/
theorem renderRun_size (cfg : Fill.Config) (paint : Tiling.CellPainter) (m : Aff) (W H : Nat)
    (fi : FontInfo) (f : T3Font) (st : Clip.RState) (gc : GlyphCache) (r : GlyphRun)
    (clip : Content.Clip) :
    (renderRun cfg paint m W H fi f st gc r clip).1.buf.size = st.buf.size := by
  unfold renderRun
  split
  · rfl
  · exact foldl_passes_size _ _ _ _ _ _ _ _ _ _ _

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
