import SafePdf.Core.Raster.Clip
import SafePdf.Core.Content.Run

/-!
# Tiling patterns (task 7.3g)

Plan.md §6 Phase 7 ("patterns"; "Proven: totality, resource bounds"), §4 **S3**.
ISO 32000-2 §8.7.3.1 (tiling patterns, `PatternType 1`: `/PaintType`, `/TilingType`,
`/BBox`, `/XStep`, `/YStep`, `/Resources`, `/Matrix`), §8.7.3.2 (coloured, PaintType 1),
§8.7.3.3 (uncoloured, PaintType 2: the cell's colour operators are ignored, the colour comes
from the `scn` operands).

## Loading (`loadTiling`, `loadTilings`)

A tiling pattern is a content stream. Its operators are tokenized and run through the 5.2b
runner (`Run.runOps`, nesting fuel `Limits.maxXObjectDepth`, the pattern's own `/Resources`,
the pattern's object number on the visited path and as the resource owner) from a fresh
machine, so the cell's display items are in **pattern space** (identity CTM). The runner's
operator cap and form budget are **shared** with the page: `Budget` carries what is left
(`Limits.maxOpsPerPage` minus the page's operators, `Env.maxForms` minus its forms), every
pattern run is charged to it, and an exhausted budget yields an empty cell. `/BBox` is
normalised (`x0 ≤ x1`, `y0 ≤ y1`); `/XStep`/`/YStep` must be nonzero numbers; `/TilingType` is
ignored (all three types are rendered as type 1, as MuPDF does).

## Rendering (`renderTiling`, `renderTilingFill`)

`T = pm × m` maps pattern space to device pixels (`pm`: the pattern matrix already combined
with the base matrix of the content that set the pattern; `m`: page → device). The paint area
is the fill coverage mask (fill path ∩ clip, `mk`); its rectangle ∩ the page is the window
`wr`. The tile instances that can touch `wr` are found exactly in pattern space (`tileRange`:
the window corners through `T⁻¹`, one instance of margin each side).

**Cell layers.** A cell is rendered by a **cell painter** (`CellPainter`, a parameter: the
renderer of the caller, so text, images and shadings in cells paint as on the page;
`pathPainter` = `Clip.renderItem` for paths) into an offscreen buffer **twice**, over opaque
white and over opaque black. Source-over is affine in the backdrop, so for every pixel
`black = P` (the premultiplied cell colour) and `white − black = 255 − α` (its coverage);
`α = max_c (255 + black_c − white_c)` (`≥ black_c`, so `P ≤ α` per channel). For PaintType 2
only `α` is kept and the colour is the given device colour (`P = colour · α`). The cell is
clipped to the layer's integer rectangle (the device bounding box of the `/BBox`), not to the
`/BBox` itself with anti-aliasing: this is what MuPDF 1.25.1 does (`fz_draw_begin_tile`
allocates the tile pixmap over `fz_irect_from_rect(view × ctm)`; `pdf_show_pattern` adds no
clip), and an anti-aliased `/BBox` clip would leave light seams wherever two rotated tiles
meet.

**Mode A (blit)**, cell at most `maxCellPixels`: the cell is rendered once over its device
bounding box `cr` (exact subpixel origin of instance (0, 0)) and blitted at instance
`(i, j)` at the **integer** offset `trunc(cr.x0 + Δx) − cr.x0` (and likewise `y`), `Δ` the
device vector of `(i · XStep, j · YStep)` — MuPDF's `fz_draw_end_tile` sets the pixmap origin
to `ttm.e`/`ttm.f` by C float → int conversion (truncation). It is clipped to `wr` and painted
through the fill mask and the fill alpha: `out = P·w + d·(255 − α·w)` with `w = cov · alpha`
(`blitRow`, `UInt32`, all bytes `≤ 255`). Instances are painted row by row (`j` outer, `i`
inner, as MuPDF), so overlapping tiles (steps smaller than the `/BBox`) compose in order.
Allowed when the instance count is at most `maxTiles` and `count × cell area ≤ maxTileWork`;
otherwise the fill is painted with the cell's **mean colour** (`meanFill`: Σ P / Σ α at
opacity mean α) — the perceptual average of a tiny, dense pattern.

**Mode B (direct)**, cell larger than `maxCellPixels` (typically a page-sized cell drawn once
or a few times; MuPDF also draws such cells instance by instance): each instance is rendered
separately at its exact position into a layer covering only its visible part
(`devRect ∩ wr`), at most `maxDirectTiles` instances; beyond that, mid grey (the pre-7.3g
fallback).

Nothing is painted for a singular matrix, a zero step, an empty `/BBox` or an empty cell.

## Bounds (S3) and what is proven

`renderTiling_size`, `renderTilingFill_size`: the page buffer keeps its size whatever the
painter returns (every write is `Clip.setB`/`Clip.composite`). The counted work
(`RState.steps`) adds the painter's own counted work, the cell and `/BBox` masks, and the blit
pixels (`count × cell area ≤ maxTileWork` in mode A, at most `maxDirectTiles` layers of at
most a window each in mode B). The cell painter's own work is bounded by the painter (for
`pathPainter`, `Clip.renderItem_steps_le` on a `w × h` cell). Local caps (candidates for `Limits`): `maxCellPixels` 2²⁰,
`maxTiles` 2²⁰, `maxTileWork` 2²⁷, `maxDirectTiles` 64.

## Task 7.3h2 (strokes, text, full cells, nesting)

`loadTilingsWith` looks up the patterns of fill **and stroke** colours of paths and glyph
runs (`itemKeys`), and, for `maxTileDepth + 1` levels, the patterns used inside the cells just
loaded (found by the cell's own `ResRef`: the runner records `.form num 0` or `.ref` for a
pattern named in the pattern's `/Resources`); a key is loaded once, so a pattern using
itself terminates. Before a cell runs, a caller-supplied `grow` extends a context (the page
renderer adds the fonts of the pattern's resources). `renderTilingStroke` paints a stroke
mask with a tiling, `paintTilingMask` any coverage mask (glyph runs). Full cell painters
(text, images, shadings, transparency in cells; nested patterns painted at one depth less,
depth 0 by `pathPainter` = mid grey) are `Glyph.cellPainterD`.

## Gaps

* The cell's graphics state starts from the default state, not the pattern's parent's (the
  CTM is the pattern matrix; line width etc. reset — ISO 32000-2 §8.7.3.1 says inherited).
* Patterns nested deeper than `maxTileDepth` paint mid grey (MuPDF has no such cap).
-/

namespace SafePdf.Core.Raster.Tiling

open SafePdf SafePdf.Core
open SafePdf.Core.Raster.Geom
open SafePdf.Core.Raster.Fill (IRect Mask Config)
open SafePdf.Core.Content (Fixed Comp Color Source FillStyle FillRule Matrix Clip Path
  DisplayList DisplayItem Env St Frame ResRef PatternUse)

/-! ## 1. Caps -/

/-- Largest cell rendered once and blitted (pixels of its device bounding box). -/
def maxCellPixels : Nat := 1 <<< 20

/-- Largest number of tile instances blitted for one fill. -/
def maxTiles : Nat := 1 <<< 20

/-- Largest blit work (instances × cell pixels) for one fill. -/
def maxTileWork : Nat := 1 <<< 27

/-- Largest number of instances rendered directly (cells above `maxCellPixels`). -/
def maxDirectTiles : Nat := 64

/-! ## 2. Loading -/

/-- A tiling pattern (`PatternType 1`) with its cell content run into display items in
pattern space. -/
structure Tiling where
  /-- Object number of the pattern stream. -/
  num : Nat
  /-- `/PaintType`: 1 coloured, 2 uncoloured. -/
  paintType : Nat
  /-- `/BBox` (normalised: `x0 ≤ x1`, `y0 ≤ y1`). -/
  bbox : Fixed × Fixed × Fixed × Fixed
  /-- `/XStep` (nonzero). -/
  xstep : Rat
  /-- `/YStep` (nonzero). -/
  ystep : Rat
  /-- `/Matrix`: pattern space → the default space of the content that set the pattern. -/
  matrix : Matrix
  /-- The pattern's `/Resources` (resolved; for a cell painter that loads the cell's fonts,
  images and shadings by these names). -/
  res : Dict
  /-- The cell's display items, in pattern space. -/
  items : DisplayList

/-- What is left of the page's operator and form budgets for pattern cells. -/
structure Budget where
  /-- Operators (`Limits.maxOpsPerPage` minus those already executed). -/
  ops : Nat
  /-- Form expansions (`Env.maxForms` minus those already expanded). -/
  forms : Nat
  deriving Repr, Inhabited

/-- `min` and `max` of two fixed-point numbers. -/
def ordF (a b : Fixed) : Fixed × Fixed := if a.raw ≤ b.raw then (a, b) else (b, a)

/-- A nonzero number as `ℚ`. -/
def stepOf (o : Option PdfObject) : Option Rat :=
  match o.bind Content.Run.numOf with
  | some x => if x.raw = 0 then none else some (Fixed.toRat x)
  | none => none

/-- The pattern's parameters (`none` unless `PatternType 1`, PaintType 1 or 2, a `/BBox` and
nonzero steps), without the content. -/
def header (d : Dict) : Option (Nat × (Fixed × Fixed × Fixed × Fixed) × Rat × Rat) :=
  match Dict.get? d (Content.Run.nm "PatternType"), Dict.get? d (Content.Run.nm "PaintType"),
      Content.Run.bboxOf d, stepOf (Dict.get? d (Content.Run.nm "XStep")),
      stepOf (Dict.get? d (Content.Run.nm "YStep")) with
  | some (.int 1), some (.int pt), some (x0, y0, x1, y1), some xs, some ys =>
    if pt = 1 ∨ pt = 2 then
      let (a, c) := ordF x0 x1
      let (b, e) := ordF y0 y1
      some (pt.toNat, (a, b, c, e), xs, ys)
    else none
  | _, _, _, _, _ => none

/-- Run a cell's content (`bytes`) with resources `res` under the budget `bud`: the runner's
operator cap becomes `bud.ops`, its form cap `bud.forms`. Returns the items, the source and
observer states and the remaining budget. -/
def runCell {σ ω : Type} (env : Env σ ω) (s : σ) (obs : ω) (bud : Budget) (num : Nat)
    (res : Dict) (bytes : ByteArray) : DisplayList × σ × ω × Budget :=
  let lim := env.cfg.limits
  let env' : Env σ ω :=
    { env with cfg := { env.cfg with limits := { lim with maxOpsPerPage := bud.ops } },
               maxForms := bud.forms }
  let t := Content.Ops.tokenize lim bytes
  let r := Content.Run.runOps env' lim.maxXObjectDepth (Content.Frame.mk' res [num] num 0 Matrix.identity) (St.init s obs) t.ops
  (r.items, r.s, r.obs, { ops := bud.ops - r.ops, forms := bud.forms - r.forms })

/-- **Load a tiling pattern** with a growing context (task 7.3h2): as `loadTiling`, but
before the cell runs, `grow fa s num res` extends the context `fa` with what the cell's
resources need (e.g. their fonts, so the cell's text is positioned with real advances), and
the cell runs in `envOf fa`. -/
def loadTilingWith {α σ ω : Type} (envOf : α → Env σ ω) (grow : α → σ → Nat → Dict → α × σ)
    (fa : α) (s : σ) (obs : ω) (bud : Budget) (o : PdfObject) :
    Option Tiling × α × σ × ω × Budget :=
  let src := (envOf fa).src
  match o with
  | .ref n g =>
    match src.fetch s n g with
    | (.ok (.stream st), s) =>
      match header st.dict with
      | none => (none, fa, s, obs, bud)
      | some (pt, bb, xs, ys) =>
        match src.decode s n st with
        | (.ok bytes, s) =>
          let (res, s) := match Dict.get? st.dict (Content.Run.nm "Resources") with
            | some r => Content.Run.dictOf src s r
            | none => ([], s)
          let (fa, s) := grow fa s n res
          let (items, s, obs, bud) := runCell (envOf fa) s obs bud n res bytes
          (some ⟨n, pt, bb, xs, ys, Content.Run.formMatrix st.dict, res, items⟩, fa, s, obs, bud)
        | (.error _, s) => (none, fa, s, obs, bud)
    | (_, s) => (none, fa, s, obs, bud)
  | _ => (none, fa, s, obs, bud)

/-- **Load a tiling pattern** from its (indirect) object: parse the dictionary, decode the
stream, run the cell. `none` for anything that is not a well-formed tiling pattern. -/
def loadTiling {σ ω : Type} (env : Env σ ω) (s : σ) (obs : ω) (bud : Budget) (o : PdfObject) :
    Option Tiling × σ × ω × Budget :=
  let r := loadTilingWith (fun (_ : Unit) => env) (fun u s _ _ => (u, s)) () s obs bud o
  (r.1, r.2.2)

/-- The tiling patterns of a page **by resource** (task 7.3h): keyed by where the pattern
resource lives and its name (`PatternUse.res`, the colour's name), as
`Shading.ShadingTable`, so patterns used inside forms and annotation appearances are found
too (`none`: not a loadable tiling pattern, e.g. a shading pattern). -/
structure TilingTable where
  /-- Patterns by `(ResRef, name)`. -/
  patterns : List ((ResRef × Name) × Option Tiling) := []
  /-- Budget left after loading. -/
  budget : Budget := { ops := 0, forms := 0 }

instance : Inhabited TilingTable := ⟨{}⟩

/-- The tiling pattern of a pattern resource. -/
def TilingTable.get? (t : TilingTable) (r : ResRef) (n : Name) : Option Tiling :=
  ((t.patterns.find? (·.1 == (r, n))).map (·.2)).join

/-- Where the pattern of a colour lives and its name (`none` for a non-pattern colour);
without a recorded use, the page's resources. -/
def patternKey (c : Color) (u : Option PatternUse) : Option (ResRef × Name) :=
  match c with
  | .pattern n => some ((u.map (·.res)).getD .page, n)
  | _ => none

/-- The PaintType 2 colour of a pattern use (the `scn` operands, §8.7.3.3); black without
operands. -/
def underOf (u : Option PatternUse) : Color := (u.bind (·.under)).getD (.gray Comp.zero)

/-- **The tiling pattern a fill colour denotes** (task 7.3h): the loaded pattern, its matrix
pattern space → page space (`Matrix.mul pat.matrix use.base`: the pattern matrix maps to the
default space of the content that set the pattern, the base matrix on to the page) and the
PaintType 2 colour. -/
def TilingTable.tileOf (t : TilingTable) (c : Color) (u : Option PatternUse) :
    Option (Tiling × Aff × Color) :=
  match patternKey c u with
  | some (r, n) =>
    (t.get? r n).map fun pat =>
      (pat, Aff.ofMatrix (Matrix.mul pat.matrix ((u.map (·.base)).getD Matrix.identity)),
        underOf u)
  | none => none

/-- Largest nesting of tiling patterns painted with their full cells (task 7.3h2): the page's
patterns are depth `maxTileDepth`, a pattern used inside one of their cells one less, …; the
cells of a depth-0 pattern are painted by `pathPainter` (patterns in them: mid grey). Patterns
are loaded for `maxTileDepth + 1` levels. -/
def maxTileDepth : Nat := 2

/-- The pattern keys an item's colours name (task 7.3h2): fill and stroke colours of paths and
glyph runs. -/
def itemKeys : DisplayItem → List (ResRef × Name)
  | .fillPath _ _ style _ => (patternKey style.color style.pattern).toList
  | .strokePath _ style _ => (patternKey style.color style.pattern).toList
  | .glyphRun r _ =>
    (patternKey r.fill.color r.fill.pattern).toList ++
      (patternKey r.stroke.color r.stroke.pattern).toList
  | _ => []

/-- Accumulator of `loadTilingsWith`: the table, the context, the source and observer states,
and the items of the cells loaded at the current level (the next level's input). -/
structure LoadAcc (α σ ω : Type) where
  /-- Patterns loaded so far. -/
  tab : TilingTable
  /-- The context (`loadTilingWith`). -/
  fa : α
  /-- Source state. -/
  s : σ
  /-- Observer state. -/
  obs : ω
  /-- Items of the cells loaded at this level. -/
  fresh : DisplayList

/-- Load the pattern `key` (once: a key already in the table is skipped, so a pattern using
itself is loaded once). -/
def loadKey {α σ ω : Type} (envOf : α → Env σ ω) (grow : α → σ → Nat → Dict → α × σ)
    (pageRes : Dict) (acc : LoadAcc α σ ω) (key : ResRef × Name) : LoadAcc α σ ω :=
  if acc.tab.patterns.any (·.1 == key) then acc else
  let (o, s) := Content.Run.resLookup (envOf acc.fa).src acc.s pageRes "Pattern" key.1 key.2
  match o with
  | some o =>
    let (p, fa, s, obs, b) := loadTilingWith envOf grow acc.fa s acc.obs acc.tab.budget o
    { tab := { patterns := (key, p) :: acc.tab.patterns, budget := b }, fa, s, obs,
      fresh := match p with
        | some t => acc.fresh ++ t.items
        | none => acc.fresh }
  | none => { acc with s, tab := { acc.tab with patterns := (key, none) :: acc.tab.patterns } }

/-- Load the patterns named by `items` (inside soft masks too), then, `n − 1` more levels, those
named by the cells just loaded. -/
def loadLevels {α σ ω : Type} (envOf : α → Env σ ω) (grow : α → σ → Nat → Dict → α × σ)
    (pageRes : Dict) (fuel : Nat) : Nat → DisplayList → LoadAcc α σ ω → LoadAcc α σ ω
  | 0, _, acc => acc
  | n + 1, items, acc =>
    let acc := Content.DisplayList.foldDeep (fun acc it =>
      (itemKeys it).foldl (loadKey envOf grow pageRes) acc) fuel { acc with fresh := #[] } items
    loadLevels envOf grow pageRes fuel n acc.fresh acc

/-- **Load the tiling patterns of a display list** with a growing context (task 7.3h2): every
pattern named by a fill or stroke colour of a path or glyph run (items nested in soft masks
too, `DisplayList.foldDeep` with `Limits.maxXObjectDepth` levels), once per `(ResRef, name)`,
looked up by `Run.resLookup` (`pageRes`: the page's resources; patterns used in a cell are
found through the cell's `ResRef`, `.form num 0` or `.ref`), charging the shared budget
`bud`; nested patterns for `maxTileDepth + 1` levels. Before each cell runs, `grow` extends
the context (e.g. with the fonts of the pattern's resources). Returns the table, the final
context, the source and observer states. -/
def loadTilingsWith {α σ ω : Type} (envOf : α → Env σ ω) (grow : α → σ → Nat → Dict → α × σ)
    (fa : α) (s : σ) (obs : ω) (bud : Budget) (pageRes : Dict) (items : DisplayList) :
    TilingTable × α × σ × ω :=
  let acc := loadLevels envOf grow pageRes (envOf fa).cfg.limits.maxXObjectDepth
    (maxTileDepth + 1) items ⟨{ budget := bud }, fa, s, obs, #[]⟩
  (acc.tab, acc.fa, acc.s, acc.obs)

/-- **Load the tiling patterns of a display list** (`loadTilingsWith` without a context). -/
def loadTilings {σ ω : Type} (env : Env σ ω) (s : σ) (obs : ω) (bud : Budget) (pageRes : Dict)
    (items : DisplayList) : TilingTable × σ × ω :=
  let r := loadTilingsWith (fun (_ : Unit) => env) (fun u s _ _ => (u, s)) () s obs bud pageRes
    items
  (r.1, r.2.2)

/-- The items of every loaded cell (for the loaders of images and shadings, task 7.3h2). -/
def TilingTable.cellItems (t : TilingTable) : DisplayList :=
  t.patterns.foldl (fun acc e => match e.2 with
    | some p => acc ++ p.items
    | none => acc) #[]

/-! ## 3. Cell layers -/

/-- A premultiplied RGBA layer (`4 · w · h` bytes; alpha byte = coverage `α`, colour bytes
`≤ α`) placed at device `(x0, y0)`. -/
structure Layer where
  /-- Left column. -/
  x0 : Int
  /-- Top row. -/
  y0 : Int
  /-- Width. -/
  w : Nat
  /-- Height. -/
  h : Nat
  /-- Premultiplied RGBA bytes. -/
  data : ByteArray

/-- A cell renderer: pattern space → cell-buffer matrix, buffer width and height, the
initial opaque RGBA buffer, the cell items ↦ the painted buffer and the counted work. -/
abbrev CellPainter := Aff → Nat → Nat → ByteArray → DisplayList → ByteArray × Nat

/-- The path-only cell painter (`Clip.renderItem` with the default stroker). -/
def pathPainter (cfg : Config) : CellPainter := fun m W H b items =>
  let st := items.foldl (Clip.renderItem cfg m W H Clip.defaultStroke) { buf := b }
  (st.buf, st.steps)

/-- An opaque black RGBA buffer. -/
def blackBuf (W H : Nat) : ByteArray :=
  ByteArray.mk ((Array.range (4 * W * H)).map fun i => if i % 4 = 3 then 255 else 0)

/-- Layer bytes from the white- and black-backdrop renders `wb`, `bb`, pixel `i` onwards;
`uc`: the PaintType 2 colour. -/
def layerLoop (wb bb : ByteArray) (uc : Option (Nat × Nat × Nat)) :
    (n i : Nat) → ByteArray → ByteArray
  | 0, _, acc => acc
  | n + 1, i, acc =>
    let j := 4 * i
    let a0 := 255 + Clip.getB bb j - Clip.getB wb j
    let a1 := 255 + Clip.getB bb (j + 1) - Clip.getB wb (j + 1)
    let a2 := 255 + Clip.getB bb (j + 2) - Clip.getB wb (j + 2)
    let a := min 255 (max a0 (max a1 a2))
    let (r, g, b) := match uc with
      | none => (min a (Clip.getB bb j), min a (Clip.getB bb (j + 1)), min a (Clip.getB bb (j + 2)))
      | some (r, g, b) => (Clip.mul255 (min r 255) a, Clip.mul255 (min g 255) a,
          Clip.mul255 (min b 255) a)
    let acc := acc.push (UInt8.ofNat r) |>.push (UInt8.ofNat g) |>.push (UInt8.ofNat b)
      |>.push (UInt8.ofNat a)
    layerLoop wb bb uc n (i + 1) acc

/-- **Render a cell layer** over the device rectangle `r` through `T` (pattern space →
device): two renders (white and black backdrops); the layer's rectangle is the only clip
(as MuPDF's tile pixmap). Returns the layer and the counted work. -/
def cellLayer (paint : CellPainter) (T : Aff) (pat : Tiling)
    (uc : Option (Nat × Nat × Nat)) (r : IRect) : Layer × Nat :=
  let w := r.width
  let h := r.height
  let Tc := T * Aff.translate (-(r.x0 : Rat)) (-(r.y0 : Rat))
  let wb := paint Tc w h (Clip.whiteBuf w h) pat.items
  let bb := paint Tc w h (blackBuf w h) pat.items
  let data := layerLoop wb.1 bb.1 uc (w * h) 0 (ByteArray.mk (Array.mkEmpty (4 * w * h)))
  (⟨r.x0, r.y0, w, h, data⟩, wb.2 + bb.2 + w * h)

/-! ## 4. Blitting -/

/-- One blitted row: `n` pixels, layer bytes from `li`, fill-mask bytes from `mi`, page bytes
from `bi`; `al` the fill alpha. `out = P·w + d·(255 − α·w)` per channel, `w = cov · al`. -/
def blitRow (ld md : ByteArray) (al : UInt32) : (n li mi bi : Nat) → ByteArray → ByteArray
  | 0, _, _, _, b => b
  | n + 1, li, mi, bi, b =>
    let w := Clip.mul255U (Clip.getU md mi) al
    let A := Clip.getU ld (li + 3)
    let b :=
      if w == 0 || A == 0 then b else
      let As := Clip.mul255U A w
      let ia := 255 - As
      let px := fun (c : Nat) (b : ByteArray) =>
        Clip.setB b (bi + c)
          (Clip.mul255U (Clip.getU ld (li + c)) w + (Clip.getU b (bi + c) * ia + 127) / 255).toUInt8
      px 2 (px 1 (px 0 b))
    blitRow ld md al n (li + 4) (mi + 1) (bi + 4) b

/-- `blitRow` preserves the buffer size. -/
theorem blitRow_size (ld md : ByteArray) (al : UInt32) (n li mi bi : Nat) (b : ByteArray) :
    (blitRow ld md al n li mi bi b).size = b.size := by
  induction n generalizing li mi bi b with
  | zero => rfl
  | succ n ih =>
    simp only [blitRow, ih]
    split
    · rfl
    · simp only [Clip.setB_size]

/-- Rows `y, y + 1, …` (`n` of them) of columns `[x, x + cw)` of a layer placed at offset
`(ox, oy)`, through the fill mask `mk`. -/
def blitRows (W : Nat) (L : Layer) (mk : Mask) (al : UInt32) (ox oy x : Int) (cw : Nat) :
    (n : Nat) → (y : Int) → ByteArray → ByteArray
  | 0, _, b => b
  | n + 1, y, b =>
    let li := 4 * Clip.offs (L.x0 + ox) (L.y0 + oy) L.w x y
    let mi := Clip.offs mk.x0 mk.y0 mk.w x y
    let bi := 4 * (y.toNat * W + x.toNat)
    blitRows W L mk al ox oy x cw n (y + 1) (blitRow L.data mk.data al cw li mi bi b)

/-- `blitRows` preserves the buffer size. -/
theorem blitRows_size (W : Nat) (L : Layer) (mk : Mask) (al : UInt32) (ox oy x : Int) (cw : Nat)
    (n : Nat) (y : Int) (b : ByteArray) : (blitRows W L mk al ox oy x cw n y b).size = b.size := by
  induction n generalizing y b with
  | zero => rfl
  | succ n ih => simp only [blitRows, ih, blitRow_size]

/-- **Blit a layer** at integer offset `(ox, oy)` inside the window `wr` (⊆ the fill mask's
rectangle ∩ the page) through the fill mask and the alpha byte `al`. Returns the buffer and
the pixels visited. -/
def blit (W : Nat) (wr : IRect) (mk : Mask) (al : Nat) (L : Layer) (ox oy : Int)
    (b : ByteArray) : ByteArray × Nat :=
  let r : IRect := ⟨L.x0 + ox, L.y0 + oy, L.x0 + ox + L.w, L.y0 + oy + L.h⟩
  let d := r.inter wr
  if d.width = 0 ∨ d.height = 0 then (b, 0) else
  (blitRows W L mk (UInt32.ofNat (min al 255)) ox oy d.x0 d.width d.height d.y0 b,
    d.width * d.height)

/-- `blit` preserves the buffer size. -/
theorem blit_size (W : Nat) (wr : IRect) (mk : Mask) (al : Nat) (L : Layer) (ox oy : Int)
    (b : ByteArray) : (blit W wr mk al L ox oy b).1.size = b.size := by
  unfold blit; simp only; split
  · rfl
  · exact blitRows_size _ _ _ _ _ _ _ _ _ _ _

/-! ## 5. Tile geometry -/

/-- `min` of two rationals. -/
def minQ (a b : Rat) : Rat := if a ≤ b then a else b

/-- `max` of two rationals. -/
def maxQ (a b : Rat) : Rat := if a ≤ b then b else a

/-- Truncate toward zero (C's float → int conversion). -/
def truncQ (q : Rat) : Int := if q < 0 then -((-q).floor) else q.floor

/-- The `/BBox` as rationals. -/
def bboxQ (pat : Tiling) : Rat × Rat × Rat × Rat :=
  let (a, b, c, d) := pat.bbox
  (Fixed.toRat a, Fixed.toRat b, Fixed.toRat c, Fixed.toRat d)

/-- Bounds `(min x, min y, max x, max y)` of the four corners of a rectangle through `T`. -/
def cornerBounds (T : Aff) (b : Rat × Rat × Rat × Rat) : Rat × Rat × Rat × Rat :=
  let (x0, y0, x1, y1) := b
  let p := T.apply ⟨x0, y0⟩
  let q := T.apply ⟨x1, y0⟩
  let r := T.apply ⟨x1, y1⟩
  let s := T.apply ⟨x0, y1⟩
  (minQ (minQ p.x q.x) (minQ r.x s.x), minQ (minQ p.y q.y) (minQ r.y s.y),
   maxQ (maxQ p.x q.x) (maxQ r.x s.x), maxQ (maxQ p.y q.y) (maxQ r.y s.y))

/-- The integer device rectangle covering a pattern-space rectangle through `T`. -/
def devRect (T : Aff) (b : Rat × Rat × Rat × Rat) : IRect :=
  let (x0, y0, x1, y1) := cornerBounds T b
  ⟨x0.floor, y0.floor, x1.ceil, y1.ceil⟩

/-- Instance indices `lo … lo + n − 1` along one axis: those whose cell `[b0, b1] + i·step`
can meet `[u0, u1]` (one instance of margin each side; `step ≠ 0`). -/
def axisRange (u0 u1 b0 b1 step : Rat) : Int × Nat :=
  let e1 := (u0 - b1) / step
  let e2 := (u1 - b0) / step
  let lo := (minQ e1 e2).floor - 1
  let hi := (maxQ e1 e2).ceil + 1
  (lo, (hi - lo + 1).toNat)

/-- **Tile range** of a window: `(i₀, nᵢ, j₀, nⱼ)` covering every instance that can touch
`wr` (the window's corners mapped to pattern space by `T⁻¹`). -/
def tileRange (T : Aff) (pat : Tiling) (wr : IRect) : Int × Nat × Int × Nat :=
  let (u0, v0, u1, v1) := cornerBounds T.inv (wr.x0, wr.y0, wr.x1, wr.y1)
  let (bx0, by0, bx1, by1) := bboxQ pat
  let (i0, ni) := axisRange u0 u1 bx0 bx1 pat.xstep
  let (j0, nj) := axisRange v0 v1 by0 by1 pat.ystep
  (i0, ni, j0, nj)

/-- Fold `f` over instances `(i₀ + a, j₀ + b)`, `b` outer, `a` inner. -/
def forTiles {α : Type} (i0 j0 : Int) (ni nj : Nat) (f : α → Int → Int → α) (acc : α) : α :=
  (List.range nj).foldl (fun acc (b : Nat) =>
    (List.range ni).foldl (fun acc (a : Nat) => f acc (i0 + (a : Int)) (j0 + (b : Int))) acc) acc

/-- `forTiles` preserves any invariant `f` preserves. -/
theorem forTiles_inv {α : Type} (P : α → Prop) (i0 j0 : Int) (ni nj : Nat) (f : α → Int → Int → α)
    (hf : ∀ acc i j, P acc → P (f acc i j)) (acc : α) (h : P acc) :
    P (forTiles i0 j0 ni nj f acc) := by
  unfold forTiles
  have inner : ∀ (l : List Nat) (b : Nat) (acc : α), P acc →
      P (l.foldl (fun acc (a : Nat) => f acc (i0 + (a : Int)) (j0 + (b : Int))) acc) := by
    intro l b
    induction l with
    | nil => intro acc h; exact h
    | cons x xs ih => intro acc h; exact ih _ (hf _ _ _ h)
  have outer : ∀ (l : List Nat) (acc : α), P acc →
      P (l.foldl (fun acc (b : Nat) => (List.range ni).foldl
        (fun acc (a : Nat) => f acc (i0 + (a : Int)) (j0 + (b : Int))) acc) acc) := by
    intro l
    induction l with
    | nil => intro acc h; exact h
    | cons x xs ih => intro acc h; exact ih _ (inner _ _ _ h)
  exact outer _ _ h

/-! ## 6. Painting -/

/-- Paint the fill mask with the cell's **mean colour** (Σ P / Σ α, opacity mean α × alpha):
the fallback for too many tiles. -/
def meanFill (W : Nat) (wr : IRect) (mk : Mask) (al : Nat) (L : Layer) (b : ByteArray) :
    ByteArray × Nat :=
  let n := L.w * L.h
  let sums := (List.range n).foldl (fun (s : Nat × Nat × Nat × Nat) i =>
    let j := 4 * i
    (s.1 + Clip.getB L.data j, s.2.1 + Clip.getB L.data (j + 1),
     s.2.2.1 + Clip.getB L.data (j + 2), s.2.2.2 + Clip.getB L.data (j + 3))) (0, 0, 0, 0)
  let (r, g, bl, a) := sums
  if a = 0 ∨ n = 0 then (b, n) else
  let rgb := (min 255 ((r * 255 + a / 2) / a), min 255 ((g * 255 + a / 2) / a),
    min 255 ((bl * 255 + a / 2) / a))
  (Clip.composite b W mk none wr rgb (Clip.mul255 (min 255 ((a + n / 2) / n)) (min al 255)),
    n + wr.width * wr.height)

/-- `meanFill` preserves the buffer size. -/
theorem meanFill_size (W : Nat) (wr : IRect) (mk : Mask) (al : Nat) (L : Layer) (b : ByteArray) :
    (meanFill W wr mk al L b).1.size = b.size := by
  unfold meanFill; simp only
  split
  · rfl
  · exact Clip.composite_size _ _ _ _ _ _ _

/-- The PaintType 2 colour (`none` for coloured patterns). -/
def uncolored (pat : Tiling) (color : Color) : Option (Nat × Nat × Nat) :=
  if pat.paintType = 2 then some (Clip.deviceRGB color) else none

/-- Is the `/BBox` empty? -/
def emptyBBox (pat : Tiling) : Bool :=
  let (x0, y0, x1, y1) := pat.bbox
  x0.raw = x1.raw || y0.raw = y1.raw

/-- Mode A: render the cell once over `cr`, blit every instance (or the mean colour beyond
the caps). -/
def modeA (paint : CellPainter) (W : Nat) (T : Aff) (pat : Tiling)
    (uc : Option (Nat × Nat × Nat)) (cr wr : IRect) (mk : Mask) (al : Nat)
    (rng : Int × Nat × Int × Nat) (b : ByteArray) : ByteArray × Nat :=
  let (i0, ni, j0, nj) := rng
  let cnt := ni * nj
  let (L, s) := cellLayer paint T pat uc cr
  if cnt ≤ maxTiles ∧ cnt * (cr.width * cr.height) ≤ maxTileWork then
    let dx := fun (i j : Int) => truncQ (cr.x0 + i * pat.xstep * T.a + j * pat.ystep * T.c) - cr.x0
    let dy := fun (i j : Int) => truncQ (cr.y0 + i * pat.xstep * T.b + j * pat.ystep * T.d) - cr.y0
    forTiles i0 j0 ni nj (fun (acc : ByteArray × Nat) i j =>
      let r := blit W wr mk al L (dx i j) (dy i j) acc.1
      (r.1, acc.2 + r.2)) (b, s)
  else
    let r := meanFill W wr mk al L b
    (r.1, s + r.2)

/-- `modeA` preserves the buffer size. -/
theorem modeA_size (paint : CellPainter) (W : Nat) (T : Aff) (pat : Tiling)
    (uc : Option (Nat × Nat × Nat)) (cr wr : IRect) (mk : Mask) (al : Nat)
    (rng : Int × Nat × Int × Nat) (b : ByteArray) :
    (modeA paint W T pat uc cr wr mk al rng b).1.size = b.size := by
  unfold modeA; simp only
  split
  · exact forTiles_inv (fun acc : ByteArray × Nat => acc.1.size = b.size) _ _ _ _ _
      (fun acc i j h => by simp only [blit_size]; exact h) _ rfl
  · simp only [meanFill_size]

/-- Mode B: render each instance (at most `maxDirectTiles`) over its visible part. -/
def modeB (paint : CellPainter) (W : Nat) (T : Aff) (pat : Tiling)
    (uc : Option (Nat × Nat × Nat)) (wr : IRect) (mk : Mask) (al : Nat)
    (rng : Int × Nat × Int × Nat) (b : ByteArray) : ByteArray × Nat :=
  let (i0, ni, j0, nj) := rng
  if ni * nj ≤ maxDirectTiles then
    forTiles i0 j0 ni nj (fun (acc : ByteArray × Nat) i j =>
      let Tij := Aff.translate (i * pat.xstep) (j * pat.ystep) * T
      let r := (devRect Tij (bboxQ pat)).inter wr
      if r.width = 0 ∨ r.height = 0 then acc else
      let (L, s) := cellLayer paint Tij pat uc r
      let q := blit W wr mk al L 0 0 acc.1
      (q.1, acc.2 + s + q.2)) (b, 0)
  else
    (Clip.composite b W mk none wr (128, 128, 128) (min al 255), wr.width * wr.height)

/-- `modeB` preserves the buffer size. -/
theorem modeB_size (paint : CellPainter) (W : Nat) (T : Aff) (pat : Tiling)
    (uc : Option (Nat × Nat × Nat)) (wr : IRect) (mk : Mask) (al : Nat)
    (rng : Int × Nat × Int × Nat) (b : ByteArray) :
    (modeB paint W T pat uc wr mk al rng b).1.size = b.size := by
  unfold modeB; simp only
  split
  · refine forTiles_inv (fun acc : ByteArray × Nat => acc.1.size = b.size) _ _ _ _ _ ?_ _ rfl
    intro acc i j h
    split
    · exact h
    · simp only [blit_size]; exact h
  · exact Clip.composite_size _ _ _ _ _ _ _

/-- **Paint a tiling pattern** through the coverage mask `mk` (fill ∩ clip, device pixels)
onto the page state `st` (`W × H`, page → device `m`): `pm` maps pattern space to the page's
default space (pattern `/Matrix` × base matrix), `color` is the PaintType 2 colour, `alpha`
the fill alpha byte. -/
def renderTiling (paint : CellPainter) (m : Aff) (W H : Nat) (st : Clip.RState)
    (pat : Tiling) (pm : Aff) (color : Color) (mk : Mask) (alpha : Nat) : Clip.RState :=
  let T := pm * m
  if T.det = 0 ∨ pat.items.size = 0 ∨ emptyBBox pat then st else
  let wr := mk.rect.inter (Clip.pageRect W H)
  if wr.width = 0 ∨ wr.height = 0 then st else
  let rng := tileRange T pat wr
  let cr := devRect T (bboxQ pat)
  let ca := cr.width * cr.height
  if ca = 0 then st else
  let uc := uncolored pat color
  let r := if ca ≤ maxCellPixels then modeA paint W T pat uc cr wr mk alpha rng st.buf
    else modeB paint W T pat uc wr mk alpha rng st.buf
  { st with buf := r.1, steps := st.steps + r.2 }

/-- Painting a tiling pattern preserves the buffer size. -/
theorem renderTiling_size (paint : CellPainter) (m : Aff) (W H : Nat)
    (st : Clip.RState) (pat : Tiling) (pm : Aff) (color : Color) (mk : Mask) (alpha : Nat) :
    (renderTiling paint m W H st pat pm color mk alpha).buf.size = st.buf.size := by
  unfold renderTiling; simp only
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · split
        · exact modeA_size _ _ _ _ _ _ _ _ _ _ _
        · exact modeB_size _ _ _ _ _ _ _ _ _ _

/-- **Paint a path filled with a tiling pattern** (`DisplayItem.fillPath p rule style clip`
with `style.color = .pattern _`): fill mask ∩ clip, then `renderTiling` with the fill alpha.
`pm`: pattern space → page default space; `color`: the PaintType 2 colour. -/
def renderTilingFill (cfg : Config) (paint : CellPainter) (m : Aff) (W H : Nat)
    (st : Clip.RState) (pat : Tiling) (pm : Aff) (color : Color) (p : Path) (rule : FillRule)
    (alpha : Comp) (clip : Clip) : Clip.RState :=
  let c := Clip.clipMaskC cfg m W H st.room st.cache clip
  let f := Clip.fillCounted cfg m p rule (Clip.itemWindow W H c.1)
  let mk := Clip.combine f.1 c.1
  renderTiling paint m W H
    { st with cache := c.2.1, steps := st.steps + c.2.2 + f.2 + mk.area } pat pm color mk
    (Clip.compByte alpha)

/-- Painting a tiling-pattern fill preserves the buffer size. -/
theorem renderTilingFill_size (cfg : Config) (paint : CellPainter) (m : Aff) (W H : Nat)
    (st : Clip.RState) (pat : Tiling) (pm : Aff) (color : Color) (p : Path) (rule : FillRule)
    (alpha : Comp) (clip : Clip) :
    (renderTilingFill cfg paint m W H st pat pm color p rule alpha clip).buf.size =
      st.buf.size := by
  unfold renderTilingFill
  exact renderTiling_size _ _ _ _ _ _ _ _ _ _

/-- **Paint a path stroked with a tiling pattern** (task 7.3h2; `DisplayItem.strokePath p style
clip` with `style.color = .pattern _`): stroke mask (by `stroke`, as `Clip.renderItem`) ∩
clip, then `renderTiling` with the stroke alpha. -/
def renderTilingStroke (cfg : Config) (paint : CellPainter) (stroke : Clip.StrokeFn) (m : Aff)
    (W H : Nat) (st : Clip.RState) (pat : Tiling) (pm : Aff) (color : Color) (p : Path)
    (style : Content.StrokeStyle) (clip : Clip) : Clip.RState :=
  let c := Clip.clipMaskC cfg m W H st.room st.cache clip
  let fm := stroke cfg m (Clip.itemWindow W H c.1) p style
  let mk := Clip.combine fm c.1
  renderTiling paint m W H { st with cache := c.2.1, steps := st.steps + c.2.2 + mk.area } pat pm
    color mk (Clip.compByte style.alpha)

/-- Painting a tiling-pattern stroke preserves the buffer size. -/
theorem renderTilingStroke_size (cfg : Config) (paint : CellPainter) (stroke : Clip.StrokeFn)
    (m : Aff) (W H : Nat) (st : Clip.RState) (pat : Tiling) (pm : Aff) (color : Color) (p : Path)
    (style : Content.StrokeStyle) (clip : Clip) :
    (renderTilingStroke cfg paint stroke m W H st pat pm color p style clip).buf.size =
      st.buf.size := by
  unfold renderTilingStroke
  exact renderTiling_size _ _ _ _ _ _ _ _ _ _

/-- **Paint a coverage mask with a tiling pattern** (task 7.3h2: pattern-coloured text): the
mask `mk` ∩ the clip mask `cm`, then `renderTiling`; `cc`/`s`: the clip cache and the work
already counted (as `Clip.paintMask`). -/
def paintTilingMask (paint : CellPainter) (m : Aff) (W H : Nat) (st : Clip.RState) (pat : Tiling)
    (pm : Aff) (color : Color) (cm : Option Mask) (mk : Mask) (alpha : Comp) (cc : Clip.ClipCache)
    (s : Nat) : Clip.RState :=
  let mk := Clip.combine mk cm
  renderTiling paint m W H { st with cache := cc, steps := st.steps + s + mk.area } pat pm color mk
    (Clip.compByte alpha)

/-- Painting a mask with a tiling pattern preserves the buffer size. -/
theorem paintTilingMask_size (paint : CellPainter) (m : Aff) (W H : Nat) (st : Clip.RState)
    (pat : Tiling) (pm : Aff) (color : Color) (cm : Option Mask) (mk : Mask) (alpha : Comp)
    (cc : Clip.ClipCache) (s : Nat) :
    (paintTilingMask paint m W H st pat pm color cm mk alpha cc s).buf.size = st.buf.size := by
  unfold paintTilingMask
  exact renderTiling_size _ _ _ _ _ _ _ _ _ _

/-! ## 7. Checks -/

#guard axisRange 0 10 0 2 2 == (-2, 9)
#guard axisRange 0 10 0 2 (-2) == (-6, 9)
#guard truncQ (-3 / 2) == -1 && truncQ (3 / 2) == 1
#guard (blackBuf 1 1).toList == [0, 0, 0, 255]

end SafePdf.Core.Raster.Tiling
