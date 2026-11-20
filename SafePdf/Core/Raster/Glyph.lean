import SafePdf.Core.Raster.Clip
import SafePdf.Core.Text
import SafePdf.Core.Font.Outline
import SafePdf.Core.Raster.Image
import SafePdf.Core.Raster.Transparency
import SafePdf.Core.Raster.Shading
import SafePdf.Core.Annot

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
   elevation). Task 7.2h: `runPath` computes the same rounded points with 64-bit fixed-point
   glyph matrices and a certified rounding test, falling back to `Rat` per point (§3b); the
   exact path stays as the reference `runPathSpec`.
4. **Painting**: all glyphs of a run form one device path, filled once with the nonzero rule
   (7.2a; task 7.2h: as column-disjoint groups of subpaths, `columnGroups`, with the same
   pixels), stroked once (7.2b, line style and CTM of the run's stroke snapshot), composited
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

Task 7.3f: a glyph mask whose colour is a shading-pattern colour is painted with the pattern
(`paintAll`, `Shading.paintPattern`, the run's recorded `PatternUse`); `strokePath` items go
through `Shading.renderStroke` (pattern strokes); `sh` items are painted with their `ca`, and
those with a blend mode or soft mask are bracketed by a one-item transparency group before
the transparency driver sees them (`liftSh`; nested soft masks included).
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
def type1Source (f : Font.Type1.Font1) (enc : Font.Encoding) : GlyphSource :=
  let fm := Aff.ofMatrix f.fontMatrix
  { glyphOf c := (oneByte c).bind fun b => (enc.glyph b.toNat).map .name
    outline
      | .name n => f.outline n
      | .gid _ => .none
    matrix _ := fm
    desc := "Type1 FontFile" }

/-- A simple font with a CFF program: name through `enc` → GID through the charset, else the
code through the CFF's own encoding (as `Text.cffCodeAdvance`). -/
def cffSource (f : Font.CFF.CFFFont) (enc : Font.Encoding) : GlyphSource :=
  let fm := Aff.ofMatrix f.fontMatrix
  { glyphOf c := (oneByte c).bind fun b =>
      match (enc.glyph b.toNat).bind f.gidOfName? with
      | some g => some (.gid g)
      | .none => (f.gidOfCode b).map .gid
    outline
      | .gid g => f.outline g
      | .name _ => .none
    matrix _ := fm
    desc := "Type1C FontFile3" }

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
def ttSource (f : Font.TrueType.TTFont) (symbolic : Bool) (enc : Font.Encoding) : GlyphSource :=
  let fm := ttMatrix f
  { glyphOf c := (oneByte c).bind fun b => (f.glyphOfCode b symbolic enc).map .gid
    outline
      | .gid g => f.glyphOutline g
      | .name _ => .none
    matrix _ := fm
    desc := "TrueType FontFile2" }

/-- A `/CIDFontType2` font: CID = the code's value, GID through `/CIDToGIDMap`. -/
def cidTTSource (f : Font.TrueType.TTFont) (m : Text.CIDToGID) : GlyphSource :=
  let fm := ttMatrix f
  { glyphOf c := (m.gid (Font.CMap.beValue c)).map .gid
    outline
      | .gid g => f.glyphOutline g
      | .name _ => .none
    matrix _ := fm
    desc := "CIDFontType2 FontFile2" }

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

/-! ## 3b. Fixed-point glyph transform (task 7.2h)

`outlineToD` maps every outline point through the exact rational matrix (`Aff.apply`, then
`toSub`): with the composed glyph matrices of real pages (denominators of `10¹⁸` and more)
that is several big-integer `gcd`s per point, and it dominated text pages (≈ 200 ms per
pdfTeX page). `outlineToDF` computes **the same subpixel coordinates** with 64-bit integers:

* per glyph matrix (`GXf.ofAff?`, once per run and font matrix) the linear entries scaled to
  subpixels per raw `Fixed` unit, `ℓ = 256 · m.a / 10⁶` …, as `Â = round(ℓ · 2ᴷ)` with the
  largest `K ≤ 60` keeping `|Â| ≤ 2²⁴`;
* per glyph (`GXf.off`) the translation `ε = 256 · m.e` split exactly into `⌊ε⌋` and the
  fraction `Φ = round(frac ε · 2ᴷ)`;
* per point (raw `X`, `Y` with `|X|, |Y| ≤ 2³⁶`; products then stay below `2⁶²`),
  `t = Â·X + Ĉ·Y + Φ + 2ᴷ⁻¹` approximates `2ᴷ · (256 · x' − ⌊ε⌋ + 1/2)` within
  `err = (|X| + |Y| + 1)/2 + 2` (each rounding at most `1/2` per unit of `|X|`, `|Y|`, the
  fraction's and `÷ 3`'s); when `t mod 2ᴷ` lies at least `err` away from both ends of
  `[0, 2ᴷ)`, `⌊t / 2ᴷ⌋ + ⌊ε⌋` **is** `toSub x'` (round half up of the exact value);
* otherwise (near a rounding boundary, about one coordinate in `2¹³`; or out-of-range raw
  values; or a matrix without a usable `K`) the point goes through the exact `Rat` path of
  `segToD`, computed from the glyph's exact matrix (passed lazily).

TrueType control points `twoThirds` are mapped from glyph space as `(X₀ + 2·X_c) / 3`
(affine maps commute with the combination; the `÷ 3` is folded into the error bound). The
reference stays `outlineToD`; suite `raster-glyph-spec` checks byte equality of device paths
on random outlines, matrices, sizes and positions, and of whole runs (`runPath` vs
`runPathSpec`). -/

/-- Most `|Â|` of a fixed-point glyph matrix (`2²⁴`). -/
def gxLinCap : Nat := 16777216

/-- Most `|X|`, `|Y|` (raw `Fixed`, `10⁻⁶` glyph units) on the fixed-point path (`2³⁶`). -/
def gxPtCap : Nat := 68719476736

/-- A glyph matrix's linear part in fixed point: entries `round(256 · m.{a,b,c,d} / 10⁶ · 2ᴷ)`
and `2ᴷ`, `2ᴷ⁻¹`. -/
structure GXf where
  /-- The shift `K` (`1 ≤ K ≤ 60`). -/
  k : Nat
  /-- `2ᴷ`. -/
  one : Int64
  /-- `2ᴷ⁻¹`. -/
  half : Int64
  /-- Scaled `m.a`. -/
  a : Int64
  /-- Scaled `m.b`. -/
  b : Int64
  /-- Scaled `m.c`. -/
  c : Int64
  /-- Scaled `m.d`. -/
  d : Int64

/-- `256 · q / 10⁶`: subpixels per raw `Fixed` unit. -/
def subPerRaw (q : Rat) : Rat := q * 256 / 1000000

/-- The largest `K` with `|q| · 2ᴷ ≤ 2²⁴` (`none` if even `K = 0` fails), capped at 60. -/
def gxShift (q : Rat) : Option Nat :=
  if q.num = 0 then some 60 else
  let qq := (gxLinCap * q.den) / q.num.natAbs
  if qq = 0 then none else some (min 60 (Nat.log2 qq))

/-- `round(q · 2ᴷ)` (halves up). -/
def fixK (k : Nat) (q : Rat) : Int := roundDivI (q.num * (2 ^ k : Nat)) (q.den : Int)

/-- The fixed-point linear part of `m`, when some `K ≥ 1` keeps every entry within `2²⁴`. -/
def GXf.ofAff? (m : Aff) : Option GXf :=
  let la := subPerRaw m.a
  let lb := subPerRaw m.b
  let lc := subPerRaw m.c
  let ld := subPerRaw m.d
  match gxShift la, gxShift lb, gxShift lc, gxShift ld with
  | some ka, some kb, some kc, some kd =>
    let k := min (min ka kb) (min kc kd)
    if k = 0 then none else
    some { k, one := ((2 ^ k : Nat) : Int).toInt64, half := ((2 ^ (k - 1) : Nat) : Int).toInt64,
           a := (fixK k la).toInt64, b := (fixK k lb).toInt64, c := (fixK k lc).toInt64,
           d := (fixK k ld).toInt64 }
  | _, _, _, _ => none

/-- A glyph's translation in fixed point: `⌊256 · m.e⌋` and `round(frac(256 · m.e) · 2ᴷ)`, same
for `f`. -/
structure GOff where
  /-- `⌊256 · m.e⌋`. -/
  ex : Int
  /-- Fraction of `256 · m.e`, times `2ᴷ`, rounded. -/
  fx : Int64
  /-- `⌊256 · m.f⌋`. -/
  ey : Int
  /-- Fraction of `256 · m.f`, times `2ᴷ`, rounded. -/
  fy : Int64
  /-- Extra error bound of `fx`, `fy` (units of `2⁻ᴷ` subpixel; 0 when computed exactly). -/
  terr : Int64 := 0

/-- `⌊q⌋` and `round(frac q · 2ᴷ)` (in `[0, 2ᴷ]`). -/
def splitK (k : Nat) (q : Rat) : Int × Int64 :=
  (q.num / (q.den : Int), (roundDivI ((q.num % (q.den : Int)) * (2 ^ k : Nat)) (q.den : Int)).toInt64)

/-- The fixed-point translation of a glyph whose matrix has translation `(e, f)` (pixels). -/
def GXf.off (g : GXf) (e f : Rat) : GOff :=
  let x := splitK g.k (256 * e)
  let y := splitK g.k (256 * f)
  ⟨x.1, x.2, y.1, y.2, 0⟩

/-- The translation of a run's glyphs in fixed point, per font matrix: the glyph at offset
`tx = T / 10⁶` has translation `256 · (L.e + tx · rm.a, L.f + tx · rm.b)` (subpixels), stored as
`L`'s translation split by `GXf.off` plus the slopes `round(256 · rm.{a,b} / 10⁶ · 2ᴷ)`. -/
structure GTx where
  /-- `GXf.off` of `L`'s translation. -/
  base : GOff
  /-- Scaled `rm.a` (per raw unit of `tx`). -/
  va : Int64
  /-- Scaled `rm.b`. -/
  vb : Int64
  /-- Largest `|T|` handled: `min 2⁴⁰ ⌊2⁶¹ / max(|va|, |vb|, 1)⌋`, so `|va · T|, |vb · T| ≤ 2⁶¹`. -/
  tmax : Int64

/-- The `GTx` of `L` and `rm` for `g`, when the slopes are within `2⁴⁰`. -/
def GTx.make? (g : GXf) (L rm : Aff) : Option GTx :=
  let va := fixK g.k (subPerRaw rm.a)
  let vb := fixK g.k (subPerRaw rm.b)
  if absLe va 1099511627776 && absLe vb 1099511627776 then
    let tmax : Nat := min 1099511627776 (2305843009213693952 / max 1 (max va.natAbs vb.natAbs))
    some ⟨g.off L.e L.f, va.toInt64, vb.toInt64, (tmax : Int).toInt64⟩
  else none

/-- The fixed-point translation of the glyph at raw offset `T` (`|T| ≤ tmax`, so
`|va · T| ≤ 2⁶¹`): the base fraction plus `va · T`, carried into the integer part; the
rounding of the slopes adds at most `(|T| + 1)/2 + 1` units of `2⁻ᴷ` subpixel (`terr`). -/
def GTx.at? (g : GXf) (t : GTx) (T : Int) : Option GOff :=
  let T64 := T.toInt64
  if T64.toInt == T && T64.abs ≤ t.tmax then
    let wx := t.base.fx + t.va * T64
    let qx := fdiv64 wx g.one
    let wy := t.base.fy + t.vb * T64
    let qy := fdiv64 wy g.one
    some ⟨t.base.ex + qx.toInt, wx - qx * g.one, t.base.ey + qy.toInt, wy - qy * g.one,
      (T64.abs + 1) / 2 + 1⟩
  else none

/-- One device coordinate on the fixed-point path: `toSub` of `(ℓ_x·X + ℓ_y·Y)/(1 or 3) + ε`
when certified (see §3b), else `none`. `X`, `Y` must satisfy `|X|, |Y| ≤ gxPtCap`. -/
@[inline] def axisF (one half A C : Int64) (E : Int) (F terr : Int64) (X Y : Int64) (div3 : Bool) :
    Option Int :=
  let lin := A * X + C * Y
  let lin := if div3 then fdiv64 lin 3 else lin
  let t := lin + F + half
  let n := fdiv64 t one
  let r := t - n * one
  let err := (X.abs + Y.abs + 1) / 2 + 2 + terr
  if err ≤ r && r + err < one then some (E + n.toInt) else none

/-- A glyph-space point with raw coordinates `(X, Y)` (divided by 3 when `div3`) in subpixel
units clamped to `±lim`: the fixed-point path when certified, else `slow ()` (the exact
`Rat` value of the same point). -/
@[inline] def ptF (lim : Int) (g : GXf) (o : GOff) (X Y : Int) (div3 : Bool) (slow : Unit → FPt) :
    FPt :=
  let X64 := X.toInt64
  let Y64 := Y.toInt64
  if X64.toInt == X && Y64.toInt == Y && X64.abs ≤ 68719476736 && Y64.abs ≤ 68719476736 then
    let X := X64
    let Y := Y64
    match axisF g.one g.half g.a g.c o.ex o.fx o.terr X Y div3,
          axisF g.one g.half g.b g.d o.ey o.fy o.terr X Y div3 with
    | some u, some v => ⟨clampCoord u lim, clampCoord v lim⟩
    | _, _ => slow ()
  else slow ()

/-- The device current point of `segToD` from a glyph-space current point (`none`: the
device origin, `segToD`'s initial value). -/
def curD (mf : Unit → Aff) : Option Content.Point → Pt
  | some p => (mf ()).apply (ptOfPoint p)
  | none => ⟨0, 0⟩

/-- `segToD` on the fixed-point path: the current point is kept in glyph space; `mf` gives
the glyph's exact matrix for the `Rat` fallback. -/
def segToDF (lim : Int) (g : GXf) (o : GOff) (mf : Unit → Aff) (cur : Option Content.Point) :
    OSeg → DSeg × Option Content.Point
  | .moveTo p =>
    (.moveTo (ptF lim g o p.x.raw p.y.raw false fun _ => FPt.ofPt ((mf ()).apply (ptOfPoint p)) lim),
      some p)
  | .lineTo p =>
    (.lineTo (ptF lim g o p.x.raw p.y.raw false fun _ => FPt.ofPt ((mf ()).apply (ptOfPoint p)) lim),
      some p)
  | .quadTo c p =>
    let slowC1 := fun (_ : Unit) =>
      FPt.ofPt (twoThirds (curD mf cur) ((mf ()).apply (ptOfPoint c))) lim
    let c1 := match cur with
      | some p0 => ptF lim g o (p0.x.raw + 2 * c.x.raw) (p0.y.raw + 2 * c.y.raw) true slowC1
      | none => slowC1 ()
    let c2 := ptF lim g o (p.x.raw + 2 * c.x.raw) (p.y.raw + 2 * c.y.raw) true fun _ =>
      FPt.ofPt (twoThirds ((mf ()).apply (ptOfPoint p)) ((mf ()).apply (ptOfPoint c))) lim
    (.curveTo c1 c2
      (ptF lim g o p.x.raw p.y.raw false fun _ => FPt.ofPt ((mf ()).apply (ptOfPoint p)) lim),
      some p)
  | .curveTo c1 c2 p =>
    (.curveTo
      (ptF lim g o c1.x.raw c1.y.raw false fun _ => FPt.ofPt ((mf ()).apply (ptOfPoint c1)) lim)
      (ptF lim g o c2.x.raw c2.y.raw false fun _ => FPt.ofPt ((mf ()).apply (ptOfPoint c2)) lim)
      (ptF lim g o p.x.raw p.y.raw false fun _ => FPt.ofPt ((mf ()).apply (ptOfPoint p)) lim),
      some p)
  | .close => (.closePath, cur)

/-- `outlineToD` on the fixed-point path (same result: §3b, suite `raster-glyph-spec`). -/
def outlineToDF (lim : Int) (g : GXf) (o : GOff) (mf : Unit → Aff) (ol : Outline) : DPath :=
  (ol.1.foldl (fun (acc : DPath × Option Content.Point) s =>
    let r := segToDF lim g o mf acc.2 s
    (acc.1.push r.1, r.2)) (Array.mkEmpty ol.1.size, none)).1

private theorem foldl_segToDF_size (lim : Int) (g : GXf) (o : GOff) (mf : Unit → Aff)
    (l : List OSeg) :
    ∀ (acc : DPath × Option Content.Point), (l.foldl (fun (acc : DPath × Option Content.Point) s =>
      let r := segToDF lim g o mf acc.2 s
      (acc.1.push r.1, r.2)) acc).1.size = acc.1.size + l.length := by
  induction l with
  | nil => intro acc; simp
  | cons s rest ih =>
    intro acc
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]; simp only [Array.size_push]; omega

/-- **Size law** of the fixed-point path: as many device segments as outline segments. -/
theorem outlineToDF_size (lim : Int) (g : GXf) (o : GOff) (mf : Unit → Aff) (ol : Outline) :
    (outlineToDF lim g o mf ol).size = ol.1.size := by
  unfold outlineToDF
  rw [← Array.foldl_toList, foldl_segToDF_size]
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

/-- One step of `runPathSpec`: the glyph of a laid-out code appended to the run's path, every
point through the exact matrix (`outlineToD`). -/
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

/-- **Reference device path of a glyph run** (task 7.3a; the specification of `runPath`):
every laid-out code's glyph outline through its exact matrix
`FontMatrix × glyphPlacement × Tm × CTM × view`. -/
def runPathSpec (cfg : Fill.Config) (view : Aff) (fi : FontInfo) (fk : FontKey)
    (gs : GlyphSource) (r : GlyphRun) (cache : Cache) : DPath × Cache :=
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

/-- **Run bound** of the reference: at most `maxRunSegs` segments. -/
theorem runPathSpec_size_le (cfg : Fill.Config) (view : Aff) (fi : FontInfo) (fk : FontKey)
    (gs : GlyphSource) (r : GlyphRun) (cache : Cache) :
    (runPathSpec cfg view fi fk gs r cache).1.size ≤ maxRunSegs :=
  foldl_glyphStep_le _ _ _ _ _ _ _ (by simp [maxRunSegs])

/-- The fixed-point data of the last font matrix of a run: that matrix `F`, its `GXf` (if
any) and `L = F × glyphPlacement r 0 × rm` (the glyph matrix at offset 0). -/
abbrev XfMemo := Option (Aff × Option GXf × Aff × Option GTx)

/-- The `GXf` and `L` for font matrix `F` (from the memo when `F` is the memo's matrix). The
glyph at offset `tx` has matrix `L` with translation `(L.e + tx·rm.a, L.f + tx·rm.b)`: only
the translation of `glyphPlacement` depends on `tx`. -/
def glyphXf (r : GlyphRun) (rm F : Aff) (memo : XfMemo) : Option GXf × Aff × Option GTx :=
  let fresh := fun (_ : Unit) =>
    let L := F * glyphPlacement r Fixed.zero * rm
    let xf := GXf.ofAff? L
    (xf, L, xf.bind fun g => GTx.make? g L rm)
  match memo with
  | some (F', xf, L, t) => if F' = F then (xf, L, t) else fresh ()
  | .none => fresh ()

/-- One step of `runPath`: as `glyphStep`, through the fixed-point path (`outlineToDF`). -/
def glyphStepF (lim : Int) (fk : FontKey) (gs : GlyphSource) (r : GlyphRun) (rm : Aff)
    (acc : DPath × Cache × XfMemo) (e : List UInt8 × Fixed × Fixed) : DPath × Cache × XfMemo :=
  match gs.glyphOf e.1 with
  | .none => acc
  | some g =>
    match acc.2.1.outline fk gs g with
    | (.none, c) => (acc.1, c, acc.2.2)
    | (some o, c) =>
      let F := gs.matrix g
      let xl := glyphXf r rm F acc.2.2
      let mf := fun (_ : Unit) => F * glyphPlacement r e.2.1 * rm
      let d := match xl.1 with
        | some x =>
          let off := match xl.2.2.bind fun t => GTx.at? x t e.2.1.raw with
            | some off => off
            | .none =>
              let tx := Fixed.toRat e.2.1
              x.off (xl.2.1.e + tx * rm.a) (xl.2.1.f + tx * rm.b)
          outlineToDF lim x off mf o
        | .none => outlineToD lim (mf ()) o
      (addGlyph acc.1 d, c, some (F, xl.1, xl.2.1, xl.2.2))

/-- **The device path of a glyph run** through `view` (page → device pixels): every laid-out
code's glyph outline (positions from `Text.layoutParts` with the font's `FontInfo`), at most
`maxRunSegs` segments; and the updated cache. Points go through the fixed-point path (§3b);
the result equals `runPathSpec`'s (suite `raster-glyph-spec`). -/
def runPath (cfg : Fill.Config) (view : Aff) (fi : FontInfo) (fk : FontKey) (gs : GlyphSource)
    (r : GlyphRun) (cache : Cache) : DPath × Cache :=
  let entries := Text.layoutParts fi (Text.runTextState r) r.font.size Fixed.zero r.parts
  let rm := Aff.ofMatrix r.tm * Aff.ofMatrix r.ctm * view
  let res := entries.foldl (glyphStepF (cfg.coordLimit : Int) fk gs r rm) (#[], cache, .none)
  (res.1, res.2.1)

private theorem foldl_glyphStepF_le (lim : Int) (fk : FontKey) (gs : GlyphSource) (r : GlyphRun)
    (rm : Aff) (l : List (List UInt8 × Fixed × Fixed)) :
    ∀ (acc : DPath × Cache × XfMemo), acc.1.size ≤ maxRunSegs →
      (l.foldl (glyphStepF lim fk gs r rm) acc).1.size ≤ maxRunSegs := by
  induction l with
  | nil => intro acc h; exact h
  | cons e rest ih =>
    intro acc h
    simp only [List.foldl_cons]
    apply ih
    unfold glyphStepF
    split
    · exact h
    · split
      · exact h
      · exact addGlyph_size_le _ _ h

/-- **Run bound**: the device path of a run has at most `maxRunSegs` segments. -/
theorem runPath_size_le (cfg : Fill.Config) (view : Aff) (fi : FontInfo) (fk : FontKey)
    (gs : GlyphSource) (r : GlyphRun) (cache : Cache) :
    (runPath cfg view fi fk gs r cache).1.size ≤ maxRunSegs :=
  foldl_glyphStepF_le _ _ _ _ _ _ _ (by simp [maxRunSegs])

/-- Whether a render mode fills (0, 2, 4, 6). -/
def TextRenderMode.fills : TextRenderMode → Bool
  | .fill | .fillStroke | .fillClip | .fillStrokeClip => true
  | _ => false

/-- Whether a render mode strokes (1, 2, 5, 6). -/
def TextRenderMode.strokes : TextRenderMode → Bool
  | .stroke | .fillStroke | .strokeClip | .fillStrokeClip => true
  | _ => false

/-! ### Column groups (task 7.2h)

A glyph run is one nonzero fill (§4 of the module doc), but filling a whole text line at once
keeps hundreds of edges active on every sample row, and the filler's per-row crossing sort
(`Fill.sortAct`: insertion sort with a swap budget, then `mergeSort`) dominated text pages.
`columnGroups` splits the run's device path into groups of whole subpaths whose **pixel
columns** are disjoint (column `⌊x / 256⌋` of every point, control points included, so every
curve and chord stays inside): the subpaths' column intervals are merged by overlap (sorted by
left end); a subpath sharing a column with another is in its group. Filled separately, the
groups give the same coverage byte for every pixel as the whole path: on a sample row each
group's crossings come from closed polygons (net winding 0), so with nonzero the inside spans
of the whole path are exactly the union of the groups' spans, and each pixel column receives
spans from one group only; every other group's mask has coverage 0 there, which compositing
leaves untouched (`Clip.blendPx` with opacity 0). Pages are byte-identical with and without
the split (checked on the pdfTeX pages of 7.4). A path not starting with `moveTo` is not
split. Pattern-coloured fills are not split. -/

/-- Pixel column of a subpixel x coordinate. -/
def colOf (x : Int) : Int := x / 256

/-- Widen a column interval by a device point. -/
def widenCol (iv : Int × Int) (p : FPt) : Int × Int := (min iv.1 (colOf p.x), max iv.2 (colOf p.x))

/-- The subpath index of every segment and the column interval of every subpath (a new
subpath at each `moveTo`). -/
def subpathCols (dp : DPath) : Array Nat × Array (Int × Int) :=
  dp.foldl (fun (acc : Array Nat × Array (Int × Int)) s =>
    let (sid, ext) := acc
    match s with
    | .moveTo p => (sid.push ext.size, ext.push (colOf p.x, colOf p.x))
    | .lineTo p => (sid.push (ext.size - 1), ext.modify (ext.size - 1) (widenCol · p))
    | .curveTo c1 c2 p =>
      (sid.push (ext.size - 1), ext.modify (ext.size - 1) (fun iv => widenCol (widenCol (widenCol iv c1) c2) p))
    | .closePath => (sid.push (ext.size - 1), ext)) (#[], #[])

/-- Group ids of the subpaths: column intervals merged by overlap (in order of left end);
and the number of groups. -/
def colComponents (ext : Array (Int × Int)) : Array Nat × Nat :=
  let lo := fun (i : Nat) => (ext[i]?.getD (0, 0)).1
  let order := (Array.range ext.size).mergeSort (fun i j => lo i ≤ lo j)
  let r := order.foldl (fun (acc : Array Nat × Nat × Int) i =>
    let (comp, n, hi) := acc
    let iv := ext[i]?.getD (0, 0)
    if n = 0 || hi < iv.1 then (comp.setIfInBounds i n, n + 1, iv.2)
    else (comp.setIfInBounds i (n - 1), n, max hi iv.2)) (Array.replicate ext.size 0, 0, 0)
  (r.1, r.2.1)

/-- **Split a run's device path into column-disjoint groups** of whole subpaths (segment
order kept within each group); `#[dp]` when the path does not start with `moveTo`. -/
def columnGroups (dp : DPath) : Array DPath :=
  match dp[0]? with
  | some (DSeg.moveTo _) =>
    let (sid, ext) := subpathCols dp
    let (comp, n) := colComponents ext
    if n ≤ 1 then #[dp] else
    (dp.zip sid).foldl (fun (gs : Array DPath) (s, k) =>
      gs.modify (comp[k]?.getD 0) (·.push s)) (Array.replicate n #[])
  | _ => #[dp]

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
        let groups :=
          if (pf.shadings.patternOf r.fill.color r.fill.pattern).isNone then columnGroups dp
          else #[dp]
        groups.toList.map fun g =>
          let f := fillEdgesCounted (flatten cfg win g) .nonzero win cfg
          (f.1, r.fill.color, r.fill.alpha, f.2)
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

/-- Paint a list of masks through one clip (cache and work of `clipMaskC` charged once). A
mask whose colour is a pattern colour that `look` resolves to a loaded shading pattern (task
7.3f: pattern-coloured text) is painted with the pattern through mask ∩ clip
(`Shading.paintPattern`); every other mask with its flat colour. -/
def paintAll (cfg : Fill.Config) (m : Aff) (W H : Nat)
    (look : Color → Option (Shading.Pattern × Matrix)) (cm : Option Mask) (cc : Clip.ClipCache)
    (s : Nat) (st : Clip.RState) : List (Mask × Color × Comp × Nat) → Clip.RState
  | [] => { st with cache := cc, steps := st.steps + s }
  | (mk, col, a, w) :: rest =>
    let st' := match look col with
      | some (pat, base) => Shading.paintPattern cfg m W H st pat base (Clip.combine mk cm) a cc (s + w)
      | none => Clip.paintMask W H st cm mk col a cc (s + w)
    paintAll cfg m W H look cm cc 0 st' rest

/-- The shading pattern a glyph-run mask colour denotes: the fill's pattern use for the fill
colour, else the stroke's. -/
def runPattern (tbl : Shading.ShadingTable) (r : GlyphRun) (c : Color) :
    Option (Shading.Pattern × Matrix) :=
  tbl.patternOf c (if c = r.fill.color then r.fill.pattern else r.stroke.pattern)

/-- Render one display item: glyph runs here, images (7.3b), shadings and pattern fills and
strokes (7.3d, 7.3f), everything else by `Clip.renderItem`. -/
def renderItemG (cfg : Fill.Config) (m : Aff) (W H : Nat) (stroke : Clip.StrokeFn) (pf : PageFonts)
    (st : TState) : DisplayItem → TState
  | .glyphRun r clip =>
    if !r.renderMode.paints then st else
    let c := Clip.clipMaskC cfg m W H st.rs.cache clip
    let (ms, cache) := runMasks cfg m (Clip.itemWindow W H c.1) pf st.cache r
    { st with rs := paintAll cfg m W H (runPattern pf.shadings r) c.1 c.2.1 c.2.2 st.rs ms, cache }
  | .image src ctm fill clip => { st with rs := Image.renderImage cfg m W H pf.images st.rs src ctm fill clip }
  | .shading name r ctm fill clip =>
    { st with rs := Shading.renderShading cfg m W H pf.shadings st.rs r name ctm fill.alpha clip }
  | .fillPath p rule style clip => { st with rs := Shading.renderFill cfg m W H pf.shadings st.rs p rule style clip }
  | .strokePath p style clip =>
    { st with rs := Shading.renderStroke cfg m W H stroke pf.shadings st.rs p style clip }
  | it => { st with rs := Clip.renderItem cfg m W H stroke st.rs it }

/-- `paintAll` preserves the buffer size. -/
theorem paintAll_size (cfg : Fill.Config) (m : Aff) (W H : Nat)
    (look : Color → Option (Shading.Pattern × Matrix)) (cm : Option Mask) (cc : Clip.ClipCache) :
    ∀ (s : Nat) (st : Clip.RState) (l : List (Mask × Color × Comp × Nat)),
      (paintAll cfg m W H look cm cc s st l).buf.size = st.buf.size
  | _, _, [] => rfl
  | s, st, (mk, col, a, w) :: rest => by
    simp only [paintAll]
    rw [paintAll_size cfg m W H look cm cc 0 _ rest]
    split
    · exact Shading.paintPattern_size _ _ _ _ _ _ _ _ _ _ _
    · simp only [Clip.paintMask, Clip.composite_size]

/-- One item preserves the buffer size. -/
theorem renderItemG_size (cfg : Fill.Config) (m : Aff) (W H : Nat) (stroke : Clip.StrokeFn)
    (pf : PageFonts) (st : TState) (it : DisplayItem) :
    (renderItemG cfg m W H stroke pf st it).rs.buf.size = st.rs.buf.size := by
  cases it with
  | glyphRun r clip =>
    simp only [renderItemG]
    split
    · rfl
    · exact paintAll_size _ _ _ _ _ _ _ _ _ _
  | image src ctm fill clip => simp only [renderItemG]; exact Image.renderImage_size _ _ _ _ _ _ _ _ _ _
  | shading name r ctm fill clip =>
    simp only [renderItemG]; exact Shading.renderShading_size _ _ _ _ _ _ _ _ _ _ _
  | fillPath p rule style clip => simp only [renderItemG]; exact Shading.renderFill_size _ _ _ _ _ _ _ _ _ _
  | strokePath p style clip =>
    simp only [renderItemG]; exact Shading.renderStroke_size _ _ _ _ _ _ _ _ _ _
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
  bound := fun it => some (Clip.itemBound cfg m W H it)

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

/-- The items an `sh` item is painted as (task 7.3f): with `Normal` blending and no soft mask,
itself; otherwise bracketed by a non-isolated, non-knockout transparency group of alpha 1
carrying the item's blend mode and soft mask, the item inside painted plainly with its `ca`.
The transparency driver composites that group exactly as it composites a fill with that
blend mode and soft mask (`Transparency.beginGroup` and `itemFx` both open one layer with the
same effect), since `Transparency.itemFx` does not look at `sh` items. -/
def liftShItem : DisplayItem → List DisplayItem
  | .shading n r ctm f clip =>
    if f.blend = .normal ∧ f.smask.isNone then [.shading n r ctm f clip]
    else [.groupBegin { blend := f.blend, smask := f.smask },
          .shading n r ctm { f with blend := .normal, smask := none } clip, .groupEnd]
  | it => [it]

/-- Apply `liftShItem` to a display list and, up to `fuel` levels, inside soft masks. -/
def liftSh : Nat → DisplayList → DisplayList
  | 0, items => items.foldl (fun acc it => Interp.pushAll acc (liftShItem it)) #[]
  | k + 1, items => items.foldl (fun acc it =>
      match it with
      | .softMask id info inner => acc.push (.softMask id info (liftSh k inner))
      | it => Interp.pushAll acc (liftShItem it)) #[]

/-- Render a display list (paths and glyph runs) onto a white `W × H` page through `m`. -/
def renderItems (cfg : Fill.Config) (m : Aff) (W H : Nat) (pf : PageFonts) (items : DisplayList)
    (stroke : Clip.StrokeFn := Clip.defaultStroke) : TState :=
  (liftSh Transparency.maxMaskDepth items).foldl (Transparency.renderTx (painterG cfg m W H stroke pf) W H Transparency.maxMaskDepth)
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
  exact Transparency.renderTx_items_size _ (painterG_lawful ..) _ _ _ (liftSh Transparency.maxMaskDepth items) _
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
    -- Annotation appearance streams (task 8.3), drawn after the page content in MuPDF order.
    -- They get their own op/form budget (the page run's counts are not exposed by `PageText`).
    let (ap, b) := Annot.docAnnots limits doc page pt.fonts
      { ops := limits.maxOpsPerPage, forms := limits.maxFormsPerPage } b
    let items := pt.items ++ ap.items
    let (srcs, b) := loadSources limits (Text.docSource limits doc) b (page.resources.getD [])
    let (srcs, b) := ap.roots.foldl (fun (acc : SourceTable × Filter.Budget) r =>
      let (t, b) := loadSources limits (Text.docSource limits doc) acc.2 r.2; (acc.1 ++ t, b)) (srcs, b)
    let (imgs, b) := Image.loadImages limits (Text.docSource limits doc) b (page.resources.getD []) items
    let (shs, b) := Shading.loadShadings limits (Text.docSource limits doc) b (page.resources.getD []) items
    (.ok (renderPage page zoom rot ⟨ap.fonts, srcs, imgs, shs⟩ items cfg), b)

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

private def shStyled (b : BlendMode) : DisplayItem :=
  .shading (Name.ofString "S") .page Matrix.identity
    { color := .gray Comp.zero, alpha := Comp.one, blend := b } []
#guard (liftSh 1 #[shStyled .multiply]).toList.map DisplayItem.kind ==
  ["groupBegin", "shading", "groupEnd"]
#guard (liftSh 1 #[shStyled .normal]).toList.map DisplayItem.kind == ["shading"]
#guard (match (liftSh 1 #[.softMask 0 { kind := .alpha } #[shStyled .screen]]).toList with
  | [.softMask _ _ inner] => inner.size == 3
  | _ => false)
end SafePdf.Core.Raster.Glyph
