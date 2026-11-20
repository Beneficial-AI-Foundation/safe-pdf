import SafePdf.Core.Raster.Tiling
import Tests.RasterGlyph

/-!
# Tiling pattern suite (task 7.3g)

Plan.md §6 Phase 7 (patterns), ISO 32000-2 §8.7.3. Buffer-size preservation is a theorem in
`SafePdf.Core.Raster.Tiling`; this suite checks behaviour by evaluation, loading pattern
streams from an in-memory source through `loadTilings` (the cell content runs through
`Run.runOps`) and painting with `renderTilingFill` and the path-only cell painter:

* a coloured checkerboard cell (red and blue quarters, transparent elsewhere) filling a
  rectangle: exact pixel colours in several tiles, gaps show the page;
* an uncoloured pattern (its own `rg` ignored) painted in two different colours;
* `/XStep` larger than the `/BBox`: gaps between tiles;
* a pattern matrix rotated by 90° (exact pixels) and by 30° (coverage ≈ ½);
* the fill alpha and a clip;
* the shared operator budget is charged by the cell's operators;
* the tile-count cap: a 2-pixel cell over a 2100 × 2100 page exceeds `maxTiles` and is
  painted with the cell's mean colour;
* timing of a full-page 612 × 792 fill with an 8 × 8 cell (printed).
-/

namespace SafePdf.Tests.RasterTiling

open SafePdf SafePdf.Core
open SafePdf.Core.Raster.Geom
open SafePdf.Core.Raster.Tiling
open SafePdf.Core.Content (Fixed Comp Color Clip ClipPath DisplayItem DisplayList Path Matrix
  FillStyle Source FillRule Env)
open SafePdf.Core.Raster

/-- A name. -/
def nm (s : String) : Name := Name.ofString s

/-- An object source over an in-memory table; stream data is used as is (no filters). -/
def memSource (objs : List (Nat × IndirectBody)) : Source Unit :=
  ⟨fun s n _ => match objs.find? (·.1 == n) with
     | some (_, b) => (.ok b, s)
     | none => (.error (.malformed 0 "missing"), s),
   fun s _ st => (.ok st.data, s)⟩

/-- View of a `W × H` page at zoom 1 (y flipped, origin top-left). -/
def view (W H : Nat) : Aff := viewMatrix 1 .r0 ⟨0, 0, W, H⟩

/-- A number array. -/
def nums (l : List Int) : PdfObject := .array (l.map PdfObject.int)

/-- A tiling pattern stream. -/
def patStream (paint : Int) (bbox : List Int) (xs ys : Int) (content : String)
    (mat : List Int := [1, 0, 0, 1, 0, 0]) : IndirectBody :=
  .stream ⟨[(nm "Type", .name (nm "Pattern")), (nm "PatternType", .int 1),
    (nm "PaintType", .int paint), (nm "TilingType", .int 1), (nm "BBox", nums bbox),
    (nm "XStep", .int xs), (nm "YStep", .int ys), (nm "Matrix", nums mat)], content.toUTF8⟩

/-- A pattern stream with a rational matrix (`mat` in millionths). -/
def patStreamQ (bbox : List Int) (xs ys : Int) (content : String) (mat : List Int) : IndirectBody :=
  .stream ⟨[(nm "PatternType", .int 1), (nm "PaintType", .int 1), (nm "TilingType", .int 1),
    (nm "BBox", nums bbox), (nm "XStep", .int xs), (nm "YStep", .int ys),
    (nm "Matrix", .array (mat.map fun v => PdfObject.real ⟨v, 6⟩))], content.toUTF8⟩

/-- Resources with pattern `P` = object 5. -/
def res : Dict := [(nm "Pattern", .dict [(nm "P", .ref 5 0)])]

/-- Rectangle path in page space. -/
def rect (x0 y0 x1 y1 : Int) : Path :=
  ⟨#[.moveTo ⟨Fixed.ofInt x0, Fixed.ofInt y0⟩, .lineTo ⟨Fixed.ofInt x1, Fixed.ofInt y0⟩,
    .lineTo ⟨Fixed.ofInt x1, Fixed.ofInt y1⟩, .lineTo ⟨Fixed.ofInt x0, Fixed.ofInt y1⟩, .closePath]⟩

/-- A fill of `p` with pattern `P`. -/
def patFill (p : Path) (alpha : Comp := Comp.one) (clip : Clip := []) : DisplayItem :=
  .fillPath p .nonzero { color := .pattern (nm "P"), alpha } clip

/-- The runner environment of the tests. -/
def env (objs : List (Nat × IndirectBody)) : Env Unit Unit :=
  { cfg := {}, src := memSource objs, observe := fun u _ _ _ => u }

/-- The initial budget. -/
def bud0 : Budget := { ops := 1000000, forms := 1000 }

/-- Load the pattern table for `items`. -/
def load (objs : List (Nat × IndirectBody)) (items : List DisplayItem) : TilingTable :=
  (loadTilings (env objs) () () bud0 res items.toArray).1

/-- Render pattern fills (with PaintType 2 colours `cols`, one per item) onto a white page. -/
def render (W H : Nat) (tbl : TilingTable) (items : List (DisplayItem × Color)) : Clip.Image :=
  let st := items.foldl (fun st (it, col) =>
    match it with
    | .fillPath p r s cl =>
      match s.color with
      | .pattern n =>
        match tbl.get? .page n with
        | some pat => renderTilingFill {} (pathPainter {}) (view W H) W H st pat
            (Aff.ofMatrix pat.matrix) col p r s.alpha cl
        | none => st
      | _ => st
    | _ => st) ({ buf := Clip.whiteBuf W H } : Clip.RState)
  ⟨W, H, st.buf⟩

/-- Load and render one pattern object over the given fills. -/
def renderPat (W H : Nat) (o : IndirectBody) (items : List (DisplayItem × Color)) : Clip.Image :=
  render W H (load [(5, o)] (items.map (·.1))) items

/-- RGB of pixel `(x, y)`. -/
def px (img : Clip.Image) (x y : Nat) : Nat × Nat × Nat :=
  let i := 4 * (y * img.w + x)
  (Clip.getB img.data i, Clip.getB img.data (i + 1), Clip.getB img.data (i + 2))

/-- `|a − b| ≤ tol`. -/
def near (a b tol : Nat) : Bool := a ≤ b + tol && b ≤ a + tol

/-- Colour constants. -/
def red : Nat × Nat × Nat := (255, 0, 0)
/-- Blue. -/
def blue : Nat × Nat × Nat := (0, 0, 255)
/-- White. -/
def white : Nat × Nat × Nat := (255, 255, 255)
/-- Black. -/
def black : Nat × Nat × Nat := (0, 0, 0)

/-- An RGB device colour from integers in `[0, 1]`. -/
def rgb (r g b : Int) : Color :=
  .rgb (Comp.ofFixed (Fixed.ofInt r)) (Comp.ofFixed (Fixed.ofInt g)) (Comp.ofFixed (Fixed.ofInt b))

/-- Check a list of `(x, y, expected)` pixels; returns the failures and reports them. -/
def checkPx (name : String) (img : Clip.Image) (l : List (Nat × Nat × (Nat × Nat × Nat))) :
    IO Nat := do
  let mut f := 0
  for (x, y, c) in l do
    if px img x y != c then
      f := f + 1
      IO.println s!"  FAIL {name}: pixel ({x}, {y}) = {px img x y}, expected {c}"
  return f

/-! ## End-to-end pages (task 7.3h1)

Hand-built 200 × 200 PDFs through `Raster.Glyph.renderDocPage` (patterns loaded by
`Tiling.loadTilings` from the page's and forms' resources, painted by `Glyph.renderItemG`
with the path-only cell painter). The PDFs are committed under `Tests/golden/raster-tiling/`
for the pixel comparator against MuPDF
(`python3 -I Tests/differential/run.py --comparator pixels --files 'Tests/golden/raster-tiling/*.pdf'`);
the suite fails when a committed file differs from the generated bytes
(`SAFEPDF_GOLDEN_UPDATE=1` rewrites them). -/

/-- Directory of the committed fixtures. -/
def pdfDir : System.FilePath := "Tests/golden/raster-tiling"

/-- A tiling pattern stream object (PDF syntax). -/
def patObj (paint : Nat) (bbox : String) (step : Nat) (content : String) (extra : String := "") :
    String :=
  SafePdf.Tests.CFFText.strmObj
    s!"/Type /Pattern /PatternType 1 /PaintType {paint} /TilingType 1 /BBox [{bbox}] /XStep {step} /YStep {step} {extra}"
    content

/-- An 8 × 8 checker cell: red `[0,4]²`, blue `[4,8]²`, the rest transparent. -/
def checkerObj : String := patObj 1 "0 0 8 8" 8 "1 0 0 rg 0 0 4 4 re f 0 0 1 rg 4 4 4 4 re f"

/-- The end-to-end fixtures: name and PDF bytes. -/
def docCases : List (String × ByteArray) :=
  let rp := RasterGlyph.resPage
  [ -- hatching: blue diagonal lines in a 10-unit coloured cell, filling [20, 180]².
    ("tiling-hatch", rp "<< /Pattern << /P0 5 0 R >> >>"
      "1 0 0 RG /Pattern cs /P0 scn 20 20 160 160 re f"
      [patObj 1 "0 0 10 10" 10 "0 0 1 RG 1 w 0 0 m 10 10 l S -5 5 m 5 15 l S 5 -5 m 15 5 l S"]),
    -- uncoloured pattern (its own green ignored), red `scn` operands, inside a form scaled
    -- ×2 by its /Matrix and translated by the page's `cm`: 20-unit page cells from (20, 20),
    -- a red 10 × 10 square in each, the fill covering page [20, 140]².
    ("tiling-uncoloured-form", rp "<< /XObject << /Fm 5 0 R >> >>" "q 1 0 0 1 20 20 cm /Fm Do Q"
      [SafePdf.Tests.CFFText.strmObj
        ("/Type /XObject /Subtype /Form /BBox [0 0 100 100] /Matrix [2 0 0 2 0 0] " ++
         "/Resources << /Pattern << /P1 6 0 R >> /ColorSpace << /Cs [/Pattern /DeviceRGB] >> >>")
        "/Cs cs 1 0 0 /P1 scn 0 0 60 60 re f",
       patObj 2 "0 0 10 10" 10 "0 1 0 rg 0 0 5 5 re f"]),
    -- the checker under a clip to [40, 120] × [40, 120].
    ("tiling-clip", rp "<< /Pattern << /P0 5 0 R >> >>"
      "40 40 80 80 re W n /Pattern cs /P0 scn 0 0 200 200 re f" [checkerObj]),
    -- the checker with fill alpha 0.5.
    ("tiling-alpha", rp "<< /Pattern << /P0 5 0 R >> /ExtGState << /G 6 0 R >> >>"
      "/G gs /Pattern cs /P0 scn 20 20 160 160 re f" [checkerObj, "<< /Type /ExtGState /ca 0.5 >>"]) ]

/-- Colour classes of a page: (red, blue, other non-white) pixel counts. -/
def classes (img : Clip.Image) : Nat × Nat × Nat := Id.run do
  let mut r := 0
  let mut b := 0
  let mut o := 0
  for i in [0:img.w * img.h] do
    let p := RasterGlyph.pxAt img (i % img.w) (i / img.w)
    if p.1 > 200 && p.2.1 < 60 && p.2.2 < 60 then r := r + 1
    else if p.2.2 > 200 && p.1 < 60 && p.2.1 < 60 then b := b + 1
    else if p != (255, 255, 255) then o := o + 1
  return (r, b, o)

/-- The checks of the end-to-end fixtures (device y = 199 − page y at pixel centres). -/
def docChecks : List (String × (Clip.Image → Bool)) :=
  let px := RasterGlyph.pxAt
  let wh : Nat × Nat × Nat := (255, 255, 255)
  let rd : Nat × Nat × Nat := (255, 0, 0)
  let bl : Nat × Nat × Nat := (0, 0, 255)
  [ -- blue hatching only inside the rectangle (≈ √2 px² of line per 10 × 10 cell: ≈ 14% ink,
    -- ≈ 3620 of 25600 px, `ink` in red-channel units), never red (the page `RG` is not the
    -- fill colour).
    ("tiling-hatch", fun img =>
      let (r, b, _) := classes img
      r == 0 && 1000 < b && RasterGlyph.near (RasterGlyph.ink img) (3620 * 255) 10 &&
      px img 10 10 == wh && px img 190 100 == wh &&
      px img 100 10 == wh),
    -- red 10 × 10 squares at page [20 + 20i, 30 + 20i]², i < 6: exactly 3600 red pixels.
    ("tiling-uncoloured-form", fun img =>
      px img 25 174 == rd && px img 35 174 == wh && px img 25 164 == wh && px img 45 174 == rd &&
      px img 10 174 == wh && px img 145 54 == wh && (classes img) == (3600, 0, 0)),
    -- 80 × 80 clip: 100 red and 100 blue 4 × 4 squares, nothing outside.
    ("tiling-clip", fun img =>
      px img 41 158 == rd && px img 45 154 == bl && px img 41 154 == wh && px img 38 158 == wh &&
      classes img == (1600, 1600, 0)),
    -- alpha 0.5 (cells start at the page origin: page [20, 24]² is a blue quarter, [24, 28]²
    -- red): red → (255, 127, 127), blue → (127, 127, 255).
    ("tiling-alpha", fun img =>
      px img 21 178 == (127, 127, 255) && px img 25 174 == (255, 127, 127) &&
      px img 25 178 == wh && px img 10 10 == wh) ]

/-- Run the end-to-end checks; the number of failures. -/
def runDoc : IO Nat := do
  let mut failures := 0
  let update := (← IO.getEnv "SAFEPDF_GOLDEN_UPDATE").isSome
  let ppmDir ← IO.getEnv "SAFEPDF_PPM_DIR"
  for (name, pdf) in docCases do
    let path := pdfDir / s!"{name}.pdf"
    if update then
      IO.FS.createDirAll pdfDir
      IO.FS.writeBinFile path pdf
    else if !(← path.pathExists) || (← IO.FS.readBinFile path).toList != pdf.toList then
      failures := failures + 1
      IO.println s!"  FAIL {name}: {path} missing or stale (SAFEPDF_GOLDEN_UPDATE=1)"
    let t0 ← IO.monoMsNow
    match RasterGlyph.render pdf with
    | none => failures := failures + 1; IO.println s!"  FAIL {name}: render failed"
    | some img =>
      let t1 ← IO.monoMsNow
      let ok := match docChecks.find? (·.1 == name) with
        | some (_, f) => f img
        | none => false
      IO.println s!"  raster-tiling {name}: {t1 - t0} ms, (red, blue, other) {classes img}"
      if !ok then
        failures := failures + 1; IO.println s!"  FAIL {name}: (red, blue, other) {classes img}"
      if let some dir := ppmDir then
        IO.FS.createDirAll dir
        RasterGlyph.writePpm (System.FilePath.mk dir / s!"{name}.ppm") img
  return failures

/-- Run the suite; returns the number of failures. -/
def run : IO Nat := do
  let mut failures := 0
  let none' : Color := .gray Comp.zero
  -- 1. Coloured checkerboard: 8 × 8 cell, red [0,4]², blue [4,8]², rest transparent.
  -- Page 32 × 32, device y = 32 − page y.
  let checker := patStream 1 [0, 0, 8, 8] 8 8 "1 0 0 rg 0 0 4 4 re f 0 0 1 rg 4 4 4 4 re f"
  let c1 := renderPat 32 32 checker [(patFill (rect 0 0 32 32), none')]
  failures := failures + (← checkPx "checker" c1
    [(1, 30, red), (5, 26, blue), (1, 26, white), (5, 30, white), (9, 30, red), (13, 26, blue),
     (25, 22, red), (29, 2, blue), (31, 0, blue), (0, 31, red)])
  -- 2. Uncoloured: its own `rg` is ignored; two fills in red and blue.
  let unc := patStream 2 [0, 0, 8, 8] 8 8 "0 1 0 rg 0 0 4 4 re f"
  let c2 := renderPat 32 32 unc [(patFill (rect 0 0 16 32), rgb 1 0 0),
    (patFill (rect 16 0 32 32), rgb 0 0 1)]
  failures := failures + (← checkPx "uncoloured" c2
    [(1, 30, red), (9, 30, red), (17, 30, blue), (25, 22, blue), (5, 30, white), (21, 26, white)])
  -- 3. XStep/YStep larger than the BBox: 4 × 4 cells every 8 units.
  let gap := patStream 1 [0, 0, 4, 4] 8 8 "0 0 4 4 re f"
  let c3 := renderPat 32 32 gap [(patFill (rect 0 0 32 32), none')]
  failures := failures + (← checkPx "gaps" c3
    [(1, 30, black), (5, 30, white), (9, 30, black), (1, 26, white), (1, 22, black),
     (13, 18, white), (17, 14, black)])
  -- 3b. Content outside the BBox is clipped: a 4 × 4 BBox with an 8 × 8 black square.
  let over := patStream 1 [0, 0, 4, 4] 8 8 "0 0 8 8 re f"
  let c3b := renderPat 32 32 over [(patFill (rect 0 0 32 32), none')]
  failures := failures + (← checkPx "bbox clip" c3b [(1, 30, black), (5, 30, white), (5, 26, white)])
  -- 4. Rotated by 90°: `[0 1 −1 0 0 0]` maps (u, v) ↦ (−v, u); vertical stripes (u ∈ [0, 4])
  -- become horizontal bands (page y mod 8 ∈ [0, 4]).
  let stripes := patStream 1 [0, 0, 8, 8] 8 8 "1 0 0 rg 0 0 4 8 re f" [0, 1, -1, 0, 0, 0]
  let c4 := renderPat 32 32 stripes [(patFill (rect 0 0 32 32), none')]
  failures := failures + (← checkPx "rot90" c4
    [(1, 30, red), (13, 30, red), (30, 29, red), (1, 26, white), (20, 25, white), (7, 22, red),
     (7, 18, white)])
  -- 4b. Rotated by 30°: half of the area is red (anti-aliased edges): mean red coverage.
  let rot30 := patStreamQ [0, 0, 8, 8] 8 8 "1 0 0 rg 0 0 4 8 re f"
    [866025, 500000, -500000, 866025, 0, 0]
  let c4b := renderPat 64 64 rot30 [(patFill (rect 0 0 64 64), none')]
  let gsum := (List.range (64 * 64)).foldl (fun s i => s + Clip.getB c4b.data (4 * i + 1)) 0
  -- green byte: 0 under red, 255 on white → mean ≈ 127.5
  let gmean := gsum / (64 * 64)
  if !near gmean 128 6 then
    failures := failures + 1; IO.println s!"  FAIL rot30: mean green {gmean}"
  -- 5. Fill alpha 0.5 and a clip to x < 8.
  let half : Comp := Comp.ofFixed (Fixed.clamp 500000)
  let c5 := renderPat 32 32 checker
    [(patFill (rect 0 0 32 32) half [⟨rect 0 0 8 32, .nonzero⟩], none')]
  failures := failures + (← checkPx "alpha+clip" c5
    [(1, 30, (255, 127, 127)), (5, 26, (127, 127, 255)), (9, 30, white), (5, 30, white)])
  -- 6. The shared budget is charged by the cell's operators (`rg re f` × 2 = 6).
  let t6 := load [(5, checker)] [patFill (rect 0 0 32 32)]
  if t6.budget.ops != bud0.ops - 6 then
    failures := failures + 1; IO.println s!"  FAIL budget: {t6.budget.ops}"
  -- 6b. Not a tiling pattern (shading pattern, PatternType 2) → not loaded.
  let t6b := load [(5, .stream ⟨[(nm "PatternType", .int 2)], ByteArray.empty⟩)]
    [patFill (rect 0 0 32 32)]
  if (t6b.get? .page (nm "P")).isSome then
    failures := failures + 1; IO.println "  FAIL shading pattern loaded as tiling"
  -- 6c. An exhausted budget leaves an empty cell (nothing painted).
  let t6c := (loadTilings (env [(5, checker)]) () () { ops := 0, forms := 0 } res
    #[patFill (rect 0 0 32 32)]).1
  let c6c := render 32 32 t6c [(patFill (rect 0 0 32 32), none')]
  failures := failures + (← checkPx "no budget" c6c [(1, 30, white)])
  -- 7. Tile-count cap: a 2 × 2 cell with a red 1 × 1 quarter over a 2100 × 2100 page has
  -- ≈ 1.1 M instances > maxTiles: painted with the mean colour (red at ¼ opacity) everywhere.
  let tiny := patStream 1 [0, 0, 2, 2] 2 2 "1 0 0 rg 0 0 1 1 re f"
  let c7 := renderPat 2100 2100 tiny [(patFill (rect 0 0 2100 2100), none')]
  let p7a := px c7 0 2099
  let p7b := px c7 1 2098
  if p7a != p7b || !near p7a.2.1 191 1 || p7a.1 != 255 then
    failures := failures + 1; IO.println s!"  FAIL tile cap: {p7a} {p7b}"
  -- 7b. Below the cap the same cell blits exactly (200 × 200 page).
  let c7b := renderPat 200 200 tiny [(patFill (rect 0 0 200 200), none')]
  failures := failures + (← checkPx "tiny blit" c7b [(0, 199, red), (1, 198, white), (2, 199, red)])
  -- 8. Timing: full 612 × 792 page with the 8 × 8 checker.
  let t0 ← IO.monoMsNow
  let c8 := renderPat 612 792 checker [(patFill (rect 0 0 612 792), none')]
  let v := px c8 1 790
  let t1 ← IO.monoMsNow
  IO.println s!"  raster-tiling: 612×792 checker fill {t1 - t0} ms ({v})"
  if v != red then
    failures := failures + 1; IO.println s!"  FAIL full page: {v}"
  if let some dir ← IO.getEnv "SAFEPDF_PPM_DIR" then
    IO.FS.createDirAll dir
    for (name, img) in [("checker", c1), ("uncoloured", c2), ("gaps", c3), ("rot90", c4),
        ("rot30", c4b)] do
      let mut rgbB := ByteArray.empty
      for i in [0:img.w * img.h] do
        rgbB := rgbB.push (UInt8.ofNat (Clip.getB img.data (4 * i)))
        rgbB := rgbB.push (UInt8.ofNat (Clip.getB img.data (4 * i + 1)))
        rgbB := rgbB.push (UInt8.ofNat (Clip.getB img.data (4 * i + 2)))
      IO.FS.writeBinFile (System.FilePath.mk dir / s!"tiling-{name}.ppm")
        (s!"P6\n{img.w} {img.h}\n255\n".toUTF8 ++ rgbB)
  -- 9. Patterns in soft masks and in forms are found (`foldDeep`, keyed by `ResRef`).
  let t9 := (loadTilings (env [(5, checker), (7, .stream ⟨[(nm "Resources", .dict res)], ByteArray.empty⟩)])
    () () bud0 [] #[.softMask 0 { kind := .alpha }
      #[.fillPath (rect 0 0 8 8) .nonzero
        { color := .pattern (nm "P"), alpha := Comp.one, pattern := some { res := .form 7 0 } } []]]).1
  if (t9.get? (.form 7 0) (nm "P")).isNone || (t9.get? .page (nm "P")).isSome then
    failures := failures + 1; IO.println "  FAIL pattern in a soft mask / form not loaded"
  -- 10. End-to-end pages (task 7.3h1).
  failures := failures + (← runDoc)
  return failures

end SafePdf.Tests.RasterTiling
