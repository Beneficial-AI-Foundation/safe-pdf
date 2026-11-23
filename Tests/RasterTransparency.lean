import SafePdf.Core.Raster.Transparency
import SafePdf.Core.Content.Run
import Tests.RasterGlyph

/-!
# Transparency suite (task 7.3c)

Plan.md §6 Phase 7 (soft masks, transparency groups), ISO 32000-2 §11. The byte bounds and
buffer sizes are theorems in `SafePdf.Core.Raster.Transparency`; this suite checks behaviour:

* every separable blend mode on a 16 × 16 grid of byte pairs against the §11.3.5 formulas
  evaluated in floating point (`round(255 · B(cb/255, cs/255))`), within one byte (exact for
  `Normal`, `Darken`, `Lighten`, `Difference`), plus known pixel pairs;
* the neutral source value of each separable mode leaves the backdrop unchanged (± 1);
* non-separable modes on known pairs (`Luminosity` keeps the backdrop's hue and takes the
  source's luminosity, …) and against a floating-point reference;
* a group with alpha 0.5 holding two overlapping black squares is composited **once**: the
  overlap is 50 % grey like the rest (items with alpha 0.5 each would darken it to 25 %);
* a luminosity soft mask from a pattern of filled grey stripes (no shadings yet) modulates a
  black fill stripe by stripe; outside the mask's `/BBox` the backdrop `/BC` (black) masks
  everything out; an alpha soft mask from a half-transparent square;
* item blend modes (`Multiply`, `Screen`) and a `Multiply` group;
* knockout groups (task 7.3i): in a `/K true` group the second of two overlapping translucent
  squares replaces the first in the overlap (blue at 50 % over white, not over black), also
  after an opaque square, and with the group at alpha 0.5; without `/K` the overlap darkens;
  `b` with `CA 0.5` through the runner: a knockout group, the stroke over the fill shows the
  page, not the fill (an opaque stroke gets no group; stroke alpha 0 gets none and paints
  nothing; an opaque `Multiply` stroke gets a group carrying the blend mode, with `Normal`
  items, so it multiplies the page, not the fill); fill+stroke text (`2 Tr`, `CA 0.5`) never
  shows the stroke over the fill;
* layer nesting beyond `maxLayerDepth` keeps the buffer size;
* end to end: a content stream with an ExtGState soft mask and a transparency-group form
  through `Content.runBytes` and the driver;
* timing: a 612 × 792 page with a group of 100 squares at alpha 0.5 (printed).

Image `/SMask` (an image's own soft mask) belongs to the image decoder (task 7.3e) and is
not tested here.
-/

namespace SafePdf.Tests.RasterTransparency

open SafePdf.Core
open SafePdf.Core.Raster.Geom
open SafePdf.Core.Raster.Fill
open SafePdf.Core.Raster.Clip
open SafePdf.Core.Raster.Transparency
open SafePdf.Core.Content (FillRule Clip Color Comp DisplayItem DisplayList Path BlendMode
  GroupInfo SoftMaskInfo FillStyle)

/-! ## Floating-point reference (§11.3.5) -/

/-- `B(cb, cs)` of a separable mode over `[0, 1]`. -/
def refB (m : BlendMode) (b s : Float) : Float :=
  let hard (b s : Float) : Float := if s ≤ 0.5 then b * (2 * s) else
    let t := 2 * s - 1
    b + t - b * t
  match m with
  | .normal => s
  | .multiply => b * s
  | .screen => b + s - b * s
  | .overlay => hard s b
  | .darken => min b s
  | .lighten => max b s
  | .colorDodge => if b == 0 then 0 else if s ≥ 1 then 1 else min 1 (b / (1 - s))
  | .colorBurn => if b ≥ 1 then 1 else if s == 0 then 0 else 1 - min 1 ((1 - b) / s)
  | .hardLight => hard b s
  | .softLight =>
    if s ≤ 0.5 then b - (1 - 2 * s) * b * (1 - b)
    else
      let d := if b ≤ 0.25 then ((16 * b - 12) * b + 4) * b else Float.sqrt b
      b + (2 * s - 1) * (d - b)
  | .difference => Float.abs (b - s)
  | .exclusion => b + s - 2 * b * s
  | _ => s

/-- Round a `[0, 1]` float to a byte. -/
def fbyte (x : Float) : Nat := (Float.floor (x * 255 + 0.5)).toUInt64.toNat

/-- Separable modes. -/
def sepModes : List BlendMode :=
  [.normal, .multiply, .screen, .overlay, .darken, .lighten, .colorDodge, .colorBurn,
   .hardLight, .softLight, .difference, .exclusion]

/-- Modes computed exactly (tolerance 0). -/
def exactModes : List BlendMode := [.normal, .darken, .lighten, .difference]

/-- `|a − b|` on naturals. -/
def dist (a b : Nat) : Nat := if a ≤ b then b - a else a - b

/-- Float reference of the non-separable modes (bytes in, bytes out). -/
def refNonSep (m : BlendMode) (cb cs : Nat × Nat × Nat) : Nat × Nat × Nat :=
  let f (c : Nat × Nat × Nat) : Float × Float × Float :=
    (c.1.toFloat / 255, c.2.1.toFloat / 255, c.2.2.toFloat / 255)
  let lumF (c : Float × Float × Float) := 0.3 * c.1 + 0.59 * c.2.1 + 0.11 * c.2.2
  let mn (c : Float × Float × Float) := min c.1 (min c.2.1 c.2.2)
  let mx (c : Float × Float × Float) := max c.1 (max c.2.1 c.2.2)
  let mp (g : Float → Float) (c : Float × Float × Float) := (g c.1, g c.2.1, g c.2.2)
  let clipC (c : Float × Float × Float) :=
    let l := lumF c
    let c := if mn c < 0 then mp (fun v => l + (v - l) * l / (l - mn c)) c else c
    if mx c > 1 then mp (fun v => l + (v - l) * (1 - l) / (mx c - l)) c else c
  let setL (c : Float × Float × Float) (l : Float) := clipC (mp (· + (l - lumF c)) c)
  let setS (c : Float × Float × Float) (s : Float) :=
    if mn c < mx c then mp (fun v => (v - mn c) * s / (mx c - mn c)) c else (0, 0, 0)
  let satF (c : Float × Float × Float) := mx c - mn c
  let b := f cb
  let s := f cs
  let r := match m with
    | .hue => setL (setS s (satF b)) (lumF b)
    | .saturation => setL (setS b (satF s)) (lumF b)
    | .color => setL s (lumF b)
    | .luminosity => setL b (lumF s)
    | _ => s
  (fbyte r.1, fbyte r.2.1, fbyte r.2.2)

/-! ## A test renderer: paths through `Clip.renderItem`, transparency through `renderTx` -/

/-- Renderer state. -/
structure TS where
  /-- Path renderer state. -/
  rs : Raster.Clip.RState
  /-- Transparency state. -/
  tx : TxState := {}

/-- The painter (identity view: page coordinates are device pixels). -/
def painter (W H : Nat) : Painter TS where
  buf := (·.rs.buf)
  setBuf := fun s b => { s with rs := { s.rs with buf := b } }
  tx := (·.tx)
  setTx := fun s t => { s with tx := t }
  paint := fun s it => { s with rs := renderItem {} Aff.id W H noStroke s.rs it }

/-- The painter is lawful (as the wiring into `Glyph` needs). -/
theorem painter_lawful (W H : Nat) : (painter W H).Lawful where
  buf_setBuf := fun _ _ => rfl
  tx_setBuf := fun _ _ => rfl
  buf_setTx := fun _ _ => rfl
  tx_setTx := fun _ _ => rfl
  paint_size := fun s it => renderItem_size {} Aff.id W H noStroke s.rs it
  paint_tx := fun _ _ => rfl

/-- Render items onto a white `W × H` page. -/
def render (W H : Nat) (items : Array DisplayItem) : Image :=
  ⟨W, H, (items.foldl (renderTx (painter W H) W H maxMaskDepth)
    { rs := { buf := whiteBuf W H } }).rs.buf⟩

/-- `render`, with strokes painted (`Clip.defaultStroke`). -/
def renderS (W H : Nat) (items : Array DisplayItem) : Image :=
  let P : Painter TS := { painter W H with
    paint := fun s it => { s with rs := renderItem {} Aff.id W H defaultStroke s.rs it } }
  ⟨W, H, (items.foldl (renderTx P W H maxMaskDepth) { rs := { buf := whiteBuf W H } }).rs.buf⟩

/-- RGB of pixel `(x, y)`. -/
def pxAt (img : Image) (x y : Nat) : Nat × Nat × Nat :=
  let i := 4 * (y * img.w + x)
  (getB img.data i, getB img.data (i + 1), getB img.data (i + 2))

/-- A page-space point. -/
def pt (x y : Int) : Content.Point := ⟨Content.Fixed.ofInt x, Content.Fixed.ofInt y⟩

/-- Rectangle `[x0, x1] × [y0, y1]`. -/
def rectP (x0 y0 x1 y1 : Int) : Path :=
  ⟨#[.moveTo (pt x0 y0), .lineTo (pt x1 y0), .lineTo (pt x1 y1), .lineTo (pt x0 y1), .closePath]⟩

/-- A component `n / 100`. -/
def comp (n : Nat) : Comp :=
  Comp.ofFixed (Content.Fixed.div (Content.Fixed.ofInt n) (Content.Fixed.ofInt 100))

/-- A fill item. -/
def fillI (p : Path) (c : Color) (alpha : Comp := Comp.one) (blend : BlendMode := .normal)
    (smask : Option Nat := none) : DisplayItem :=
  .fillPath p .nonzero { color := c, alpha, blend, smask } []

/-- Grey `n %`. -/
def grey (n : Nat) : Color := .gray (comp n)

/-- Black. -/
def black : Color := .gray Comp.zero

/-- RGB colour from percentages. -/
def rgbC (r g b : Nat) : Color := .rgb (comp r) (comp g) (comp b)

/-! ## Content-stream fixtures (end to end) -/

/-- Parse a PDF object from a string. -/
def obj (s : String) : PdfObject :=
  match ObjParse.parseObject {} s.toUTF8 0 with
  | .ok (o, _) => o
  | .error _ => .null

/-- A dictionary from a string. -/
def dictS (s : String) : Dict :=
  match obj s with
  | .dict d => d
  | _ => []

/-- A document of numbered stream objects; `decode` returns the data as is. -/
def mkSrc (objs : List (Nat × String × String)) : Content.Source Unit :=
  ⟨fun s n _ => match objs.lookup n with
     | some (d, data) => (.ok (.stream ⟨dictS d, data.toUTF8⟩), s)
     | none => (.error (.malformed 0 "missing"), s),
   fun s _ st => (.ok st.data, s)⟩

/-- Run a content stream with resources `res` over the objects `objs`. -/
def runC (objs : List (Nat × String × String)) (res content : String) : DisplayList :=
  let env : Content.Env Unit Unit := { cfg := {}, src := mkSrc objs, observe := fun _ _ _ _ => () }
  (Content.runBytes env (dictS res) content.toUTF8 () ()).items

/-- Run the suite; returns the number of failures. -/
def run : IO Nat := do
  let mut failures := 0
  let report (msg : String) : IO Unit := IO.eprintln s!"  raster-transparency FAIL: {msg}"
  -- 1. Separable blend modes vs the §11.3.5 formulas.
  let grid := (List.range 16).map (· * 17)
  for m in sepModes do
    let tol := if exactModes.contains m then 0 else 1
    let mut worst := 0
    for cb in grid do
      for cs in grid do
        let got := blendSep m cb cs
        let want := fbyte (refB m (cb.toFloat / 255) (cs.toFloat / 255))
        worst := max worst (dist got want)
    if worst > tol then
      failures := failures + 1; report s!"{repr m}: worst difference {worst} > {tol}"
  let known : List (BlendMode × Nat × Nat × Nat) :=
    [(.multiply, 255, 128, 128), (.multiply, 0, 200, 0), (.screen, 0, 128, 128),
     (.screen, 255, 3, 255), (.darken, 10, 20, 10), (.lighten, 10, 20, 20),
     (.difference, 10, 200, 190), (.exclusion, 255, 255, 0), (.exclusion, 0, 77, 77),
     (.colorDodge, 0, 255, 0), (.colorDodge, 100, 255, 255), (.colorBurn, 255, 0, 255),
     (.colorBurn, 100, 0, 0), (.hardLight, 200, 0, 0), (.hardLight, 200, 255, 255),
     (.overlay, 0, 200, 0), (.overlay, 255, 10, 255), (.softLight, 0, 255, 0),
     (.softLight, 255, 0, 255)]
  for (m, cb, cs, want) in known do
    if blendSep m cb cs != want then
      failures := failures + 1; report s!"{repr m} {cb} {cs} = {blendSep m cb cs}, want {want}"
  -- 2. Neutral source values.
  for m in sepModes.filter (· != .normal) do
    let tol := if [BlendMode.overlay, .hardLight, .softLight].contains m then 1 else 0
    let bad := (List.range 256).filter fun cb => dist (blendSep m cb (neutral m)) cb > tol
    if !bad.isEmpty then
      failures := failures + 1; report s!"neutral of {repr m} moves {bad.take 5}"
  -- 3. Non-separable modes.
  let red := (255, 0, 0)
  let blue := (0, 0, 255)
  let lumR := lumByte (blendRGB .luminosity red blue)
  if dist lumR (lumByte blue) > 1 then
    failures := failures + 1; report s!"luminosity: lum {lumR} ≠ {lumByte blue}"
  if blendRGB .color (128, 128, 128) (128, 128, 128) != (128, 128, 128) then
    failures := failures + 1; report "color of grey on grey"
  for m in [BlendMode.hue, .saturation, .color, .luminosity] do
    for c in [(255, 0, 0), (12, 200, 77), (128, 128, 128), (0, 0, 0), (250, 250, 3)] do
      if blendRGB m c c != c then
        failures := failures + 1; report s!"{repr m}({c}, {c}) ≠ {c}"
    let mut worst := 0
    for cb in [(255, 0, 0), (12, 200, 77), (128, 128, 128), (30, 60, 90), (250, 250, 3)] do
      for cs in [(0, 0, 255), (90, 10, 200), (200, 200, 200), (255, 128, 0)] do
        let g := blendRGB m cb cs
        let w := refNonSep m cb cs
        worst := max worst (max (dist g.1 w.1) (max (dist g.2.1 w.2.1) (dist g.2.2 w.2.2)))
    if worst > 1 then
      failures := failures + 1; report s!"{repr m}: worst difference {worst} vs float reference"
  -- 4. A group with alpha 0.5: overlapping squares composited once.
  let half := comp 50
  let sqA := fillI (rectP 2 2 12 12) black
  let sqB := fillI (rectP 8 8 18 18) black
  let g4 := render 20 20 #[.groupBegin { alpha := half }, sqA, sqB, .groupEnd]
  let v4 := (pxAt g4 10 10, pxAt g4 4 4, pxAt g4 15 15, pxAt g4 0 0)
  if v4 != ((127, 127, 127), (127, 127, 127), (127, 127, 127), (255, 255, 255)) then
    failures := failures + 1; report s!"group alpha 0.5: {v4}"
  let n4 := render 20 20 #[fillI (rectP 2 2 12 12) black half, fillI (rectP 8 8 18 18) black half]
  if pxAt n4 10 10 != (63, 63, 63) || pxAt n4 4 4 != (127, 127, 127) then
    failures := failures + 1; report s!"items alpha 0.5: {pxAt n4 10 10}"
  if g4.data.size != 4 * 20 * 20 then
    failures := failures + 1; report "group buffer size"
  -- 5. Luminosity soft mask from grey stripes (0 %, 25 %, 50 %, 100 % white) over BC black,
  -- mask bbox [0, 16] × [0, 4]; then black is painted over the whole 20 × 8 page through it.
  let stripes : Array DisplayItem :=
    #[fillI (rectP 0 0 4 4) (grey 0), fillI (rectP 4 0 8 4) (grey 25),
      fillI (rectP 8 0 12 4) (grey 50), fillI (rectP 12 0 16 4) (grey 100)]
  let sm5 : SoftMaskInfo := { kind := .luminosity, bbox := some (rectP 0 0 16 4) }
  let i5 := render 20 8 #[.softMask 7 sm5 stripes, fillI (rectP 0 0 20 8) black (smask := some 7)]
  let row := [1, 5, 9, 13, 17].map fun x => (pxAt i5 x 1).1
  if row != [255, 191, 127, 0, 255] || (pxAt i5 9 6).1 != 255 then
    failures := failures + 1; report s!"luminosity mask: {row}, below {(pxAt i5 9 6).1}"
  -- the mask item paints nothing itself
  let i5b := render 20 8 #[.softMask 7 sm5 stripes]
  if (pxAt i5b 1 1) != (255, 255, 255) then
    failures := failures + 1; report "mask contents painted"
  -- BC white: outside the stripes the mask is 1
  let i5c := render 20 8 #[.softMask 7 { sm5 with backdrop := .gray Comp.one } stripes,
    fillI (rectP 0 0 20 8) black (smask := some 7)]
  if (pxAt i5c 17 6).1 != 0 || (pxAt i5c 1 1).1 != 255 then
    failures := failures + 1; report s!"BC white: {(pxAt i5c 17 6).1} {(pxAt i5c 1 1).1}"
  -- an alpha mask: a black square at alpha 0.5 → mask 128 there, 0 elsewhere
  let i5d := render 20 8 #[.softMask 2 { kind := .alpha } #[fillI (rectP 0 0 10 8) black half],
    fillI (rectP 0 0 20 8) (rgbC 100 0 0) (smask := some 2)]
  if dist (pxAt i5d 3 3).2.1 127 > 1 || pxAt i5d 15 3 != (255, 255, 255) then
    failures := failures + 1; report s!"alpha mask: {pxAt i5d 3 3} {pxAt i5d 15 3}"
  -- an unknown mask identifier paints unmasked
  let i5e := render 4 4 #[fillI (rectP 0 0 4 4) black (smask := some 99)]
  if pxAt i5e 1 1 != (0, 0, 0) then
    failures := failures + 1; report "unknown mask"
  -- 6. Item blend modes and a Multiply group.
  let blueBg := fillI (rectP 0 0 10 10) (rgbC 0 0 100)
  let i6 := render 20 10 #[blueBg, fillI (rectP 0 0 20 10) (rgbC 100 0 0) (blend := .multiply)]
  if pxAt i6 5 5 != (0, 0, 0) || pxAt i6 15 5 != (255, 0, 0) then
    failures := failures + 1; report s!"multiply item: {pxAt i6 5 5} {pxAt i6 15 5}"
  let i6b := render 20 10 #[blueBg, fillI (rectP 0 0 20 10) (rgbC 100 0 0) (blend := .screen)]
  if pxAt i6b 5 5 != (255, 0, 255) || pxAt i6b 15 5 != (255, 255, 255) then
    failures := failures + 1; report s!"screen item: {pxAt i6b 5 5} {pxAt i6b 15 5}"
  let greenBg := fillI (rectP 0 0 20 10) (rgbC 0 50 0)
  let i6c := render 20 10 #[greenBg, .groupBegin { blend := .multiply },
    fillI (rectP 0 0 10 10) (rgbC 100 100 0), .groupEnd]
  if pxAt i6c 5 5 != (0, 128, 0) || pxAt i6c 15 5 != (0, 128, 0) then
    failures := failures + 1; report s!"multiply group: {pxAt i6c 5 5} {pxAt i6c 15 5}"
  -- 7. Nesting beyond maxLayerDepth: 12 nested groups at alpha 0.5, then their ends.
  let nest : Array DisplayItem :=
    (Array.replicate 12 (DisplayItem.groupBegin { alpha := half })).push (fillI (rectP 0 0 4 4) black)
      ++ Array.replicate 13 DisplayItem.groupEnd
  let i7 := render 4 4 nest
  if i7.data.size != 4 * 4 * 4 then
    failures := failures + 1; report "nested groups: buffer size"
  -- 8 open layers at alpha 0.5 → 255 · (1 − 2⁻⁸) ≈ 254 remains of the white
  if (pxAt i7 1 1).1 < 250 then
    failures := failures + 1; report s!"nested groups: {pxAt i7 1 1}"
  -- 8. End to end: ExtGState soft mask + transparency group form through the runner.
  let objs : List (Nat × String × String) :=
    [(6, "<< /Subtype /Form /BBox [0 0 16 4] /Group << /S /Transparency >> >>",
       "0 g 0 0 4 4 re f 0.25 g 4 0 4 4 re f 0.5 g 8 0 4 4 re f 1 g 12 0 4 4 re f"),
     (7, "<< /Subtype /Form /BBox [0 0 20 20] /Group << /S /Transparency /I true >> >>",
       "0 g 2 2 10 10 re f 8 8 10 10 re f")]
  let res := "<< /XObject << /G 7 0 R >> /ExtGState << /M << /SMask << /S /Luminosity " ++
    "/G 6 0 R >> >> /H << /ca 0.5 >> >> >>"
  let items8 := runC objs res "q /M gs 0 g 0 0 20 8 re f Q"
  let i8 := render 20 8 items8
  let row8 := [1, 5, 9, 13, 17].map fun x => (pxAt i8 x 1).1
  if row8 != [255, 191, 127, 0, 255] then
    failures := failures + 1
    report s!"runner soft mask: {row8} (items {items8.toList.map DisplayItem.kind})"
  let items8b := runC objs res "/H gs /G Do"
  let i8b := render 20 20 items8b
  if pxAt i8b 10 10 != (127, 127, 127) || pxAt i8b 4 4 != (127, 127, 127) then
    failures := failures + 1
    report s!"runner group: {pxAt i8b 10 10} (items {items8b.toList.map DisplayItem.kind})"
  -- 9. Knockout groups (task 7.3i): the second of two overlapping translucent squares in a
  -- `/K true` group composites over the group's backdrop, not over the first square.
  let k9 := render 20 20 #[.groupBegin { knockout := true }, fillI (rectP 2 2 12 12) black half,
    fillI (rectP 8 8 18 18) (rgbC 0 0 100) half, .groupEnd]
  let v9 := (pxAt k9 10 10, pxAt k9 4 4, pxAt k9 15 15, pxAt k9 0 0)
  if v9 != ((127, 127, 255), (127, 127, 127), (127, 127, 255), (255, 255, 255)) then
    failures := failures + 1; report s!"knockout group: {v9}"
  -- an opaque item inside a knockout group paints normally; a later translucent one knocks it out
  let k9b := render 20 20 #[.groupBegin { knockout := true }, fillI (rectP 2 2 12 12) (rgbC 100 0 0),
    fillI (rectP 8 8 18 18) (rgbC 0 0 100) half, .groupEnd, fillI (rectP 0 0 1 1) black half]
  let v9b := (pxAt k9b 10 10, pxAt k9b 4 4, pxAt k9b 15 15, pxAt k9b 0 0)
  if v9b != ((127, 127, 255), (255, 0, 0), (127, 127, 255), (127, 127, 127)) then
    failures := failures + 1; report s!"knockout over opaque: {v9b}"
  -- a knockout group at alpha 0.5 over a red backdrop
  let k9c := render 20 20 #[fillI (rectP 0 0 20 20) (rgbC 100 0 0),
    .groupBegin { knockout := true, alpha := half }, fillI (rectP 2 2 12 12) black half,
    fillI (rectP 8 8 18 18) black half, .groupEnd]
  if pxAt k9c 10 10 != pxAt k9c 4 4 || pxAt k9c 0 0 != (255, 0, 0) then
    failures := failures + 1; report s!"knockout group alpha: {pxAt k9c 10 10} {pxAt k9c 4 4}"
  -- without /K the overlap darkens
  let k9d := render 20 20 #[.groupBegin {}, fillI (rectP 2 2 12 12) black half,
    fillI (rectP 8 8 18 18) (rgbC 0 0 100) half, .groupEnd]
  if pxAt k9d 10 10 != (63, 63, 191) then
    failures := failures + 1; report s!"non-knockout group: {pxAt k9d 10 10}"
  -- `b` with a translucent stroke (`CA 0.5`, task 7.3i): a knockout group around the fill and
  -- the stroke, so inside the fill the stroke shows the page (white), not the red fill.
  let res9 := "<< /ExtGState << /K << /CA 0.5 >> >> >>"
  let items9e := runC [] res9 "/K gs 1 0 0 rg 0 0 1 RG 4 w 6 6 14 14 re b"
  let kinds9e := items9e.toList.map DisplayItem.kind
  let k9e := renderS 20 20 items9e
  let v9e := (pxAt k9e 7 10, pxAt k9e 5 10, pxAt k9e 10 10, pxAt k9e 1 1)
  if kinds9e != ["groupBegin", "fillPath", "strokePath", "groupEnd"] ||
      v9e != ((127, 127, 255), (127, 127, 255), (255, 0, 0), (255, 255, 255)) then
    failures := failures + 1; report s!"b with CA 0.5: {kinds9e} {v9e}"
  -- an opaque Normal stroke needs no group
  let items9f := runC [] res9 "1 0 0 rg 0 0 1 RG 4 w 6 6 14 14 re b"
  if items9f.toList.map DisplayItem.kind != ["fillPath", "strokePath"] then
    failures := failures + 1; report s!"b opaque: {items9f.toList.map DisplayItem.kind}"
  -- stroke alpha 0: no group, the stroke paints nothing (the fill shows everywhere)
  let items9g := runC [] "<< /ExtGState << /Z << /CA 0 /BM /Multiply >> >> >>"
    "/Z gs 1 0 0 rg 0 0 1 RG 4 w 6 6 14 14 re b"
  let k9g := renderS 20 20 items9g
  if items9g.toList.map DisplayItem.kind != ["fillPath", "strokePath"] ||
      (pxAt k9g 7 10, pxAt k9g 5 10) != ((255, 0, 0), (255, 255, 255)) then
    failures := failures + 1
    report s!"b with CA 0: {items9g.toList.map DisplayItem.kind} {(pxAt k9g 7 10, pxAt k9g 5 10)}"
  -- opaque stroke with `Multiply` (MuPDF: the blend group around the knockout group): the
  -- group carries the blend mode, the fill and stroke inside it are `Normal`; on a grey page
  -- the cyan stroke over the yellow fill multiplies the page only (grey × cyan), not the fill
  -- (grey × yellow × cyan = (0, 128, 0) without the group)
  let items9h := runC [] "<< /ExtGState << /M << /BM /Multiply >> >> >>"
    "0.5 g 0 0 20 20 re f /M gs 1 1 0 rg 0 1 1 RG 4 w 6 6 14 14 re b"
  let ok9h := match items9h.toList with
    | [.fillPath .., .groupBegin g, .fillPath _ _ f _, .strokePath _ k _, .groupEnd] =>
      g.knockout && !g.isolated && g.blend == .multiply && f.blend == .normal &&
        k.blend == .normal
    | _ => false
  let k9h := renderS 20 20 items9h
  let v9h := (pxAt k9h 7 10, pxAt k9h 10 10, pxAt k9h 1 1)
  let near1 (a b : Nat × Nat × Nat) : Bool :=
    a.1 + 1 ≥ b.1 && b.1 + 1 ≥ a.1 && a.2.1 + 1 ≥ b.2.1 && b.2.1 + 1 ≥ a.2.1 &&
      a.2.2 + 1 ≥ b.2.2 && b.2.2 + 1 ≥ a.2.2
  if !ok9h || !near1 v9h.1 (0, 128, 128) || !near1 v9h.2.1 (128, 128, 0) ||
      !near1 v9h.2.2 (128, 128, 128) then
    failures := failures + 1
    report s!"b with BM Multiply: {items9h.toList.map DisplayItem.kind} {v9h}"
  -- fill+stroke text (`2 Tr`) with `CA 0.5` (one glyph run; the renderer gives it MuPDF's
  -- knockout group, `Transparency.splitRun?`): no pixel shows the blue stroke over the red fill
  -- ((127, 0, 128)); the stroke shows over the page ((127, 127, 255)) and the fill shows red.
  let ttf ← IO.FS.readBinFile "Tests/fonts/tiny.ttf"
  let textPdf (ca : String) := RasterGlyph.resPage
    s!"<< /Font << /F1 5 0 R >> /ExtGState << /K << /CA {ca} >> >> >>"
    "/K gs BT /F1 100 Tf 2 Tr 6 w 1 0 0 rg 0 0 1 RG 20 20 Td (A) Tj ET"
    [ "<< /Type /Font /Subtype /TrueType /BaseFont /SafePdfTiny /FirstChar 65 /LastChar 65 /Widths [600] /Encoding /WinAnsiEncoding /FontDescriptor 6 0 R >>",
      "<< /Type /FontDescriptor /FontName /SafePdfTiny /Flags 32 /FontFile2 7 0 R >>",
      CFFText.strmObj "/Filter /ASCIIHexDecode" (CFFText.hex ttf) ]
  let countPx (img : Image) (c : Nat × Nat × Nat) : Nat := Id.run do
    let mut n := 0
    for y in [0:img.h] do
      for x in [0:img.w] do
        if near1 (pxAt img x y) c then n := n + 1
    return n
  match RasterGlyph.render (textPdf "0.5"), RasterGlyph.render (textPdf "1") with
  | some t5, some t1 =>
    let c5 := (countPx t5 (127, 0, 128), countPx t5 (127, 127, 255), countPx t5 (255, 0, 0))
    let c1 := (countPx t1 (127, 0, 128), countPx t1 (127, 127, 255), countPx t1 (0, 0, 255))
    if c5.1 != 0 || c5.2.1 < 100 || c5.2.2 < 100 || c1.2.1 != 0 || c1.2.2 < 100 then
      failures := failures + 1; report s!"text 2 Tr with CA 0.5 / 1: {c5} {c1}"
  | _, _ => failures := failures + 1; report "text 2 Tr: render failed"
  -- 10. Timing: a group of 100 squares at alpha 0.5 on 612 × 792; a soft-masked full fill.
  let sq : Array DisplayItem := (Array.range 100).map fun k =>
    let x : Int := (k % 10 : Nat) * 60
    let y : Int := (k / 10 : Nat) * 78
    fillI (rectP x y (x + 50) (y + 70)) (rgbC (k % 100) 30 60)
  let t0 ← IO.monoMsNow
  let i9 := render 612 792 ((#[DisplayItem.groupBegin { alpha := half }] ++ sq).push .groupEnd)
  let n9 := (pxAt i9 25 35).1
  let t1 ← IO.monoMsNow
  let i9b := render 612 792 #[.softMask 1 { kind := .luminosity } #[fillI (rectP 0 0 306 792) (grey 100)],
    fillI (rectP 0 0 612 792) black (smask := some 1)]
  let n9b := (pxAt i9b 10 10).1
  let t2 ← IO.monoMsNow
  IO.println s!"  raster-transparency: group of 100 squares at alpha 0.5 on 612×792: {t1 - t0} ms; luminosity-masked full fill: {t2 - t1} ms ({n9}, {n9b})"
  if n9b != 0 || (pxAt i9b 400 10).1 != 255 then
    failures := failures + 1; report "timing page mask"
  return failures

end SafePdf.Tests.RasterTransparency
