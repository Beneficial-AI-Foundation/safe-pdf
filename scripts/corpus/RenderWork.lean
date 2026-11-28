import SafePdf.Core.Parse
import SafePdf.Core.Doc
import SafePdf.Core.Raster.Glyph
import SafePdf.Shell.Fonts

/-!
# Counted render work per page (task 13.4a, calibration spike)

Read-only measuring tool; nothing under `SafePdf/` changes. Driven by
`scripts/corpus/render-work.py` (which compiles this file and runs it once per PDF); see
`docs/render-work-calibration.md` for what is measured and why.

`RenderWork FILE DPI [--check]` prints one tab-separated line per page:

    page  W  H  items  steps  pixels  replaySteps  approx  groups  softMasks  imgOk

* `steps` is the counted work of the page as the renderer charges it: `RState.steps` of the
  final `TState` of `Glyph.renderItems` (clip masks, rasterizer rows, compositing, images,
  shadings, tiling cells, Type 3 glyphs). `renderItemsCounted_steps_le` and
  `fillEdgesCounted_steps_le` bound exactly this quantity (for path items). It is obtained
  by repeating the front half of `Glyph.renderDocPage` (a copy: that function returns only the
  image) and reading the state that `Glyph.renderPage` discards. `--check` compares the image
  with the one `renderDocPage` returns (`imgOk` is 1 when equal), so a drift of the copy is
  caught.
* `pixels` is the second candidate unit: the pixels written, i.e. the areas of every coverage
  mask built (clip levels, fills, glyph, stroke) plus the area composited, without the
  rasterizer's edge-walking term (`S · E` per row). Computed by replaying the top-level
  display items with the same functions (`clipMaskC`'s recursion, `fillCounted`,
  `runMasks`, the page's stroker); items of other kinds (images, shadings, tiling or Type 3
  items) are charged their real `steps` delta in both units. `replaySteps` is the replay's
  step total: it equals `steps` on every corpus page without transparency groups (on pages
  with groups the replay is lower, by up to 45%: the cause was not investigated); `approx`
  counts the Type 3 and pattern-coloured items charged by their real delta in both units
  (images, shadings and other kinds are charged so too, uncounted); `groups` and `softMasks` count the
  top-level `groupBegin` and `softMask` items.
-/

open SafePdf SafePdf.Core SafePdf.Core.Content SafePdf.Core.Raster SafePdf.Core.Raster.Fill
open SafePdf.Core.Raster.Glyph SafePdf.Core.Raster.Clip

/-- What the replay accumulates. -/
structure WAcc where
  /-- Clip cache (the real one's recursion and eviction). -/
  cc : ClipCache := {}
  /-- Outline cache of the glyph runs. -/
  oc : Cache := {}
  /-- Type 3 glyph bitmap cache. -/
  t3 : Type3.GlyphCache := Type3.GlyphCache.empty
  /-- Steps as the renderer charges them. -/
  steps : Nat := 0
  /-- Pixels written. -/
  pixels : Nat := 0
  /-- Items replayed approximately (patterns, type 3). -/
  approx : Nat := 0

/-- `clipMaskC` with the pixel total of the masks it builds: `(mask, cache, steps, pixels)`. -/
def clipMaskP (cfg : Fill.Config) (m : Geom.Aff) (W H : Nat) (cc : ClipCache) :
    Clip → Option Mask × ClipCache × Nat × Nat
  | [] => (none, cc, 0, 0)
  | cp :: rest =>
    match cc.find? (cp :: rest) with
    | some mk => (some mk, cc.touch (cp :: rest) mk, 0, 0)
    | none =>
      let r1 := clipMaskP cfg m W H cc rest
      let win := clipWindow W H r1.1
      let f := fillCounted cfg m cp.path cp.rule win
      let res := combine f.1 r1.1
      (some res, r1.2.1.insert cfg.clipCacheSize (cp :: rest) res,
        r1.2.2.1 + f.2 + res.area, r1.2.2.2 + f.1.area + res.area)

/-- The glyph-run, fill and stroke items are replayed with their own functions; any other item
is charged what the real item painter charges. -/
def replayItem (cfg : Fill.Config) (m : Geom.Aff) (W H : Nat) (stroke : StrokeFn) (pf : PageFonts)
    (a : WAcc) (it : DisplayItem) : WAcc :=
  let other := fun (a : WAcc) =>
    let st : TState := { rs := { buf := ByteArray.empty, cache := a.cc } , cache := a.oc, t3 := a.t3 }
    let st' := renderItemG cfg m W H stroke pf st it
    { a with cc := st'.rs.cache, oc := st'.cache, t3 := st'.t3, steps := a.steps + st'.rs.steps,
             pixels := a.pixels + st'.rs.steps }
  match it with
  | .fillPath p rule style clip =>
    if (pf.tilings.tileOf style.color style.pattern).isSome ||
        (pf.shadings.patternOf style.color style.pattern).isSome then
      { other a with approx := a.approx + 1 }
    else
      let c := clipMaskP cfg m W H a.cc clip
      let f := fillCounted cfg m p rule (itemWindow W H c.1)
      let r := f.1.rect.inter (itemWindow W H c.1)
      { a with cc := c.2.1, steps := a.steps + c.2.2.1 + f.2 + r.width * r.height,
               pixels := a.pixels + c.2.2.2 + f.1.area + r.width * r.height }
  | .strokePath p style clip =>
    if (pf.tilings.tileOf style.color style.pattern).isSome ||
        (pf.shadings.patternOf style.color style.pattern).isSome then
      { other a with approx := a.approx + 1 }
    else
      let c := clipMaskP cfg m W H a.cc clip
      let win := itemWindow W H c.1
      let fm := stroke cfg m win p style
      let r := fm.rect.inter win
      { a with cc := c.2.1, steps := a.steps + c.2.2.1 + r.width * r.height,
               pixels := a.pixels + c.2.2.2 + fm.area + r.width * r.height }
  | .glyphRun r clip =>
    if !r.renderMode.paints then a else
    if ((pf.sources.get r.font).bind (·.t3)).isSome then { other a with approx := a.approx + 1 }
    else
      let c := clipMaskP cfg m W H a.cc clip
      let win := itemWindow W H c.1
      let (ms, oc) := runMasks cfg m win pf a.oc r
      -- `paintAll`: the clip's work is charged once, with the first mask (or alone).
      let (steps, pixels, _) := ms.foldl (fun (acc : Nat × Nat × Bool) (mk, col, _, w) =>
        let rr := (Mask.rect mk).inter win
        let comp := rr.width * rr.height
        let isPat := (runPattern pf.shadings r col).isSome || (runTiling pf.tilings r col).isSome
        if isPat then (acc.1 + w, acc.2.1 + mk.area, true) else
        (acc.1 + w + comp, acc.2.1 + mk.area + comp, true)) (c.2.2.1, c.2.2.2, false)
      { a with cc := c.2.1, oc := oc, steps := a.steps + steps, pixels := a.pixels + pixels,
               approx := a.approx + (if ms.any (fun (_, col, _, _) =>
                 (runPattern pf.shadings r col).isSome || (runTiling pf.tilings r col).isSome)
                 then 1 else 0) }
  | _ => other a

/-- The part of `renderDocPage` before `renderPage`, repeated: the display list, the page's
fonts and resources, and the view. Keep in step with `Glyph.renderDocPage`; `--check`
verifies the image. -/
def prepare (limits : Limits) (doc : Doc.Doc) (page : Doc.Page) (zoom : Rat)
    (rot : Doc.Rotation) (budget : Filter.Budget) (subst : Subst.SubstFonts) :
    Option (DisplayList × PageFonts) :=
  let (ocs, budget) := Text.ocStateFor limits doc budget none
  match Text.extractDocPage limits doc page budget {} (some ocs) with
  | (.error _, _) => none
  | (.ok pt, b) =>
    let (ap, b) := Annot.docAnnots limits doc page pt.fonts (Annot.Budget.after limits pt) b
      (some ocs)
    let items := pt.items ++ ap.items
    let (srcs, b) := loadSources limits (Text.docSource limits doc) b (page.resources.getD []) 0 subst
    let (srcs, b) := ap.roots.foldl (fun (acc : SourceTable × Filter.Budget) r =>
      let (t, b) := loadSources limits (Text.docSource limits doc) acc.2 r.2 r.1 subst; (acc.1 ++ t, b)) (srcs, b)
    let (tls, ft, b, _) := Tiling.loadTilingsWith
      (fun (ft : Text.FontTable × SourceTable) => Text.textEnv limits (Text.docSource limits doc) ft.1 ocs)
      (fun ft b num res =>
        let (fonts, b) := Annot.loadAnnotFonts limits (Text.docSource limits doc) b ft.1 [(num, res)]
        let (t, b) := loadSources limits (Text.docSource limits doc) b res num subst
        ((fonts, ft.2 ++ t), b))
      (ap.fonts, srcs) b ()
      { ops := limits.maxOpsPerPage - pt.ops - ap.ops, forms := limits.maxFormsPerPage - pt.forms - ap.forms }
      (page.resources.getD []) items
    let (srcs, b, _, _) := loadType3 (Text.textEnv limits (Text.docSource limits doc) ft.1 ocs) b ()
      tls.budget (page.resources.getD []) ft.2
    let all := items ++ tls.cellItems ++ type3Items srcs
    let view := Geom.viewMatrix zoom (Geom.rotAdd page.rotate rot) (Geom.Box.ofRect page.cropBox)
    let exts := Image.imageExtents limits.maxXObjectDepth view items
      (tls.cellItems ++ type3Items srcs)
    let imageSource := Text.docSource limits doc
    let (imgs, b) := Image.loadImages limits imageSource b (page.resources.getD []) all exts .document
    let (imgs, b) := imgs.loadInlineJPXFrom imageSource b (some view) items
    let (imgs, b) := imgs.loadInlineJPXFrom imageSource b none (tls.cellItems ++ type3Items srcs)
    let (shs, _) := Shading.loadShadings limits (Text.docSource limits doc) b (page.resources.getD []) all
    some (items, { fonts := tabulateWidths ft.1, sources := srcs, images := imgs, shadings := shs,
                   tilings := tls, fallback := hailMarySource subst })

/-- Count the groups, soft masks and similar uncounted constructs of a display list (top level). -/
def countKinds (items : DisplayList) : Nat × Nat :=
  items.foldl (fun (g, s) it => match it with
    | .groupBegin _ => (g + 1, s)
    | .softMask .. => (g, s + 1)
    | _ => (g, s)) (0, 0)

def main (args : List String) : IO UInt32 := do
  let path :: dpiS :: rest := args
    | IO.eprintln "usage: RenderWork FILE DPI [--check]"; return 2
  let some dpi := dpiS.toNat? | IO.eprintln "bad dpi"; return 2
  let check := rest.contains "--check"
  let limits : Limits := Limits.default
  let bytes ← IO.FS.readBinFile path
  let doc ← match parseWith limits bytes with
    | .error e => IO.println s!"#open-error\t{repr e}"; return 1
    | .ok d => match (Doc.ofSession d.session limits).1 with
      | .error e => IO.println s!"#open-error\t{repr e}"; return 1
      | .ok doc => pure doc
  let subst ← SafePdf.Shell.Fonts.loadSubstFonts limits
  let zoom : Rat := (dpi : Rat) / 72
  let cfg : Fill.Config := Fill.Config.ofLimits limits
  IO.println s!"#pages\t{doc.pages.size}"
  for k in [0:doc.pages.size] do
   if let some page := doc.pages[k]? then
    let rot : Doc.Rotation := .r0
    match prepare limits doc page zoom rot (Filter.Budget.init limits) subst with
    | none => IO.println s!"{k + 1}\terror"
    | some (items, pf) =>
      let r := Geom.rotAdd page.rotate rot
      let bx := Geom.Box.ofRect page.cropBox
      let sz := pageSize cfg.maxPageSide zoom r bx
      let view := Geom.viewMatrix zoom r bx
      let stroke := tableStroke (pageGeoTable cfg view items)
      let ts := Glyph.renderItems cfg view sz.1 sz.2 pf items stroke
      let acc := items.foldl (replayItem cfg view sz.1 sz.2 stroke pf) ({} : WAcc)
      let (g, s) := countKinds items
      let imgOk ← if check then
          let img := (renderDocPage limits doc page zoom rot (Filter.Budget.init limits)
            (subst := subst)).1
          match img with
          | .ok im => pure (if im.data == ts.rs.buf then "1" else "0")
          | .error _ => pure "0"
        else pure "-"
      IO.println s!"{k + 1}\t{sz.1}\t{sz.2}\t{items.size}\t{ts.rs.steps}\t{acc.pixels}\t{acc.steps}\t{acc.approx}\t{g}\t{s}\t{imgOk}"
  return 0
