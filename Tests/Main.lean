import SafePdf
import Tests.Golden
import Tests.Adversarial
import Tests.XrefViews
import Tests.FlateRoundTrip
import Tests.StreamsView
import Tests.Bombs
import Tests.PagesView
import Tests.Crypt
import Tests.SvgView
import Tests.TextView
import Tests.FontIdentity
import Tests.RasterGeom
import Tests.CFFText
import Tests.RasterFill
import Tests.RasterFillSpec
import Tests.RasterClip
import Tests.RasterStroke
import Tests.RasterStrokeSpec
import Tests.TextLayout
import Tests.TextUnicode
import Tests.RasterGlyph
import Tests.RasterGlyphSpec
import Tests.RasterComposite
import Tests.RasterSubst
import Tests.RasterImage
import Tests.RasterTransparency
import Tests.RasterShading
import Tests.RasterTiling
import Tests.RasterTxFast
import Tests.Annot
import Tests.DCT

/-!
# Test runner

Shared registry: test suites are registered in `suites` (the orchestrator adds lines).
-/

namespace SafePdf.Tests

/-- A named test suite returning the number of failures. -/
structure Suite where
  name : String
  run : IO Nat

/-- Registered test suites. -/
def suites : List Suite :=
  [ { name := "smoke", run := do
        let l := SafePdf.Limits.default
        return if l.maxXObjectDepth == 32 then 0 else 1 },
    { name := "golden", run := SafePdf.Tests.Golden.run },
    { name := "adversarial", run := SafePdf.Tests.Adversarial.run },
    { name := "xref-views", run := SafePdf.Tests.XrefViews.run },
    { name := "flate-roundtrip", run := SafePdf.Tests.FlateRoundTrip.run },
    { name := "streams-view", run := SafePdf.Tests.StreamsView.run },
    { name := "bombs", run := SafePdf.Tests.Bombs.run },
    { name := "pages-view", run := SafePdf.Tests.PagesView.run },
    { name := "crypt", run := SafePdf.Tests.Crypt.run },
    { name := "svg-view", run := SafePdf.Tests.SvgView.run },
    { name := "text-view", run := SafePdf.Tests.TextView.run },
    { name := "font-identity", run := SafePdf.Tests.FontIdentity.run },
    { name := "raster-geom", run := SafePdf.Tests.RasterGeom.run },
    { name := "cff-text", run := SafePdf.Tests.CFFText.run },
    { name := "raster-fill", run := SafePdf.Tests.RasterFill.run },
    { name := "raster-fill-spec", run := SafePdf.Tests.RasterFillSpec.run },
    { name := "raster-clip", run := SafePdf.Tests.RasterClip.run },
    { name := "raster-stroke", run := SafePdf.Tests.RasterStroke.run },
    { name := "raster-stroke-spec", run := SafePdf.Tests.RasterStrokeSpec.run },
    { name := "text-layout", run := SafePdf.Tests.TextLayout.run },
    { name := "text-unicode", run := SafePdf.Tests.TextUnicode.run },
    { name := "raster-glyph", run := SafePdf.Tests.RasterGlyph.run },
    { name := "raster-glyph-spec", run := SafePdf.Tests.RasterGlyphSpec.run },
    { name := "raster-composite", run := SafePdf.Tests.RasterComposite.run },
    { name := "raster-subst", run := SafePdf.Tests.RasterSubst.run },
    { name := "raster-image", run := SafePdf.Tests.RasterImage.run },
    { name := "raster-transparency", run := SafePdf.Tests.RasterTransparency.run },
    { name := "raster-shading", run := SafePdf.Tests.RasterShading.run },
    { name := "raster-tiling", run := SafePdf.Tests.RasterTiling.run },
    { name := "raster-tx-fast", run := SafePdf.Tests.RasterTxFast.run },
    { name := "annot", run := SafePdf.Tests.Annot.run },
    { name := "dct", run := SafePdf.Tests.DCT.run } ]

end SafePdf.Tests

def main : IO UInt32 := do
  let mut failures := 0
  for s in SafePdf.Tests.suites do
    let f ← s.run
    IO.println s!"[{if f == 0 then "PASS" else "FAIL"}] {s.name} ({f} failures)"
    failures := failures + f
  return if failures == 0 then 0 else 1
