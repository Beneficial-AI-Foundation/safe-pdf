import SafePdf
import SafePdf.Quarantine.CCITT
import Tests.RasterSubst

/-!
# CCITT fax images and Type 3 bitmap glyphs (task 7.8)

Plan.md §6 Phase 7 (pixel faithfulness vs MuPDF; images composited from quarantine-zone
decodes). dvips + Ghostscript Type 3 fonts draw every glyph as an inline CCITT Group 4 stencil
mask; without a decoder each glyph was the placeholder, a solid box in the text colour.

* Decoder unit cases (`Quarantine.CCITT.decode`): hand-assembled Group 4 and Group 3 rows
  (horizontal and vertical modes, `/BlackIs1`, the row cap, limits, a missing initial `EOL`).
* Fixture `Tests/fixtures-type3/ccitt.pdf` (`python3 -I Tests/fixtures-type3/gen_ccitt.py`):
  four Type 3 glyphs, each an inline CCITT image mask of another flavour (G4 with `/D [1 0]`,
  G4 plain, G3 1-D byte-aligned `/BlackIs1`, G3 mixed `/K 2` with `/EndOfLine`), at 100 and
  50 pt, and a `[/FlateDecode /CCITTFaxDecode]` image XObject with an indirect `/Columns`.
  Always checked: the ring glyph has a white hole and black ring (no box), the checkerboard
  alternates. With `mutool`: at most 0.1% of the pixels differ (`pixels.py` metric).
-/

namespace SafePdf.Tests.RasterType3Fax

open SafePdf.Core
open SafePdf.Core.Raster
open SafePdf.Tests.RasterSubst (Rgb mutoolRef differing)

/-- The fixture's path. -/
def fixture : System.FilePath := "Tests/fixtures-type3/ccitt.pdf"

/-- Decode with default limits. -/
def dec (p : Quarantine.CCITT.Params) (rows : Nat) (b : List UInt8) : Option (List UInt8) :=
  match Quarantine.CCITT.decode {} p rows ⟨b.toArray⟩ with
  | .ok out => some out.toList
  | .error _ => none

/-- Decoder cases: name, result, expected. Row `WWWBBBBW` (8 columns) is raw `0x1E`, output
`0xE1` without `/BlackIs1`. -/
def decoderCases : List (String × Option (List UInt8) × Option (List UInt8)) :=
  [ -- G4: one all-white row, V0 → `1`
    ("g4-white", dec { k := -1, columns := 8 } 1 [0x80], some [0xFF]),
    -- G3 1-D: white 3 `1000`, black 4 `011`, white 1 `000111`
    ("g3-1d", dec { columns := 8 } 1 [0x86, 0x38], some [0xE1]),
    ("g3-1d-blackis1", dec { columns := 8, blackIs1 := true } 1 [0x86, 0x38], some [0x1E]),
    -- G4: H 3 W / 4 B, V0; second row V0 V0 V0
    ("g4-h-v0", dec { k := -1, columns := 8 } 2 [0x30, 0xFC], some [0xE1, 0xE1]),
    ("g4-row-cap", dec { k := -1, columns := 8 } 1 [0x30, 0xFC], some [0xE1]),
    -- 16 columns: stride 2
    ("g4-two-bytes", dec { k := -1, columns := 16 } 1 [0x80], some [0xFF, 0xFF]),
    -- no data: no row
    ("empty", dec { k := -1, columns := 8 } 4 [], some []),
    -- `/EndOfLine` without an EOL in the data
    ("missing-eol", dec { endOfLine := true, columns := 8 } 1 [0x86, 0x38], none),
    -- an invalid 2-D code (`0000001000`, no mode) at the start of row 2: the partial row
    -- (nothing set: white) is emitted, then decoding stops (MuPDF `error:`)
    ("invalid-code", dec { k := -1, columns := 8 } 3 [0x30, 0xE0, 0x47], some [0xE1, 0xFF]),
    ("columns-limit", (match Quarantine.CCITT.decode { maxImagePixels := 4 } { columns := 8 } 1
        ⟨#[0x80]⟩ with | .ok o => some o.toList | .error _ => none), none) ]

/-- Render page 1 at zoom 1. -/
def render (bytes : ByteArray) : Option Clip.Image :=
  match Doc.openDoc {} bytes with
  | .ok d =>
    match d.pages.toList with
    | p :: _ =>
      match (Glyph.renderDocPage {} d p 1 .r0 (Filter.Budget.init {})).1 with
      | .ok img => some img
      | .error _ => none
    | [] => none
  | .error _ => none

/-- Expected colours at device pixels (72 dpi, page 300 × 220): `true` = dark. The ring glyph
(100 pt, origin 20 150) spans x 20–60, rows 30–70; the checkerboard (glyph 3 at x 106) has
3 px cells from row 40. -/
def probes : List (String × Nat × Nat × Bool) :=
  [ ("ring hole", 40, 50, false), ("ring left", 23, 50, true), ("ring top", 40, 33, true),
    ("check cell 0", 107, 41, true), ("check cell 1", 110, 41, false),
    ("check cell 2", 113, 41, true), ("check row 2", 107, 44, false),
    ("image stripe", 30, 152, true), ("image gap", 30, 162, false) ]

/-- Run the suite. -/
def run : IO Nat := do
  let mut failures := 0
  let report (s : String) : IO Unit := IO.println s!"  FAIL raster-type3-fax: {s}"
  for (n, got, want) in decoderCases do
    if got != want then
      failures := failures + 1; report s!"{n}: got {got}, want {want}"
  let bytes ← IO.FS.readBinFile fixture
  let some img := render bytes
    | report "fixture does not render"; return failures + 1
  let ours := Rgb.ofImage img
  for (n, x, y, dark) in probes do
    let v := ours.at x y 0
    if (v < 128) != dark then
      failures := failures + 1; report s!"{n} ({x}, {y}): red {v}, want {if dark then "dark" else "light"}"
  let some ref ← mutoolRef fixture
    | IO.println "  raster-type3-fax: mutool not available; MuPDF comparison skipped"
      return failures
  let n := differing ours ref
  if n * 1000 > ours.w * ours.h then
    failures := failures + 1; report s!"{n} of {ours.w * ours.h} pixels differ from MuPDF"
  return failures

end SafePdf.Tests.RasterType3Fax
