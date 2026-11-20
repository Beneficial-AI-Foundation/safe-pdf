import SafePdf.Core.Raster.Subst

/-!
# Substitute font programs from the system (task 7.7)

Plan.md §6 Phase 7 (pixel faithfulness vs MuPDF); ledger Decisions 2026-11-20 (7.7):
"Substitute fonts are found on the system, not committed". The repository ships no font
files (it is MIT; the URW base-35 fonts are AGPL-3.0 with a font exception, TeX Gyre GUST
licensed). This Shell module finds, at run time, one program per standard-14 face and hands
the bytes to the core (`Core.Raster.Subst.SubstFonts.ofBytes`, parsed lazily there).

Search order per face (first file found wins):

1. `$SAFEPDF_FONT_DIR` (one directory, or several separated by `:`), with the URW base-35 file
   names, then the TeX Gyre names;
2. URW base-35 (Debian/Ubuntu `fonts-urw-base35`, the outlines MuPDF bundles):
   `/usr/share/fonts/type1/urw-base35` (`.t1`), `/usr/share/fonts/X11/Type1` (`.pfb`),
   `/usr/share/fonts/opentype/urw-base35` (`.otf`), Ghostscript's `Resource/Font` (no
   extension; Homebrew and `/usr/local`, `/usr`);
3. TeX Gyre (`fonts-texgyre`): `/usr/share/texmf/fonts/opentype/public/tex-gyre`,
   `/usr/share/fonts/opentype/texgyre` — Heros (Helvetica), Termes (Times), Cursor (Courier);
   no Symbol/ZapfDingbats.

`SAFEPDF_SUBST_FONTS=0` disables substitutes (non-embedded text unpainted, the behaviour
before task 7.7). A face with no file, an unreadable file or one larger than
`maxFontFileBytes` is simply absent: its text stays unpainted, nothing fails.
-/

namespace SafePdf.Shell.Fonts

open SafePdf SafePdf.Core
open SafePdf.Core.Font (Std14)

/-- Largest font file read (bytes). -/
def maxFontFileBytes : Nat := 16 <<< 20

/-- The URW base-35 file name (without extension) of a standard-14 face. -/
def urwName : Std14 → String
  | .helvetica => "NimbusSans-Regular"
  | .helveticaBold => "NimbusSans-Bold"
  | .helveticaOblique => "NimbusSans-Italic"
  | .helveticaBoldOblique => "NimbusSans-BoldItalic"
  | .timesRoman => "NimbusRoman-Regular"
  | .timesBold => "NimbusRoman-Bold"
  | .timesItalic => "NimbusRoman-Italic"
  | .timesBoldItalic => "NimbusRoman-BoldItalic"
  | .courier => "NimbusMonoPS-Regular"
  | .courierBold => "NimbusMonoPS-Bold"
  | .courierOblique => "NimbusMonoPS-Italic"
  | .courierBoldOblique => "NimbusMonoPS-BoldItalic"
  | .symbol => "StandardSymbolsPS"
  | .zapfDingbats => "D050000L"

/-- The TeX Gyre file name (without extension) of a face, if TeX Gyre has one. -/
def texGyreName : Std14 → Option String
  | .helvetica => some "texgyreheros-regular"
  | .helveticaBold => some "texgyreheros-bold"
  | .helveticaOblique => some "texgyreheros-italic"
  | .helveticaBoldOblique => some "texgyreheros-bolditalic"
  | .timesRoman => some "texgyretermes-regular"
  | .timesBold => some "texgyretermes-bold"
  | .timesItalic => some "texgyretermes-italic"
  | .timesBoldItalic => some "texgyretermes-bolditalic"
  | .courier => some "texgyrecursor-regular"
  | .courierBold => some "texgyrecursor-bold"
  | .courierOblique => some "texgyrecursor-italic"
  | .courierBoldOblique => some "texgyrecursor-bolditalic"
  | .symbol | .zapfDingbats => none

/-- Every standard-14 face. -/
def allFaces : List Std14 :=
  [.helvetica, .helveticaBold, .helveticaOblique, .helveticaBoldOblique, .timesRoman, .timesBold,
    .timesItalic, .timesBoldItalic, .courier, .courierBold, .courierOblique, .courierBoldOblique,
    .symbol, .zapfDingbats]

/-- URW base-35 system directories, with the extensions to try in each. -/
def urwDirs : List (String × List String) :=
  [ ("/usr/share/fonts/type1/urw-base35", [".t1"]),
    ("/usr/share/fonts/X11/Type1", [".pfb"]),
    ("/usr/share/fonts/opentype/urw-base35", [".otf"]),
    ("/opt/homebrew/share/ghostscript/Resource/Font", [""]),
    ("/usr/local/share/ghostscript/Resource/Font", [""]),
    ("/usr/share/ghostscript/Resource/Font", [""]) ]

/-- TeX Gyre system directories. -/
def texGyreDirs : List String :=
  ["/usr/share/texmf/fonts/opentype/public/tex-gyre", "/usr/share/fonts/opentype/texgyre"]

/-- Extensions tried in `$SAFEPDF_FONT_DIR`. -/
def userExts : List String := [".t1", ".pfb", ".pfa", ".otf", ""]

/-- The candidate paths of a face, in search order (`userDirs` from `$SAFEPDF_FONT_DIR`). -/
def candidates (userDirs : List String) (f : Std14) : List System.FilePath :=
  let names := urwName f :: (texGyreName f).toList
  let user := userDirs.flatMap fun d => names.flatMap fun n =>
    userExts.map fun e => System.FilePath.mk d / (n ++ e)
  let urw := urwDirs.flatMap fun (d, es) => es.map fun e => System.FilePath.mk d / (urwName f ++ e)
  let gyre := match texGyreName f with
    | some n => texGyreDirs.map fun d => System.FilePath.mk d / (n ++ ".otf")
    | none => []
  user ++ urw ++ gyre

/-- The bytes of the first readable candidate file (at most `maxFontFileBytes`). -/
def firstFile : List System.FilePath → IO (Option (System.FilePath × ByteArray))
  | [] => return none
  | p :: rest => do
    let ok ← try
        let md ← p.metadata
        pure (md.type == .file && md.byteSize.toNat ≤ maxFontFileBytes)
      catch _ => pure false
    if ok then
      try
        return some (p, ← IO.FS.readBinFile p)
      catch _ => firstFile rest
    else firstFile rest

/-- The directories of `$SAFEPDF_FONT_DIR`. -/
def userDirs : IO (List String) := do
  match ← IO.getEnv "SAFEPDF_FONT_DIR" with
  | some d => return (d.splitOn ":").filter (!·.isEmpty)
  | none => return []

/-- **Find the substitute font files**: each face with the file found for it. Empty when
`SAFEPDF_SUBST_FONTS=0`. -/
def findFiles : IO (List (Std14 × System.FilePath × ByteArray)) := do
  if (← IO.getEnv "SAFEPDF_SUBST_FONTS") == some "0" then return []
  let dirs ← userDirs
  let mut out := []
  for f in allFaces do
    if let some (p, b) ← firstFile (candidates dirs f) then out := out ++ [(f, p, b)]
  return out

/-- **The substitute table** for the core renderer (`Core.Raster.Glyph.renderDocPage …
(subst := …)`): the files found, parsed lazily under `limits`. -/
def loadSubstFonts (limits : Limits) : IO Raster.Subst.SubstFonts := do
  let fs ← findFiles
  return Raster.Subst.SubstFonts.ofBytes limits (fs.map fun (f, _, b) => (f, b))

end SafePdf.Shell.Fonts
