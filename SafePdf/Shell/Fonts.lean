import SafePdf.Core.Raster.Subst
import SafePdf.Shell.Read

/-!
# Substitute font programs from the system (tasks 7.7, 9.r7)

Plan.md §6 Phase 7 (pixel faithfulness vs MuPDF); ledger Decisions 2026-11-20 (7.7):
"Substitute fonts are found on the system, not committed". The repository ships no font
files (it is MIT; the URW base-35 fonts are AGPL-3.0 with a font exception, TeX Gyre GUST
licensed, the macOS fonts Apple's). This Shell module finds, at run time, one program per
standard-14 face and hands the bytes — with the face index inside a TrueType collection — to
the core (`Core.Raster.Subst.SubstFonts.ofFaces`, parsed lazily there).

Search order per face (first readable candidate wins; `docs/raster.md` lists it in full):

1. `$SAFEPDF_FONT_DIR` (one directory, or several separated by `:`), with the URW base-35 file
   names, then the TeX Gyre names;
2. URW base-35 (the outlines MuPDF bundles): Debian/Ubuntu `fonts-urw-base35`
   (`/usr/share/fonts/type1/urw-base35`, `/usr/share/fonts/X11/Type1`,
   `/usr/share/fonts/opentype/urw-base35`), then Ghostscript's `Resource/Font` (no extension)
   under `/opt/homebrew`, `/usr/local` (Homebrew) and `/usr`, unversioned and in every
   version directory `share/ghostscript/<ver>/Resource/Font` (versions sorted, newest name
   first);
3. TeX Gyre (`.otf`; Heros = Helvetica, Termes = Times, Cursor = Courier; no Symbol or
   Dingbats): Debian `fonts-texgyre`, Homebrew `share/fonts`, MacTeX/TeX Live
   (`/usr/local/texlive/<year>/texmf-dist/…/tex-gyre`, newest year first;
   `/Library/TeX/Root/texmf-dist/…/tex-gyre`);
4. the macOS font folders `~/Library/Fonts` and `/Library/Fonts`, with the URW names
   (`.otf`, `.t1`, `.pfb`, `.ttf`) then the TeX Gyre names (`.otf`);
5. **the macOS system fonts** (task 9.r7): `/System/Library/Fonts/Helvetica.ttc`, `Times.ttc`,
   `Courier.ttc` — the face is chosen by its PostScript name (`Helvetica-BoldOblique`, …,
   `Core.Font.TrueType.faceByPsName?`); a collection without that name is skipped, never
   guessed — then Arial, Times New Roman, Courier New (`Supplemental/` or `/Library/Fonts`),
   `Symbol.ttf` (then `Apple Symbols.ttf`) and `ZapfDingbats.ttf`.

Every directory is a fixed path below the search root (`SearchConfig.root`, `/` in use; tests
use a temporary directory) or one level of a sorted listing of a fixed directory; nothing is
searched recursively. `SAFEPDF_SUBST_FONTS=0` disables substitutes (non-embedded text
unpainted, the behaviour before task 7.7); `SAFEPDF_SUBST_FONTS=report` prints, on stderr,
the file and face chosen for each standard-14 name and whether it parses. A face with no file,
an unreadable file or one larger than `maxFontFileBytes` is simply absent: its text stays
unpainted, nothing fails.
-/

namespace SafePdf.Shell.Fonts

open SafePdf SafePdf.Core
open SafePdf.Core.Font (Std14)

/-- Largest font file read (bytes). macOS's `Helvetica.ttc` is a few MB. -/
def maxFontFileBytes : Nat := 32 <<< 20

/-- The PostScript name of a standard-14 face (also the face names in macOS's `Helvetica.ttc`,
`Times.ttc` and `Courier.ttc`). -/
def stdName : Std14 → String
  | .helvetica => "Helvetica"
  | .helveticaBold => "Helvetica-Bold"
  | .helveticaOblique => "Helvetica-Oblique"
  | .helveticaBoldOblique => "Helvetica-BoldOblique"
  | .timesRoman => "Times-Roman"
  | .timesBold => "Times-Bold"
  | .timesItalic => "Times-Italic"
  | .timesBoldItalic => "Times-BoldItalic"
  | .courier => "Courier"
  | .courierBold => "Courier-Bold"
  | .courierOblique => "Courier-Oblique"
  | .courierBoldOblique => "Courier-BoldOblique"
  | .symbol => "Symbol"
  | .zapfDingbats => "ZapfDingbats"

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

/-! ## Candidates -/

/-- How the face is picked inside a candidate file. -/
inductive Pick where
  /-- The file's only (first) face: Type 1, OpenType, a single TrueType font. -/
  | first
  /-- The face of a TrueType collection with this PostScript name (skipped when absent). -/
  | psName (n : String)
  deriving BEq, Repr

/-- A file that may hold a face. -/
structure Candidate where
  /-- The file. -/
  path : System.FilePath
  /-- Which face of it. -/
  pick : Pick := .first
  deriving BEq, Repr

/-- Where to look (paths below `root`; `/` in use). -/
structure SearchConfig where
  /-- Prefix of every system path (`/`; a temporary directory in tests). -/
  root : System.FilePath := "/"
  /-- The home directory (for `~/Library/Fonts`), if known. -/
  home : Option System.FilePath := none
  /-- The directories of `$SAFEPDF_FONT_DIR` (not below `root`). -/
  userDirs : List String := []
  /-- The version directories found under each Ghostscript `share/ghostscript` directory and
  the year directories under `/usr/local/texlive` (filled by `listVersions`). -/
  versions : List (String × List String) := []

/-- `root / p` for a path `p` written without its leading `/`. -/
def SearchConfig.at (c : SearchConfig) (p : String) : System.FilePath :=
  let r := String.ofList (c.root.toString.toList.reverse.dropWhile (· == '/')).reverse
  System.FilePath.mk (r ++ "/" ++ p)

/-- URW base-35 system directories (below the root), with the extensions to try in each. -/
def urwDirs : List (String × List String) :=
  [ ("usr/share/fonts/type1/urw-base35", [".t1"]),
    ("usr/share/fonts/X11/Type1", [".pfb"]),
    ("usr/share/fonts/opentype/urw-base35", [".otf"]) ]

/-- Ghostscript `share/ghostscript` directories (below the root): Homebrew on Apple silicon,
Homebrew on Intel / `/usr/local` builds, the system's. -/
def ghostscriptDirs : List String :=
  ["opt/homebrew/share/ghostscript", "usr/local/share/ghostscript", "usr/share/ghostscript"]

/-- TeX Live installation roots whose year directories are listed. -/
def texliveDirs : List String := ["usr/local/texlive"]

/-- The TeX Gyre directory inside a `texmf-dist`. -/
def texGyreSub : String := "texmf-dist/fonts/opentype/public/tex-gyre"

/-- Fixed TeX Gyre system directories (below the root). -/
def texGyreDirs : List String :=
  [ "usr/share/texmf/fonts/opentype/public/tex-gyre", "usr/share/fonts/opentype/texgyre",
    "opt/homebrew/share/fonts", "usr/local/share/fonts",
    "Library/TeX/Root/" ++ texGyreSub ]

/-- Extensions tried in `$SAFEPDF_FONT_DIR`. -/
def userExts : List String := [".t1", ".pfb", ".pfa", ".otf", ""]

/-- Extensions of URW names tried in the macOS font folders. -/
def libraryExts : List String := [".otf", ".t1", ".pfb", ".ttf"]

/-- **The macOS system fonts** of a face, in order (paths below the root): the face of the
system collection with the standard PostScript name, then Monotype's metric-compatible
Arial / Times New Roman / Courier New (`Supplemental/` since macOS 10.15, `/Library/Fonts`
before), `Symbol.ttf` then `Apple Symbols.ttf`, `ZapfDingbats.ttf`. -/
def macSystem (f : Std14) : List Candidate :=
  let sys := "System/Library/Fonts/"
  let ttc (file : String) : List Candidate :=
    [{ path := System.FilePath.mk (sys ++ file), pick := .psName (stdName f) }]
  let ttf (file : String) : List Candidate :=
    [sys ++ "Supplemental/" ++ file, "Library/Fonts/" ++ file, sys ++ file].map
      fun p => { path := System.FilePath.mk p }
  match f with
  | .helvetica => ttc "Helvetica.ttc" ++ ttf "Arial.ttf"
  | .helveticaBold => ttc "Helvetica.ttc" ++ ttf "Arial Bold.ttf"
  | .helveticaOblique => ttc "Helvetica.ttc" ++ ttf "Arial Italic.ttf"
  | .helveticaBoldOblique => ttc "Helvetica.ttc" ++ ttf "Arial Bold Italic.ttf"
  | .timesRoman => ttc "Times.ttc" ++ ttf "Times New Roman.ttf"
  | .timesBold => ttc "Times.ttc" ++ ttf "Times New Roman Bold.ttf"
  | .timesItalic => ttc "Times.ttc" ++ ttf "Times New Roman Italic.ttf"
  | .timesBoldItalic => ttc "Times.ttc" ++ ttf "Times New Roman Bold Italic.ttf"
  | .courier => ttc "Courier.ttc" ++ ttf "Courier New.ttf"
  | .courierBold => ttc "Courier.ttc" ++ ttf "Courier New Bold.ttf"
  | .courierOblique => ttc "Courier.ttc" ++ ttf "Courier New Italic.ttf"
  | .courierBoldOblique => ttc "Courier.ttc" ++ ttf "Courier New Bold Italic.ttf"
  | .symbol => ttf "Symbol.ttf" ++ ttf "Apple Symbols.ttf"
  | .zapfDingbats => ttf "ZapfDingbats.ttf"

/-- The listed sub-directories of `dir` in `c.versions`. -/
def SearchConfig.versionsOf (c : SearchConfig) (dir : String) : List String :=
  (c.versions.lookup dir).getD []

/-- **The candidate files of a face**, in search order (see the module doc). Pure: the
directory listings it needs are in `c.versions`. -/
def candidates (c : SearchConfig) (f : Std14) : List Candidate :=
  let names := urwName f :: (texGyreName f).toList
  let plain (ps : List System.FilePath) : List Candidate := ps.map fun p => { path := p }
  let user := plain <| c.userDirs.flatMap fun d => names.flatMap fun n =>
    userExts.map fun e => System.FilePath.mk d / (n ++ e)
  let urw := plain <| urwDirs.flatMap fun (d, es) => es.map fun e => c.at d / (urwName f ++ e)
  let gs := plain <| ghostscriptDirs.flatMap fun d =>
    (c.at d / "Resource/Font" / urwName f) ::
      (c.versionsOf d).map fun (v : String) => c.at d / v / "Resource/Font" / urwName f
  let gyreDirs := texGyreDirs.map c.at ++ texliveDirs.flatMap fun d =>
    (c.versionsOf d).map fun (v : String) => c.at d / v / texGyreSub
  let gyre := match texGyreName f with
    | some n => plain (gyreDirs.map fun d => d / (n ++ ".otf"))
    | none => []
  let libs := (c.home.map (· / "Library/Fonts")).toList ++ [c.at "Library/Fonts"]
  let lib := plain <| libs.flatMap fun d =>
    libraryExts.map (fun e => d / (urwName f ++ e)) ++
      (texGyreName f).toList.map fun n => d / (n ++ ".otf")
  let mac := (macSystem f).map fun k => { k with path := c.at k.path.toString }
  user ++ urw ++ gs ++ gyre ++ lib ++ mac

/-! ## Reading -/

/-- Version-directory names in descending order (`10.05.1` before `10.04.0`, `2025` before
`2024`), comparing dot- or dash-separated parts as numbers (words sort below numbers, so a
non-version name such as `fonts` comes last). -/
def versionKey (s : String) : List (Nat ⊕ String) :=
  let parts := (s.splitOn ".").flatMap fun p => p.splitOn "-"
  parts.map fun p => match p.toNat? with
    | some n => .inl n
    | none => .inr p

/-- `a` is an older version than `b` (lexicographic on `versionKey`, words below numbers). -/
def versionLt : List (Nat ⊕ String) → List (Nat ⊕ String) → Bool
  | [], _ :: _ => true
  | _, [] => false
  | .inl a :: as, .inl b :: bs => a < b || (a == b && versionLt as bs)
  | .inl _ :: _, .inr _ :: _ => false
  | .inr _ :: _, .inl _ :: _ => true
  | .inr a :: as, .inr b :: bs => a < b || (a == b && versionLt as bs)

/-- Sort version names, newest first. -/
def sortVersions (vs : List String) : List String :=
  (vs.toArray.qsort fun a b => versionLt (versionKey b) (versionKey a)).toList

#guard sortVersions ["9.56.1", "10.04.0", "10.05.1", "fonts"] == ["10.05.1", "10.04.0", "9.56.1", "fonts"]
#guard sortVersions ["2023", "2025", "2024"] == ["2025", "2024", "2023"]

/-- Most entries of a listed directory kept. -/
def maxListed : Nat := 32

/-- The sub-directory names of `dir` (none when unreadable), newest version first, at most
`maxListed`. -/
def listVersionDirs (dir : System.FilePath) : IO (List String) := do
  try
    let es ← dir.readDir
    let mut out := []
    for e in es do
      if (← e.path.isDir) then out := e.fileName :: out
    return (sortVersions out).take maxListed
  catch _ => return []

/-- Fill `c.versions`: list the Ghostscript and TeX Live directories below the root. -/
def listVersions (c : SearchConfig) : IO SearchConfig := do
  let mut vs := []
  for d in ghostscriptDirs ++ texliveDirs do
    vs := vs ++ [(d, ← listVersionDirs (c.at d))]
  return { c with versions := vs }

/-- The bytes of a regular file of at most `maxFontFileBytes`, if readable. -/
def readFont (p : System.FilePath) : IO (Option ByteArray) := do
  try
    let md ← p.metadata
    if md.type != .file then return none
    -- The shared capped read (task 12.1): a font file that grows past the cap is absent.
    match ← Read.readFile p maxFontFileBytes .inputBytes with
    | .ok b => return some b
    | .error _ => return none
  catch _ => return none

/-- A file read once per search (macOS's three collections serve four faces each). -/
abbrev FileCache := List (System.FilePath × Option ByteArray)

/-- Read through the cache. -/
def readCached (cache : FileCache) (p : System.FilePath) : IO (Option ByteArray × FileCache) := do
  match cache.lookup p with
  | some b => return (b, cache)
  | none =>
    let b ← readFont p
    return (b, (p, b) :: cache)

/-- A face found: the standard-14 face, the file, its bytes and the face index in the file. -/
structure Found where
  /-- The standard-14 face. -/
  face : Std14
  /-- The file. -/
  path : System.FilePath
  /-- Its contents. -/
  bytes : ByteArray
  /-- The face index (in a TrueType collection; `0` otherwise). -/
  index : Nat

/-- The first candidate that is readable and, for `.psName`, has a face of that name. -/
def firstFace (f : Std14) : List Candidate → FileCache → IO (Option Found × FileCache)
  | [], cache => return (none, cache)
  | k :: rest, cache => do
    let (b, cache) ← readCached cache k.path
    match b with
    | none => firstFace f rest cache
    | some b =>
      match k.pick with
      | .first => return (some ⟨f, k.path, b, 0⟩, cache)
      | .psName n =>
        match Font.TrueType.faceByPsName? b n with
        | some i => return (some ⟨f, k.path, b, i⟩, cache)
        | none => firstFace f rest cache

/-- **Find the substitute faces** for configuration `c` (`c.versions` filled by
`listVersions`): each face with the file and face index found for it. -/
def findFacesIn (c : SearchConfig) : IO (List Found) := do
  let mut cache : FileCache := []
  let mut out := []
  for f in allFaces do
    let (r, cache') ← firstFace f (candidates c f) cache
    cache := cache'
    if let some x := r then out := out ++ [x]
  return out

/-- The directories of `$SAFEPDF_FONT_DIR`. -/
def userDirs : IO (List String) := do
  match ← IO.getEnv "SAFEPDF_FONT_DIR" with
  | some d => return (d.splitOn ":").filter (!·.isEmpty)
  | none => return []

/-- The configuration in use: root `/`, `$HOME`, `$SAFEPDF_FONT_DIR`, listed versions. -/
def systemConfig : IO SearchConfig := do
  let home := (← IO.getEnv "HOME").filter (!·.isEmpty) |>.map System.FilePath.mk
  listVersions { home, userDirs := ← userDirs }

/-- **Find the substitute faces on this system**. Empty when `SAFEPDF_SUBST_FONTS=0`. -/
def findFaces : IO (List Found) := do
  if (← IO.getEnv "SAFEPDF_SUBST_FONTS") == some "0" then return []
  findFacesIn (← systemConfig)

/-- **Find the substitute font files**: each face with its file and contents (face indices
dropped; `findFaces` keeps them). Empty when `SAFEPDF_SUBST_FONTS=0`. -/
def findFiles : IO (List (Std14 × System.FilePath × ByteArray)) := do
  return (← findFaces).map fun x => (x.face, x.path, x.bytes)

/-- The substitute table of the faces found. -/
def tableOf (limits : Limits) (fs : List Found) : Raster.Subst.SubstFonts :=
  Raster.Subst.SubstFonts.ofFaces limits (fs.map fun x => (x.face, x.bytes, x.index))

/-- One line per standard-14 face: the file and face index chosen and whether it parses. -/
def reportLines (limits : Limits) (fs : List Found) : List String :=
  allFaces.map fun f =>
    match fs.find? (·.face == f) with
    | some x =>
      let ok := (Raster.Subst.Program.parseFace limits f x.bytes x.index).isSome
      s!"subst: {stdName f} <- {x.path} #{x.index}{if ok then "" else " (does not parse)"}"
    | none => s!"subst: {stdName f} <- none (unpainted)"

/-- **The substitute table** for the core renderer (`Core.Raster.Glyph.renderDocPage …
(subst := …)`): the faces found, parsed lazily under `limits`. With
`SAFEPDF_SUBST_FONTS=report` the choice is printed on stderr first. -/
def loadSubstFonts (limits : Limits) : IO Raster.Subst.SubstFonts := do
  let fs ← findFaces
  if (← IO.getEnv "SAFEPDF_SUBST_FONTS") == some "report" then
    for l in reportLines limits fs do IO.eprintln l
  return tableOf limits fs

end SafePdf.Shell.Fonts
