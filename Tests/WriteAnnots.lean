import SafePdf
import SafePdf.Core.Write.Annots
import Tests.RasterSubst

/-!
# Annotation dictionaries for user marks (task 9.5b)

Plan.md §4 S8/C7, §6 Phase 9 "Persistence — annotations inside the PDF". Fixture:
`Tests/fixtures-write/annots/text.pdf` (`generate.py`): two pages of black Helvetica text,
page 2 with an existing `/Square`.

Marks (`Core.Write.Annots.Mark`) — a yellow highlight over the first line, a pink highlight
with a non-ASCII comment (pdf.js "highlight with comment": `/Contents` + `/Popup`), a green
note at a point with a non-ASCII text, and on page 2 a note anchored to a selection and a
half-transparent blue highlight — go through `Annots.build` and
`Write.Incremental.writeAnnots` (`Annots.writeMarks`); then:

* the result reopens **strictly** (`Open.openFile`, not repaired) and through `Api`;
* `Api.pageAnnotations` reads back `/NM`, `/Subtype`, `/QuadPoints` (rounded to 1/1000 as
  written), `/Contents` (incl. UTF-16 with surrogate pairs); the raw dictionaries carry `/C`,
  `/P` (the page), `/F 4`, `/M`; `/Popup` ↔ `/Parent` link highlight and popup; `/AP /N` is a
  form XObject stream (`/BBox`, highlight resources with `/BM /Multiply`); the old `/Square`
  of page 2 stays first in `/Annots`;
* **rendering** with our rasterizer (`Api.renderPage`, zoom 2) and with `mutool draw -r 144`
  (skipped when `mutool` is missing): inside the highlight quad the paper turns the
  highlight colour and the text pixels that were dark stay dark (multiply); the note icon
  shows its fill colour;
* `qpdf --check` exits 0 (skipped when `qpdf` is missing);
* refusals: a page index out of range, a highlight without quads.

Environment: `SAFEPDF_WRITEANNOTS_CORPUS=FILE` also writes a highlight over the first text
line of page 1 of `FILE` plus a note, and checks reopen, read-back and our render;
`SAFEPDF_WRITE_OUT=DIR` keeps the written files (`DIR/annots-*.pdf`).
-/

namespace SafePdf.Tests.WriteAnnots

open SafePdf SafePdf.Core
open SafePdf.Core.Write.Annots
open SafePdf.Tests.RasterSubst (Rgb parsePpm)

/-- Fixture. -/
def fixture : System.FilePath := "Tests" / "fixtures-write" / "annots" / "text.pdf"

/-- Report a failed check. -/
def check (what : String) (ok : Bool) (detail : String := "") : IO Nat := do
  if ok then return 0
  IO.println s!"  FAIL write-annots: {what} {detail}"
  return 1

/-- The date every test mark carries. -/
def date : String := "D:20261120120000Z"

/-- Pink comment (non-ASCII, a surrogate pair). -/
def comment : String := "Grüße – très bien 😀"

/-- Note text (non-ASCII). -/
def noteText : String := "Ünïcödé note\nsecond line"

/-- The marks of the fixture. -/
def marks : List Mark :=
  [ { page := 0, kind := .highlight, quads := [Quad.ofBox 38 114 210 136],
      rect := ⟨0, 0, 0, 0⟩, color := (1, 1, 152 / 255), id := 1, date := date },
    { page := 0, kind := .highlight, quads := [Quad.ofBox 38 56 (100 + 1 / 3) 72],
      rect := ⟨0, 0, 0, 0⟩, color := (1, 203 / 255, 230 / 255), id := 2, date := date,
      contents := comment, author := "Reader" },
    { page := 0, kind := .note, quads := [], rect := ⟨250, 160, 270, 180⟩,
      color := (83 / 255, 1, 188 / 255), id := 3, date := date, contents := noteText },
    { page := 1, kind := .note, quads := [Quad.ofBox 28 146 130 166],
      rect := ⟨132, 146, 152, 166⟩, color := (1, 1, 152 / 255), id := 4, date := date,
      contents := "anchored" },
    { page := 1, kind := .highlight, quads := [Quad.ofBox 28 146 130 166],
      rect := ⟨0, 0, 0, 0⟩, color := (128 / 255, 235 / 255, 1), opacity := 1 / 2, id := 5,
      date } ]

/-- The value a number reads back as after rounding to 1/1000. -/
def r3 (q : Rat) : Rat := Raster.Geom.decimalToRat (decRound 3 q)

/-- A raw annotation dictionary of the result, by `/NM`. -/
def rawByNm (doc : Doc.Doc) (lim : Limits) (page : Nat) (n : String) : Option Dict :=
  match doc.pages[page]? with
  | none => none
  | some p =>
    match Write.Incremental.annotsOf doc.file lim p.num p.gen with
    | .ok xs => xs.findSome? fun a => match a with
      | .ref k g => match doc.file.getObject lim k g with
        | .ok (.obj (.dict d)) =>
          if Dict.get? d kNM == some (.string (textBytes n)) then some d else none
        | _ => none
      | _ => none
    | .error _ => none

/-- The stream behind `/AP /N`. -/
def apStream (doc : Doc.Doc) (lim : Limits) (d : Dict) : Option Stream :=
  match Dict.get? d kAP with
  | some (.dict ap) => match Dict.get? ap (nm "N") with
    | some (.ref k g) => match doc.file.getObject lim k g with
      | .ok (.stream s) => some s
      | _ => none
    | _ => none
  | _ => none

/-- Whether `pat` occurs in `bs`. -/
def contains (bs pat : List UInt8) : Bool :=
  (List.range (bs.length + 1)).any fun i => (bs.drop i).take pat.length == pat

/-- Pixel statistics inside the page box `[x0, x1] × [y0, y1]` (page space, inset by
`inset` pixels) of a page `ph` points high at `z` pixels per point: (pixels, pixels close to
`rgb`, dark pixels, pixels that are near white). -/
def stats (m : Rgb) (z : Nat) (ph x0 y0 x1 y1 : Nat) (rgb : Nat × Nat × Nat) (inset := 2) :
    Nat × Nat × Nat × Nat := Id.run do
  let mut n := 0
  let mut col := 0
  let mut dark := 0
  let mut white := 0
  for y in [z * (ph - y1) + inset : z * (ph - y0) - inset] do
    for x in [z * x0 + inset : z * x1 - inset] do
      let r := m.at x y 0
      let g := m.at x y 1
      let b := m.at x y 2
      n := n + 1
      let near (a e : Nat) : Bool := a + 14 ≥ e && a ≤ e + 14
      if near r rgb.1 && near g rgb.2.1 && near b rgb.2.2 then col := col + 1
      if r < 90 && g < 90 && b < 90 then dark := dark + 1
      if r > 240 && g > 240 && b > 240 then white := white + 1
  return (n, col, dark, white)

/-- Our render of page `i` as RGB at zoom 2. -/
def ours (bytes : ByteArray) (i : Nat) : Option Rgb :=
  match Api.openBytes bytes with
  | .ok d => match Api.renderPage d i 2 with
    | .ok img => some (Rgb.ofImage img)
    | .error _ => none
  | .error _ => none

/-- `mutool draw -r 144` of page `i + 1` as a PPM, if `mutool` runs. -/
def mutool (pdf : System.FilePath) (i : Nat) : IO (Option Rgb) := do
  try
    let (h, tmp) ← IO.FS.createTempFile
    h.flush
    let out ← IO.Process.output
      { cmd := "mutool", args := #["draw", "-q", "-r", "144", "-c", "rgb", "-F", "pnm", "-o",
          tmp.toString, pdf.toString, toString (i + 1)] }
    let b ← IO.FS.readBinFile tmp
    IO.FS.removeFile tmp
    if out.exitCode != 0 then return none
    return parsePpm b
  catch _ => return none

/-- `qpdf --check` exit code, if `qpdf` runs. -/
def qpdfCheck (pdf : System.FilePath) : IO (Option UInt32) := do
  try
    let out ← IO.Process.output { cmd := "qpdf", args := #["--check", pdf.toString] }
    return some out.exitCode
  catch _ => return none

/-- The highlight / multiply checks on one rendering `after` (and the original `before`).
Returns the failures. -/
def renderChecks (who : String) (before after : Rgb) : IO Nat := do
  let mut f := 0
  -- mark 1: yellow quad over "Highlight me please" (38..210 × 114..136)
  let (n, yel, dark, white) := stats after 2 200 38 114 210 136 (255, 255, 152)
  let (_, _, dark0, _) := stats before 2 200 38 114 210 136 (255, 255, 152)
  f := f + (← check s!"{who}: highlight colour fills the quad" (yel * 2 ≥ n)
    s!"{yel}/{n} yellow")
  f := f + (← check s!"{who}: no white paper left in the quad" (white * 50 ≤ n)
    s!"{white}/{n} white")
  f := f + (← check s!"{who}: text under the highlight stays dark (multiply)"
    (dark0 > 0 && dark * 10 ≥ dark0 * 8) s!"dark {dark0} → {dark}")
  -- mark 3: green note icon (250..270 × 160..180)
  let (n3, green, _, _) := stats after 2 200 250 160 270 180 (83, 255, 188) 4
  f := f + (← check s!"{who}: note icon shows its colour" (green * 4 ≥ n3)
    s!"{green}/{n3} green")
  -- outside the marks nothing changed (a blank strip at the bottom)
  let (n0, _, _, w0) := stats after 2 200 0 0 300 30 (0, 0, 0) 0
  f := f + (← check s!"{who}: blank paper elsewhere" (w0 == n0) s!"{w0}/{n0}")
  return f

/-- Read-back checks of the fixture result. -/
def readBack (out : ByteArray) : IO Nat := do
  let lim := Limits.default
  let mut f := 0
  match Open.openFile lim out with
  | .error _ => return (← check "strict reopen" false)
  | .ok od => f := f + (← check "strict reopen not repaired" (!od.repaired))
  match Api.openBytes out with
  | .error e => return f + (← check "Api.openBytes" false e.message)
  | .ok d =>
    match Api.pageAnnotations d 0, Api.pageAnnotations d 1 with
    | .ok a0, .ok a1 =>
      let names (as : List Api.Annotation) := as.filterMap (·.name)
      f := f + (← check "page 1 names"
        (names a0 == ["safepdf-mark-1", "safepdf-mark-2", "safepdf-mark-2-popup",
          "safepdf-mark-3"]) (toString (names a0)))
      f := f + (← check "page 2: old /Square first, then the marks"
        ((a1.map (·.subtype)) == ["Square", "Text", "Highlight"] &&
          names a1 == ["safepdf-mark-4", "safepdf-mark-5"]) (toString (a1.map (·.subtype))))
      let byName (as : List Api.Annotation) (n : String) := as.find? (·.name == some n)
      match byName a0 "safepdf-mark-1", byName a0 "safepdf-mark-2", byName a0 "safepdf-mark-3" with
      | some h1, some h2, some n3 =>
        f := f + (← check "highlight subtype/flags" (h1.subtype == "Highlight" && h1.flags == 4))
        f := f + (← check "highlight /QuadPoints round trip"
          (h1.quadPoints == [38, 136, 210, 136, 38, 114, 210, 114]) (toString h1.quadPoints))
        f := f + (← check "quad rounded to 1/1000"
          (h2.quadPoints == [38, 72, r3 (100 + 1 / 3), 72, 38, 56, r3 (100 + 1 / 3), 56]))
        f := f + (← check "highlight /Rect = union of quads"
          (h1.rect == ⟨38, 114, 210, 136⟩) (reprStr h1.rect))
        f := f + (← check "comment (UTF-16) round trip" (h2.contents == some comment)
          (reprStr h2.contents))
        f := f + (← check "author" (h2.author == some "Reader"))
        f := f + (← check "highlight without comment has no /Contents" (h1.contents == none))
        f := f + (← check "note subtype + contents" (n3.subtype == "Text" &&
          n3.contents == some noteText) (reprStr n3.contents))
        f := f + (← check "note /Rect" (n3.rect == ⟨250, 160, 270, 180⟩))
      | _, _, _ => f := f + (← check "page 1 marks found" false)
      -- raw dictionaries
      let doc := d.doc
      let pageRef (i : Nat) : Option PdfObject := doc.pages[i]?.map fun p => .ref p.num p.gen
      match rawByNm doc lim 0 "safepdf-mark-1", rawByNm doc lim 0 "safepdf-mark-2",
          rawByNm doc lim 0 "safepdf-mark-2-popup", rawByNm doc lim 0 "safepdf-mark-3",
          rawByNm doc lim 1 "safepdf-mark-5" with
      | some h1, some h2, some pp, some n3, some h5 =>
        f := f + (← check "/C of the highlight"
          (Dict.get? h1 kC == some (colorObj (1, 1, 152 / 255))))
        f := f + (← check "/C value" (Dict.get? h1 kC ==
          some (.array [.real ⟨1, 0⟩, .real ⟨1, 0⟩, .real ⟨5961, 4⟩])))
        f := f + (← check "/P is the page" (Dict.get? h1 (nm "P") == pageRef 0 &&
          Dict.get? n3 (nm "P") == pageRef 0 && Dict.get? h5 (nm "P") == pageRef 1))
        f := f + (← check "/M is the caller's date" (Dict.get? h1 (nm "M") ==
          some (.string date.toUTF8.toList)))
        f := f + (← check "no /CA at full opacity" (Dict.get? h1 (nm "CA") == none))
        f := f + (← check "/CA at half opacity"
          (Dict.get? h5 (nm "CA") == some (.real ⟨5, 1⟩)))
        f := f + (← check "/Name /Comment, /Open false on the note"
          (Dict.get? n3 (nm "Name") == some (.name (nm "Comment")) &&
            Dict.get? n3 (nm "Open") == some (.bool false)))
        -- popup linking (pdf.js "highlight with comment")
        let popupRef := Dict.get? h2 (nm "Popup")
        let parentRef := Dict.get? pp (nm "Parent")
        let linked := match popupRef, parentRef with
          | some (.ref pn _), some (.ref hn _) =>
            (match doc.file.getObject lim pn 0, doc.file.getObject lim hn 0 with
              | .ok (.obj (.dict p')), .ok (.obj (.dict h')) => p' == pp && h' == h2
              | _, _ => false)
          | _, _ => false
        f := f + (← check "/Popup ↔ /Parent link" linked)
        f := f + (← check "popup subtype /Open false" (Dict.get? pp kSubtype ==
          some (.name (nm "Popup")) && Dict.get? pp (nm "Open") == some (.bool false)))
        -- appearance streams
        match apStream doc lim h1, apStream doc lim n3 with
        | some s1, some s3 =>
          f := f + (← check "highlight AP is a form with /BBox = /Rect"
            (Dict.get? s1.dict kSubtype == some (.name (nm "Form")) &&
              Dict.get? s1.dict (nm "BBox") == Dict.get? h1 kRect))
          f := f + (← check "highlight AP resources: /BM /Multiply"
            (contains (Print.printObj (.dict s1.dict)) (ascii "/BM /Multiply")))
          f := f + (← check "highlight AP content fills the quad"
            (contains s1.data.toList (ascii "38. 136. m")))
          f := f + (← check "note AP is a form with /BBox [0 0 20 20]"
            (Dict.get? s3.dict (nm "BBox") == some (.array [.int 0, .int 0, .int 20, .int 20])))
        | _, _ => f := f + (← check "appearance streams resolve" false)
      | _, _, _, _, _ => f := f + (← check "raw annotation dictionaries" false)
    | _, _ => f := f + (← check "pageAnnotations" false)
    return f

/-- Write `out` to a temporary file (or `SAFEPDF_WRITE_OUT/name`); returns the path and
whether it is temporary. -/
def place (name : String) (out : ByteArray) : IO (System.FilePath × Bool) := do
  match ← IO.getEnv "SAFEPDF_WRITE_OUT" with
  | some d =>
    IO.FS.createDirAll d
    let p := System.FilePath.mk d / name
    IO.FS.writeBinFile p out
    return (p, false)
  | none =>
    let (h, tmp) ← IO.FS.createTempFile
    h.flush
    IO.FS.writeBinFile tmp out
    return (tmp, true)

/-- External checks on a written file: `qpdf --check`, and `mutool draw` render checks
against the original (`orig`). -/
def external (name : String) (orig : System.FilePath) (out : ByteArray)
    (renderCheck : Bool) : IO Nat := do
  let (path, tmp) ← place name out
  let mut f := 0
  match ← qpdfCheck path with
  | some code => f := f + (← check s!"{name}: qpdf --check" (code == 0) s!"exit {code}")
  | none => IO.println "  write-annots: qpdf not found, skipped"
  if renderCheck then
    match ← mutool orig 0, ← mutool path 0 with
    | some b, some a => f := f + (← renderChecks "mutool" b a)
    | _, _ => IO.println "  write-annots: mutool not found, render check skipped"
  if tmp then IO.FS.removeFile path
  return f

/-- The corpus end-to-end run on `FILE`: a highlight over the first text line of page 1
and a note beside it. -/
def corpus (file : String) : IO Nat := do
  let bytes ← IO.FS.readBinFile file
  match Api.openBytes bytes with
  | .error e => check s!"corpus {file}: open" false e.message
  | .ok d =>
    match Api.pageText d 0 with
    | .error _ => check s!"corpus {file}: text" false
    | .ok pt =>
      match pt.lines.toList.find? (fun l => l.text.length ≥ 10) with
      | none => check s!"corpus {file}: a text line" false
      | some ln =>
        let b := ln.box
        let ms : List Mark :=
          [ { page := 0, kind := .highlight, quads := [Quad.ofBox b.llx b.lly b.urx b.ury],
              rect := ⟨0, 0, 0, 0⟩, color := (1, 1, 152 / 255), id := 1, date := date,
              contents := "corpus comment ✓" },
            { page := 0, kind := .note, quads := [Quad.ofBox b.llx b.lly b.urx b.ury],
              rect := ⟨b.urx, b.ury - 20, b.urx + 20, b.ury⟩, color := (83 / 255, 1, 188 / 255),
              id := 2, date := date, contents := "note ✓" } ]
        match writeMarks Limits.default d.doc ms with
        | .error e => check s!"corpus {file}: writeMarks" false (Api.Error.message (.pdf e))
        | .ok out =>
          let mut f := 0
          match Api.openBytes out with
          | .error e => f := f + (← check s!"corpus {file}: reopen" false e.message)
          | .ok d' =>
            match Api.pageAnnotations d' 0 with
            | .ok as =>
              let mine := as.filter fun a => (a.name.getD "").startsWith nmPrefix
              f := f + (← check s!"corpus {file}: marks read back"
                ((mine.map (·.name.getD "")) ==
                  ["safepdf-mark-1", "safepdf-mark-1-popup", "safepdf-mark-2"] &&
                  (mine.find? (·.subtype == "Text")).bind (·.contents) == some "note ✓"))
            | .error _ => f := f + (← check s!"corpus {file}: annotations" false)
            match ours out 0 with
            | some img =>
              -- the line box's middle row: yellow paper somewhere on it
              let y := 2 * ((d'.doc.pages[0]?.map (fun p =>
                Raster.Geom.decimalToRat p.cropBox.ury)).getD 0 - (b.lly + b.ury) / 2)
              let yi := y.floor.toNat
              let mut yel := 0
              for x in [(2 * b.llx).floor.toNat : (2 * b.urx).floor.toNat] do
                if img.at x yi 0 > 240 && img.at x yi 1 > 240 && img.at x yi 2 < 175 &&
                  img.at x yi 2 > 130 then yel := yel + 1
              f := f + (← check s!"corpus {file}: highlight visible in our render" (yel > 10)
                s!"{yel} yellow pixels")
            | none => f := f + (← check s!"corpus {file}: render" false)
          f := f + (← external "annots-corpus.pdf" file out false)
          IO.println s!"  write-annots corpus {file}: {if f == 0 then "ok" else "FAIL"}"
          return f

/-- **Suite entry point.** -/
def run : IO Nat := do
  let lim := Limits.default
  let bytes ← IO.FS.readBinFile fixture
  let mut f := 0
  match Api.openBytes bytes with
  | .error e => return (← check "open fixture" false e.message)
  | .ok d =>
    -- build: shapes and numbering
    match build d.doc marks with
    | .error _ => f := f + (← check "build" false)
    | .ok (ms, aux) =>
      f := f + (← check "build: pages in first-occurrence order" (ms.map (·.1) == [0, 1]))
      f := f + (← check "build: one appearance stream per mark" (aux.length == marks.length))
      f := f + (← check "build: dictionaries per page (popup for the comment)"
        (ms.map (·.2.length) == [4, 2]))
    -- refusals
    let isErr (r : Except Error ByteArray) : Bool := match r with
      | .error _ => true
      | .ok _ => false
    f := f + (← check "refuse page out of range" (isErr (writeMarks lim d.doc
      [{ page := 9, kind := .note, quads := [], rect := ⟨0, 0, 20, 20⟩, color := (1, 1, 0),
         id := 9, date := date }])))
    f := f + (← check "refuse highlight without quads" (isErr (writeMarks lim d.doc
      [{ page := 0, kind := .highlight, quads := [], rect := ⟨0, 0, 20, 20⟩,
         color := (1, 1, 0), id := 9, date := date }])))
    match writeMarks lim d.doc marks with
    | .error e => f := f + (← check "writeMarks" false (Api.Error.message (.pdf e)))
    | .ok out =>
      f := f + (← check "original is a prefix" (out.extract 0 bytes.size == bytes))
      f := f + (← readBack out)
      match ours bytes 0, ours out 0 with
      | some b, some a => f := f + (← renderChecks "ours" b a)
      | _, _ => f := f + (← check "our render" false)
      -- page 2: half-transparent blue over the anchored note's line
      match ours out 1 with
      | some a =>
        let (n, blue, _, _) := stats a 2 200 28 146 130 166 (192, 245, 255)
        f := f + (← check "ours: half-transparent highlight" (blue * 3 ≥ n) s!"{blue}/{n}")
      | none => f := f + (← check "our render page 2" false)
      f := f + (← external "annots-text.pdf" fixture out true)
      -- a second update on top of the first
      match Api.openBytes out with
      | .ok d2 =>
        let more : List Mark :=
          [{ page := 0, kind := .note, quads := [], rect := ⟨10, 10, 30, 30⟩,
             color := (1, 79 / 255, 95 / 255), id := 6, date := date,
             contents := "second save" }]
        match writeMarks lim d2.doc more with
        | .ok out2 =>
          match Api.openBytes out2 with
          | .ok d3 => match Api.pageAnnotations d3 0 with
            | .ok as => f := f + (← check "second update keeps the first marks"
                ((as.filterMap (·.name)).length == 5))
            | .error _ => f := f + (← check "second update annotations" false)
          | .error e => f := f + (← check "second update reopen" false e.message)
        | .error e => f := f + (← check "second update" false (Api.Error.message (.pdf e)))
      | .error e => f := f + (← check "reopen for second update" false e.message)
  match ← IO.getEnv "SAFEPDF_WRITEANNOTS_CORPUS" with
  | some file => f := f + (← corpus file)
  | none => pure ()
  return f

end SafePdf.Tests.WriteAnnots
