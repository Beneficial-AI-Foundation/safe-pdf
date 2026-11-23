import SafePdf
import SafePdf.Core.Write.Annots
import Tests.RasterSubst
import SafePdf.Shell.App.Save

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

Encrypted documents (task 9.5f, `runEncrypted`): the same marks are written into the fixture
encrypted with RC4-40, RC4-128, AES-128, AES-256 and AES-256 with an xref stream
(`Tests/fixtures-write/encrypted/`, made by qpdf); the result passes every read-back and
render check above (our rasterizer and `mutool`), `qpdf --check`, keeps the file key, has no
mark string or appearance-stream content in the clear, and takes a second update.

Edits of saved marks (task 9.5g, writer rule W11, `runEdits`), on the plain fixture and on
the encrypted ones: after the first write, one update (`Annots.writeEdits`) recolours
highlight 1 and gives it a comment (a **new** popup object), recolours highlight 2 and
changes its comment (its popup **superseded**), edits note 3's text, **removes** highlight 5
(page 2) and adds a note 7. Checked: the earlier file is a byte prefix; strict reopen with
one more revision; page 1's `/Annots` is the old list in order (superseded references in
place) followed by note 7 and the new popup `safepdf-mark-1-popup-8` (rule A11), page 2's has
no highlight 5; the superseded objects keep their numbers and carry the new `/C`,
`/Contents`, `/M` and the old `/CreationDate`; the new popup's `/Parent` is highlight 1;
our render shows highlight 1 green and page 2 without the blue; `mutool` shows it green;
`qpdf --check`; no plaintext in an encrypted update. A third update on top drops highlight
2's comment: its popup reference leaves `/Annots`, `/Contents` and `/Popup` leave the
dictionary.

Free text and ink (task 9.9, rules A12–A15, `runEditors`), on the plain fixture and on every
encrypted one: page 2 gets a red free text with a non-WinAnsi character ("Text Box ✓", size
20), an opaque blue drawing (a three-point stroke and a one-point stroke, width 6) and a green
drawing at opacity 0.4. Checked: the original is a prefix; strict reopen not repaired; the raw
dictionaries (`/Subtype`, `/Contents` in UTF-16, `/DA`, `/Rect` = the Core layout, `/InkList`
one array per stroke with two numbers per point, `/BS /W`, `/C`, `/CA` only below 1, `/F 4`)
and appearance streams (Helvetica `/Helv` resource, the ✓ drawn as `\267`, round caps, `/R0
gs`); the shell's read-back (`Shell.App.Save.readMarks`) gives the same free text (text,
position, size, colour) and drawings (strokes, width, opacity, colour); our render (with the
system's substitute fonts; skipped without them) and `mutool draw` show red text pixels in
the text box, the blue stroke and the half-transparent green; `qpdf --check`; nothing of the
new strings in the clear when encrypted. Then one update moves and re-words the free text
(superseded under its own number, W11) and removes the green drawing: read back moved and
re-worded, the green gone, the blue kept; `qpdf --check`.

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
    -- A missing command does not throw: the spawned child exits 255. Probe `--version` first
    -- so a machine without qpdf (the CI `build` job) skips instead of failing.
    let probe ← IO.Process.output { cmd := "qpdf", args := #["--version"] }
    if probe.exitCode != 0 then return none
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
            match ours bytes 0, ours out 0 with
            | some img0, some img =>
              -- multiply by the highlight colour (1, 1, 152/255): pixels whose red and green
              -- stay and whose blue drops to 152/255 of the original. Compared with the
              -- original render, anywhere on the page, so it holds on coloured paper, under
              -- /Rotate and with any CropBox origin (task 9.5f: NTSB headers, AAR0501).
              let mut yel := 0
              if img0.w == img.w && img0.h == img.h then
                for y in [0:img.h] do
                  for x in [0:img.w] do
                    let b0 := img0.at x y 2
                    let near (a e : Nat) : Bool := a + 8 ≥ e && a ≤ e + 8
                    if b0 > 60 && near (img.at x y 0) (img0.at x y 0) &&
                        near (img.at x y 1) (img0.at x y 1) &&
                        near (img.at x y 2) (b0 * 152 / 255) then
                      yel := yel + 1
              f := f + (← check s!"corpus {file}: highlight visible in our render" (yel > 10)
                s!"{yel} multiplied pixels")
            | _, _ => f := f + (← check s!"corpus {file}: render" false)
          f := f + (← external "annots-corpus.pdf" file out false)
          IO.println s!"  write-annots corpus {file}: {if f == 0 then "ok" else "FAIL"}"
          return f

/-- The `/Annots` reference and dictionary of our annotation named `n` on page `page`. -/
def refByNm (doc : Doc.Doc) (lim : Limits) (page : Nat) (n : String) :
    Option ((Nat × Nat) × Dict) :=
  match doc.pages[page]? with
  | none => none
  | some p =>
    match Write.Incremental.annotsOf doc.file lim p.num p.gen with
    | .ok xs => xs.findSome? fun a => match a with
      | .ref k g => match doc.file.getObject lim k g with
        | .ok (.obj (.dict d)) =>
          if Dict.get? d kNM == some (.string (textBytes n)) then some ((k, g), d) else none
        | _ => none
      | _ => none
    | .error _ => none

/-- Our annotation names on page `i` of `out`, in `/Annots` order. -/
def namesOn (out : ByteArray) (i : Nat) : List String :=
  match Api.openBytes out with
  | .ok d => match Api.pageAnnotations d i with
    | .ok as => as.filterMap (·.name)
    | .error _ => []
  | .error _ => []

/-- The date of the edit updates. -/
def date2 : String := "D:20261121090000Z"

/-- **Edits of saved marks** (task 9.5g; see the module doc) on the written file `out1` of
`marks` into `orig` (`ctx` names the run; `enc`: the document is encrypted). -/
def runEdits (ctx : String) (orig : System.FilePath) (out1 : ByteArray) (enc : Bool) :
    IO Nat := do
  let lim := Limits.default
  let mut f := 0
  let .ok d1 := Api.openBytes out1 | return (← check s!"{ctx}: reopen" false)
  let get (n : String) (pg : Nat) := refByNm d1.doc lim pg n
  let (some (r1, _), some (r2, h2), some (r3, n3), some (r5, _), some (rp2, _)) :=
      (get "safepdf-mark-1" 0, get "safepdf-mark-2" 0, get "safepdf-mark-3" 0,
        get "safepdf-mark-5" 1, get "safepdf-mark-2-popup" 0)
    | return (← check s!"{ctx}: first write's annotations" false)
  let created := match Dict.get? n3 (nm "CreationDate") with
    | some (.string bs) => String.fromUTF8? ⟨bs.toArray⟩ |>.getD ""
    | _ => ""
  let find (i : Nat) : Mark := (marks.find? (·.id == i)).getD default
  let green : Rat × Rat × Rat := (83 / 255, 1, 188 / 255)
  let m1 := { (find 1) with color := green, contents := "now commented ✓" }
  let m1 := { m1 with commentId := some 8, date := date2, created := date }
  let m2 := { (find 2) with color := (128 / 255, 235 / 255, 1), contents := "changed comment" }
  let m2 := { m2 with date := date2, created := date }
  let m3 := { (find 3) with contents := "edited note", date := date2, created }
  let m7 : Mark := { page := 0, kind := .note, quads := [], rect := ⟨10, 10, 30, 30⟩,
                     color := (1, 79 / 255, 95 / 255), id := 7, date := date2,
                     contents := "added with the edits" }
  let es : EditSet :=
    { adds := [m7],
      sups := [⟨m1, r1, none⟩, ⟨m2, r2, some rp2⟩, ⟨m3, r3, none⟩],
      removes := removeMark 1 r5 none }
  let .ok out2 := writeEdits lim d1.doc es
    | return (← check s!"{ctx}: writeEdits" false)
  f := f + (← check s!"{ctx}: first revision is a prefix" (out2.extract 0 out1.size == out1))
  if enc then
    f := f + (← check s!"{ctx}: no plaintext /NM in the edit update"
      (!contains (out2.extract out1.size out2.size).toList (ascii "safepdf-mark")))
  match Open.openFile lim out1, Open.openFile lim out2 with
  | .ok o1, .ok o2 =>
    f := f + (← check s!"{ctx}: strict reopen, one more revision"
      (!o2.repaired && o2.revisions == o1.revisions + 1))
  | _, _ => f := f + (← check s!"{ctx}: strict reopen of the edit update" false)
  f := f + (← check s!"{ctx}: page 1 annotations after the edits"
    (namesOn out2 0 == ["safepdf-mark-1", "safepdf-mark-2", "safepdf-mark-2-popup",
      "safepdf-mark-3", "safepdf-mark-7", "safepdf-mark-1-popup-8"])
    (toString (namesOn out2 0)))
  f := f + (← check s!"{ctx}: highlight 5 removed from page 2"
    (namesOn out2 1 == ["safepdf-mark-4"]) (toString (namesOn out2 1)))
  let .ok d2 := Api.openBytes out2 | return f + (← check s!"{ctx}: Api reopen" false)
  let get2 (n : String) (pg : Nat) := refByNm d2.doc lim pg n
  match get2 "safepdf-mark-1" 0, get2 "safepdf-mark-2" 0, get2 "safepdf-mark-3" 0,
      get2 "safepdf-mark-1-popup-8" 0, get2 "safepdf-mark-2-popup" 0 with
  | some (q1, e1), some (q2, e2), some (q3, e3), some (qp1, p1), some (qp2, p2) =>
    f := f + (← check s!"{ctx}: superseded objects keep their numbers"
      (q1 == r1 && q2 == r2 && q3 == r3 && qp2 == rp2))
    f := f + (← check s!"{ctx}: new colour" (Dict.get? e1 kC == some (colorObj green)))
    f := f + (← check s!"{ctx}: comments"
      (Dict.get? e1 kContents == some (.string (textBytes "now commented ✓")) &&
       Dict.get? e2 kContents == some (.string (textBytes "changed comment")) &&
       Dict.get? e3 kContents == some (.string (textBytes "edited note"))))
    f := f + (← check s!"{ctx}: /Popup and /Parent link the new popup"
      (Dict.get? e1 (nm "Popup") == some (.ref qp1.1 qp1.2) &&
       Dict.get? p1 (nm "Parent") == some (.ref r1.1 r1.2) &&
       Dict.get? p2 (nm "Parent") == some (.ref r2.1 r2.2) &&
       Dict.get? e2 (nm "Popup") == some (.ref rp2.1 rp2.2)))
    f := f + (← check s!"{ctx}: /M new, /CreationDate kept"
      (Dict.get? e3 (nm "M") == some (asciiStr date2) &&
       Dict.get? e3 (nm "CreationDate") == some (asciiStr created) && !created.isEmpty &&
       Dict.get? h2 (nm "M") == some (asciiStr date)))
  | _, _, _, _, _ => f := f + (← check s!"{ctx}: edited annotations" false)
  -- renders: highlight 1 green (ours, mutool), page 2 without the blue highlight
  match ours out2 0 with
  | some a =>
    let (n, g, _, _) := stats a 2 200 38 114 210 136 (83, 255, 188)
    f := f + (← check s!"{ctx}: ours: recoloured highlight" (g * 2 ≥ n) s!"{g}/{n} green")
  | none => f := f + (← check s!"{ctx}: our render" false)
  match ours out2 1 with
  | some a =>
    let (n, blue, _, _) := stats a 2 200 28 146 130 166 (192, 245, 255)
    f := f + (← check s!"{ctx}: ours: removed highlight gone" (blue == 0) s!"{blue}/{n}")
  | none => f := f + (← check s!"{ctx}: our render page 2" false)
  let (path, tmp) ← place s!"annots-edit-{ctx}.pdf" out2
  match ← mutool path 0 with
  | some a =>
    let (n, g, _, _) := stats a 2 200 38 114 210 136 (83, 255, 188)
    f := f + (← check s!"{ctx}: mutool: recoloured highlight" (g * 2 ≥ n) s!"{g}/{n} green")
  | none => IO.println "  write-annots: mutool not found, edit render check skipped"
  if tmp then IO.FS.removeFile path
  f := f + (← external s!"annots-edit-{ctx}.pdf" orig out2 false)
  -- a third update: highlight 2 loses its comment (popup removed)
  let m2' := { m2 with contents := "", date := date2 }
  match writeEdits lim d2.doc { sups := [⟨m2', r2, some rp2⟩] } with
  | .error _ => f := f + (← check s!"{ctx}: third update" false)
  | .ok out3 =>
    f := f + (← check s!"{ctx}: third update: prefix" (out3.extract 0 out2.size == out2))
    f := f + (← check s!"{ctx}: third update: popup reference removed"
      (namesOn out3 0 == ["safepdf-mark-1", "safepdf-mark-2", "safepdf-mark-3",
        "safepdf-mark-7", "safepdf-mark-1-popup-8"]) (toString (namesOn out3 0)))
    match Api.openBytes out3 with
    | .ok d3 =>
      match refByNm d3.doc lim 0 "safepdf-mark-2" with
      | some (_, e) => f := f + (← check s!"{ctx}: third update: no /Contents, no /Popup"
          ((Dict.get? e kContents).isNone && (Dict.get? e (nm "Popup")).isNone))
      | none => f := f + (← check s!"{ctx}: third update: highlight 2" false)
    | .error _ => f := f + (← check s!"{ctx}: third update reopen" false)
    f := f + (← external s!"annots-edit3-{ctx}.pdf" orig out3 false)
  -- refusals: removing a reference that is not on the page; superseding a page object
  let isErr (r : Except Error ByteArray) : Bool := match r with
    | .error _ => true
    | .ok _ => false
  f := f + (← check s!"{ctx}: refuse removing an annotation of another page"
    (isErr (writeEdits lim d1.doc { removes := [(0, r5.1, r5.2)] })))
  match d1.doc.pages[0]? with
  | some pg => f := f + (← check s!"{ctx}: refuse superseding a page object"
      (isErr (Write.Incremental.writeUpdate lim d1.doc [] [(pg.num, pg.gen, [])])))
  | none => pure ()
  f := f + (← check s!"{ctx}: refuse superseding twice"
    (isErr (Write.Incremental.writeUpdate lim d1.doc []
      [(r1.1, r1.2, [(nm "A", PdfObject.int 1)]), (r1.1, r1.2, [(nm "A", PdfObject.int 2)])])))
  return f

/-! ## Free text and ink (task 9.9) -/

/-- The free text of `edMarks` (a non-WinAnsi character). -/
def ftText : String := "Text Box ✓"

/-- Free text and ink on page 2 (task 9.9). -/
def edMarks : List Mark :=
  [ { page := 1, kind := .freeText, quads := [], rect := ⟨40, 110, 40, 110⟩,
      color := (215 / 255, 0, 34 / 255), id := 11, date, contents := ftText, fontSize := 20 },
    { page := 1, kind := .ink, quads := [], rect := ⟨0, 0, 0, 0⟩,
      color := (0, 96 / 255, 223 / 255), id := 12, date,
      strokes := [[(150, 40), (170, 95), (190, 50)], [(130, 60)]], lineWidth := 6 },
    { page := 1, kind := .ink, quads := [], rect := ⟨0, 0, 0, 0⟩,
      color := (5 / 255, 139 / 255, 0), opacity := 2 / 5, id := 13, date,
      strokes := [[(30, 40), (110, 40)]], lineWidth := 3 } ]

/-- Our render of page `i` at zoom 2 with the system's substitute fonts (`none` without the
Helvetica substitute or when the page does not render). -/
def oursSubst (bytes : ByteArray) (i : Nat) : IO (Option Rgb) := do
  let files ← SafePdf.Shell.Fonts.findFiles
  if !files.any (·.1 == Font.Std14.helvetica) then return none
  let subst ← SafePdf.Shell.Fonts.loadSubstFonts {}
  match Api.openBytes bytes with
  | .ok d => match d.doc.pages[i]? with
    | some p => match (Raster.Glyph.renderDocPage d.limits d.doc p 2 .r0
          (Filter.Budget.init d.limits) (subst := subst)).1 with
      | .ok img => return some (Rgb.ofImage img)
      | .error _ => return none
    | none => return none
  | .error _ => return none

/-- Render checks of page 2 with the free text and ink: red text in the box, the blue stroke
(around the middle of its first segment), the half-transparent green line. -/
def edRenderChecks (who : String) (m : Rgb) (text : Bool) : IO Nat := do
  let mut f := 0
  if text then
    let (n, red, _, _) := stats m 2 200 42 80 130 108 (215, 0, 34) 0
    f := f + (← check s!"{who}: red free text in its box" (red * 20 ≥ n && red > 30)
      s!"{red}/{n} red")
  let (n2, blue, _, _) := stats m 2 200 158 66 162 70 (0, 96, 223) 0
  f := f + (← check s!"{who}: blue ink stroke" (blue * 2 ≥ n2) s!"{blue}/{n2} blue")
  let (n3, green, _, _) := stats m 2 200 60 39 80 41 (155, 208, 153) 0
  f := f + (← check s!"{who}: half-transparent green ink" (green * 2 ≥ n3) s!"{green}/{n3}")
  let (n4, _, _, w4) := stats m 2 200 60 110 100 140 (0, 0, 0) 0
  f := f + (← check s!"{who}: paper above the text box stays white" (w4 == n4) s!"{w4}/{n4}")
  return f

/-- **Free text and ink** (task 9.9; see the module doc) written into `orig` (`ctx` names the
run; `enc`: the document is encrypted). -/
def runEditors (ctx : String) (orig : System.FilePath) (enc : Bool) : IO Nat := do
  let lim := Limits.default
  let bytes ← IO.FS.readBinFile orig
  let .ok d := Api.openBytes bytes | check s!"{ctx}: open" false
  let mut f := 0
  let .ok out := writeMarks lim d.doc edMarks | check s!"{ctx}: writeMarks" false
  f := f + (← check s!"{ctx}: original is a prefix" (out.extract 0 bytes.size == bytes))
  if enc then
    let upd := (out.extract bytes.size out.size).toList
    f := f + (← check s!"{ctx}: no plaintext appearance in the update"
      (!contains upd (ascii "150. 40. m") && !contains upd (ascii "/Helv 20. Tf")))
  match Open.openFile lim out with
  | .ok od => f := f + (← check s!"{ctx}: strict reopen not repaired" (!od.repaired))
  | .error _ => f := f + (← check s!"{ctx}: strict reopen" false)
  let .ok d2 := Api.openBytes out | check s!"{ctx}: reopen" false
  let doc := d2.doc
  let some ft := edMarks[0]? | check s!"{ctx}: marks" false
  let some k1 := edMarks[1]? | check s!"{ctx}: marks" false
  match rawByNm doc lim 1 "safepdf-mark-11", rawByNm doc lim 1 "safepdf-mark-12",
      rawByNm doc lim 1 "safepdf-mark-13" with
  | some t, some i1, some i2 =>
    f := f + (← check s!"{ctx}: free text dictionary" (Dict.get? t kSubtype ==
      some (.name (nm "FreeText")) && Dict.get? t kContents == some (.string (textBytes ftText)) &&
      Dict.get? t kDA == some (.string (daBytes ft)) &&
      Dict.get? t kRect == some (rectObj ft.annotRect) && Dict.get? t (nm "F") == some (.int 4) &&
      Dict.get? t kC == none))
    f := f + (← check s!"{ctx}: /DA text" (daBytes ft == ascii "/Helv 20. Tf 0.8431 0. 0.1333 rg"))
    f := f + (← check s!"{ctx}: ink dictionary" (Dict.get? i1 kSubtype == some (.name (nm "Ink")) &&
      Dict.get? i1 kInkList == some (.array (inkListObj k1.strokes)) &&
      Dict.get? i1 (nm "BS") == some (.dict [(nm "W", .real ⟨6, 0⟩)]) &&
      Dict.get? i1 (nm "CA") == none && Dict.get? i2 (nm "CA") == some (.real ⟨4, 1⟩)))
    f := f + (← check s!"{ctx}: /InkList 1:1" (match Dict.get? i1 kInkList with
      | some (.array [.array a, .array b]) => a.length == 6 && b.length == 2
      | _ => false))
    match apStream doc lim t, apStream doc lim i1, apStream doc lim i2 with
    | some at', some a1, some a2 =>
      f := f + (← check s!"{ctx}: free-text appearance" (contains
        (Print.printObj (.dict at'.dict)) (ascii "/BaseFont /Helvetica") &&
        contains at'.data.toList (ascii "(Text Box \\267) Tj")))
      f := f + (← check s!"{ctx}: ink appearance" (contains a1.data.toList (ascii "1 J\n1 j\n") &&
        contains a1.data.toList (ascii "150. 40. m\n170. 95. l\n190. 50. l\nS\n") &&
        contains a1.data.toList (ascii "130. 60. m\n130. 60. l\nS\n") &&
        contains a2.data.toList (ascii "/R0 gs")))
    | _, _, _ => f := f + (← check s!"{ctx}: appearance streams resolve" false)
  | _, _, _ => f := f + (← check s!"{ctx}: free text / ink dictionaries" false)
  -- the shell's read-back
  let got := SafePdf.Shell.App.Save.readMarks doc lim
  let kindOf (id : Nat) : Option SafePdf.Shell.App.Marks.Kind := (got.find? (·.id == id)).map (·.kind)
  f := f + (← check s!"{ctx}: read back free text" ((kindOf 11).any (·.same
    (.freeText ftText ⟨40, 110⟩ 20 (215, 0, 34)))) (reprStr (kindOf 11)))
  f := f + (← check s!"{ctx}: read back ink" ((kindOf 12).any (·.same
    (.ink [[⟨150, 40⟩, ⟨170, 95⟩, ⟨190, 50⟩], [⟨130, 60⟩]] 6 100 (0, 96, 223))) &&
    (kindOf 13).any (·.same (.ink [[⟨30, 40⟩, ⟨110, 40⟩]] 3 40 (5, 139, 0)))) (reprStr (kindOf 12)))
  -- renders
  match ← oursSubst out 1 with
  | some m => f := f + (← edRenderChecks s!"{ctx} ours" m true)
  | none =>
    IO.println "  write-annots: no Helvetica substitute, our free-text render check skipped"
    match ours out 1 with
    | some m => f := f + (← edRenderChecks s!"{ctx} ours" m false)
    | none => f := f + (← check s!"{ctx}: our render" false)
  let (path, tmp) ← place s!"annots-editors-{ctx}.pdf" out
  match ← qpdfCheck path with
  | some code => f := f + (← check s!"{ctx}: qpdf --check" (code == 0) s!"exit {code}")
  | none => IO.println "  write-annots: qpdf not found, skipped"
  match ← mutool path 1 with
  | some m => f := f + (← edRenderChecks s!"{ctx} mutool" m true)
  | none => IO.println "  write-annots: mutool not found, editor render check skipped"
  if tmp then IO.FS.removeFile path
  -- an update: the free text moved and re-worded (superseded), the green drawing removed
  match refByNm doc lim 1 "safepdf-mark-11", refByNm doc lim 1 "safepdf-mark-13" with
  | some (r11, _), some (r13, _) =>
    let moved : Mark := { ft with rect := ⟨40, 140, 40, 140⟩, contents := "Moved", date := date2,
                                  created := date }
    match writeEdits lim doc { sups := [⟨moved, r11, none⟩], removes := [(1, r13.1, r13.2)] } with
    | .error e => f := f + (← check s!"{ctx}: edit update" false (Api.Error.message (.pdf e)))
    | .ok out2 =>
      f := f + (← check s!"{ctx}: edit: first file is a prefix" (out2.extract 0 out.size == out))
      match Api.openBytes out2 with
      | .error e => f := f + (← check s!"{ctx}: edit reopen" false e.message)
      | .ok d3 =>
        let got2 := SafePdf.Shell.App.Save.readMarks d3.doc lim
        f := f + (← check s!"{ctx}: edit read back" (got2.length == 2 &&
          (got2.find? (·.id == 11)).any (·.kind.same (.freeText "Moved" ⟨40, 140⟩ 20 (215, 0, 34))) &&
          (got2.find? (·.id == 12)).isSome && (got2.find? (·.id == 13)).isNone)
          (reprStr (got2.map (·.id))))
        f := f + (← check s!"{ctx}: edit keeps the object number" ((refByNm d3.doc lim 1
          "safepdf-mark-11").any (·.1 == r11)))
        let (p2, tmp2) ← place s!"annots-editors-edit-{ctx}.pdf" out2
        match ← qpdfCheck p2 with
        | some code => f := f + (← check s!"{ctx}: edit qpdf --check" (code == 0) s!"exit {code}")
        | none => pure ()
        if tmp2 then IO.FS.removeFile p2
  | _, _ => f := f + (← check s!"{ctx}: references of the free text / ink" false)
  return f

/-- Encrypted variants of the fixture (task 9.5f; `Tests/fixtures-write/encrypted/`,
`generate.py`): RC4-40, RC4-128, AES-128, AES-256, and AES-256 with an xref stream. -/
def encFixtures : List String :=
  ["rc4-40.pdf", "rc4-128.pdf", "aes-128.pdf", "aes-256.pdf", "aes-256-objstm.pdf"]

/-- One encrypted fixture (task 9.5f): the fixture's marks are written with `writeMarks`; the
result reopens strictly with the same file key, reads back exactly as the unencrypted
fixture (`readBack`: `/Contents` incl. UTF-16, appearance streams, …), renders the
highlight (ours and `mutool`), passes `qpdf --check`; the update holds none of the new
strings or appearance-stream data in the clear; a second update on top works. -/
def runEncrypted (name : String) : IO Nat := do
  let lim := Limits.default
  let path : System.FilePath := "Tests" / "fixtures-write" / "encrypted" / name
  let bytes ← IO.FS.readBinFile path
  let ctx := s!"encrypted {name}"
  match Api.openBytes bytes with
  | .error e => check s!"{ctx}: open" false e.message
  | .ok d =>
    let mut f := 0
    f := f + (← check s!"{ctx}: original is encrypted" d.doc.file.crypt.isSome)
    match writeMarks lim d.doc marks with
    | .error e => return f + (← check s!"{ctx}: writeMarks" false (Api.Error.message (.pdf e)))
    | .ok out =>
      f := f + (← check s!"{ctx}: original is a prefix" (out.extract 0 bytes.size == bytes))
      let upd := (out.extract bytes.size out.size).toList
      f := f + (← check s!"{ctx}: no plaintext /NM in the update"
        (!contains upd (ascii "safepdf-mark")))
      f := f + (← check s!"{ctx}: no plaintext /M date in the update"
        (!contains upd (ascii "D:2026")))
      f := f + (← check s!"{ctx}: no plaintext appearance stream in the update"
        (!contains upd (ascii "38. 136. m")))
      f := f + (← check s!"{ctx}: /Encrypt kept in the new trailer"
        (contains upd (ascii "/Encrypt")))
      match Open.openFile lim out with
      | .ok od => f := f + (← check s!"{ctx}: same file key after reopen"
          (match od.crypt, d.doc.file.crypt with
            | some a, some b => a.fileKey.data == b.fileKey.data
            | _, _ => false))
      | .error _ => f := f + (← check s!"{ctx}: strict reopen" false)
      let rb ← readBack out
      if rb > 0 then IO.println s!"  ({ctx}: {rb} read-back failure(s) above)"
      f := f + rb
      match ours bytes 0, ours out 0 with
      | some b, some a => f := f + (← renderChecks s!"{ctx} ours" b a)
      | _, _ => f := f + (← check s!"{ctx}: our render" false)
      f := f + (← external s!"annots-enc-{name}" path out true)
      f := f + (← runEdits s!"enc-{name}" path out true)
      f := f + (← runEditors s!"enc-{name}" path true)
      match Api.openBytes out with
      | .ok d2 =>
        let more : List Mark :=
          [{ page := 1, kind := .note, quads := [], rect := ⟨10, 10, 30, 30⟩,
             color := (1, 79 / 255, 95 / 255), id := 6, date := date,
             contents := "zweite Sicherung ✓" }]
        match writeMarks lim d2.doc more with
        | .ok out2 =>
          match Api.openBytes out2 with
          | .ok d3 => match Api.pageAnnotations d3 1 with
            | .ok as => f := f + (← check s!"{ctx}: second update read back"
                ((as.filterMap (·.name)) == ["safepdf-mark-4", "safepdf-mark-5",
                  "safepdf-mark-6"] &&
                  (as.find? (·.name == some "safepdf-mark-6")).bind (·.contents) ==
                    some "zweite Sicherung ✓") (toString (as.filterMap (·.name))))
            | .error _ => f := f + (← check s!"{ctx}: second update annotations" false)
          | .error e => f := f + (← check s!"{ctx}: second update reopen" false e.message)
          f := f + (← external s!"annots-enc2-{name}" path out2 false)
        | .error e =>
          f := f + (← check s!"{ctx}: second update" false (Api.Error.message (.pdf e)))
      | .error e => f := f + (← check s!"{ctx}: reopen for second update" false e.message)
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
    let ink0 : Mark :=
      { page := 0, kind := .ink, quads := [], rect := ⟨0, 0, 0, 0⟩, color := (0, 0, 0), id := 9,
        date := date }
    f := f + (← check "refuse ink without strokes / with an empty stroke"
      (isErr (writeMarks lim d.doc [ink0]) &&
       isErr (writeMarks lim d.doc [{ ink0 with strokes := [[(1, 1)], []] }])))
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
      f := f + (← runEdits "plain" fixture out false)
      f := f + (← runEditors "plain" fixture false)
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
  for name in encFixtures do
    f := f + (← runEncrypted name)
  match ← IO.getEnv "SAFEPDF_WRITEANNOTS_CORPUS" with
  | some file => f := f + (← corpus file)
  | none => pure ()
  return f

end SafePdf.Tests.WriteAnnots
