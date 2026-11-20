import SafePdf.Shell.App.Xfdf

/-!
# XFDF import/export (task 9.5d)

Plan.md §6 Phase 9 ("Persistence — annotations inside the PDF": XFDF stays as import/export).
The pure module `SafePdf.Shell.App.Xfdf` carries most checks as `#guard`s; this suite covers
what needs files or large inputs:

* round trip export → file → import on a store with highlights, notes, a highlight's comment
  and non-ASCII / non-BMP / control-character text: the identity on our marks (ids included);
* the samples under `Tests/xfdf/` in the styles of Acrobat, Foxit, an Okular-style and a
  PDF.js-style variant (each file's header comment says where its conventions come from and
  what it must import): marks, colours, pages, quads, comments, skipped and ignored counts;
* hostile inputs, each refused with the expected error and within `quickMs`: billion laughs
  and XXE (`<!DOCTYPE`), an undeclared entity, 1,000,000 nested elements, a 7 MiB attribute,
  a 9 MiB file, 100,000 attributes, 300,000 elements.
-/

namespace SafePdf.Tests.Xfdf

open SafePdf.Core.Raster.Geom (Pt Box)
open SafePdf.Shell.App.Marks (Mark Color Store Kind Anchor)
open SafePdf.Shell.App.Xfdf

/-- Reports a failed check; 1 on failure. -/
def check (what : String) (ok : Bool) (detail : String := "") : IO Nat := do
  if ok then return 0
  IO.println s!"  FAIL xfdf: {what} {detail}"
  return 1

/-- Directory of the samples. -/
def dir : System.FilePath := "Tests" / "xfdf"

/-- Time budget of a hostile input (milliseconds). -/
def quickMs : Nat := 2000

/-- The store of the round trip: two highlights, a note at a point with hostile text, a
highlight's comment, a note anchored to a selection, an empty note. -/
def sample : Store :=
  let s : Store := {}
  let (s, _) := (s.addHighlight 0 .yellow [⟨72.5, 700, 300.125, 712⟩, ⟨72.5, 688, 150, 700⟩]).getD (s, 0)
  let (s, _) := s.addNote 0 .pink "Grüße <&> \"q\" 'a' ]]> &amp;\n\ttab\r😀 𝔸 日本" (.point ⟨400, 500⟩)
  let (s, _) := (s.addHighlight 3 .green [⟨10, 10, 20, 20⟩]).getD (s, 0)
  let (s, _) := s.addNote 3 .green "its comment" (.quads [⟨10, 10, 20, 20⟩])
  let (s, _) := s.addNote 1 .red "on a selection" (.quads [⟨1, 2, 3, 4⟩, ⟨5, 6, 7, 8⟩])
  let (s, _) := s.addNote 2 .blue "" (.point ⟨50, 60⟩)
  s

/-- Whether two stores hold the same marks (ids, pages, colours, kinds), in order. -/
def sameMarks (a b : Store) : Bool :=
  a.marks.size == b.marks.size &&
    (a.marks.toList.zip b.marks.toList).all fun (x, y) => x.id == y.id && sameContent x y

/-- An item as a mark with id 0 (for comparisons). -/
def asMark (it : Item) : Mark := ⟨0, it.page, it.color, it.kind⟩

/-- What a sample must import: the marks (as id-0 marks), the skipped element names, and
the number of ignored elements. -/
structure Expect where
  /-- File name under `dir`. -/
  file : String
  /-- The marks. -/
  marks : List Mark
  /-- Element names of the skipped annotations. -/
  skipped : List String
  /-- Ignored elements outside `<annots>`. -/
  ignored : Nat

/-- The samples and what they import. -/
def samples : List Expect :=
  [ { file := "acrobat.xfdf",
      marks := [⟨0, 0, .yellow, .highlight [⟨72.024, 703.21, 301.66, 715.33⟩]⟩,
                ⟨0, 0, .yellow, .note "Key result — see Table 2\ncheck eq. (3)"
                  (.quads [⟨72.024, 703.21, 301.66, 715.33⟩])⟩,
                ⟨0, 1, .yellow, .note "Typo here?" (.point ⟨400.5, 620.25⟩)⟩],
      skipped := ["text", "underline"], ignored := 0 },
    { file := "foxit.xfdf",
      marks := [⟨0, 0, .yellow, .highlight [⟨56.7, 513.2, 540.3, 524.9⟩, ⟨56.7, 500.1, 300, 511.8⟩]⟩,
                ⟨0, 0, .yellow, .note "two lines, with a comment & an ampersand"
                  (.quads [⟨56.7, 513.2, 540.3, 524.9⟩, ⟨56.7, 500.1, 300, 511.8⟩])⟩,
                ⟨0, 2, .green, .highlight [⟨100, 100, 200, 112⟩]⟩,
                ⟨0, 2, .pink, .note "Fußnote prüfen" (.point ⟨500, 720⟩)⟩],
      skipped := ["squiggly", "strikeout"], ignored := 0 },
    { file := "okular-style.xfdf",
      marks := [⟨0, 4, .blue, .highlight [⟨90, 400, 250, 412⟩]⟩,
                ⟨0, 4, .blue, .note "a <CDATA> comment & more" (.quads [⟨90, 400, 250, 412⟩])⟩,
                ⟨0, 4, .yellow, .note "line one\nline two" (.point ⟨300, 324⟩)⟩],
      skipped := ["ink"], ignored := 1 },
    { file := "pdfjs-style.xfdf",
      marks := [⟨0, 0, .red, .highlight [⟨72, 616, 300, 628⟩, ⟨72, 600, 180, 612⟩]⟩,
                ⟨0, 0, .red, .note "📌 pinned\ttab\rand CR — “quotes”"
                  (.quads [⟨72, 616, 300, 628⟩, ⟨72, 600, 180, 612⟩])⟩,
                ⟨0, 1, .pink, .highlight [⟨10, 10, 50, 20⟩]⟩,
                ⟨0, 1, .blue, .note "日本語のメモ" (.point ⟨100, 220⟩)⟩],
      skipped := ["freetext", "ink"], ignored := 0 } ]

/-- Runs `f` and returns its result and the elapsed milliseconds. -/
def timed {α : Type} (f : Unit → α) : IO (α × Nat) := do
  let t0 ← IO.monoMsNow
  let r := f ()
  -- Force the result before taking the time.
  let r ← pure r
  let t1 ← IO.monoMsNow
  return (r, t1 - t0)

/-- Checks that `bytes` is refused with an error satisfying `ok`, within `quickMs`. -/
def hostile (what : String) (bytes : ByteArray) (ok : SafePdf.Shell.App.Xfdf.Error → Bool) : IO Nat := do
  let (r, ms) ← timed fun _ => readXfdf {} bytes (pages := some 10)
  match r with
  | .ok _ => check s!"{what} refused" false "(accepted)"
  | .error e =>
    IO.println s!"  xfdf: {what} ({bytes.size} bytes): {e.message} in {ms} ms"
    return (← check s!"{what} error kind" (ok e) e.message) +
      (← check s!"{what} quick" (ms ≤ quickMs) s!"{ms} ms")

/-- Run the suite. -/
def run : IO Nat := do
  let mut failures := 0
  -- 1. Round trip through a file.
  let xml := toXfdf sample (fun i => if i < 5 then some ⟨0, 0, 612, 792⟩ else none)
    "D:20261120120000Z" (some "paper ü.pdf")
  let (h, path) ← IO.FS.createTempFile
  h.putStr xml
  h.flush
  let r ← readFile {} path.toString (pages := some 5)
  IO.FS.removeFile path
  match r with
  | .error e => failures := failures + (← check "round trip reads back" false e)
  | .ok rep =>
    let (s, ids, dups) := importItems {} rep.items
    failures := failures + (← check "round trip identity" (sameMarks s sample))
    failures := failures + (← check "round trip ids" (ids == [1, 2, 3, 4, 5, 6] && dups == 0 &&
      rep.skippedCount == 0 && rep.ignored == 0 && s.nextId == 7 && s.dirty))
    -- Importing the same file again adds nothing.
    let (s2, ids2, dups2) := importItems s rep.items
    failures := failures + (← check "re-import idempotent"
      (ids2.isEmpty && dups2 == 6 && s2.marks.size == 6))
  -- A page beyond the document is skipped, not an error.
  match readXfdf {} xml.toUTF8 (pages := some 3) with
  | .ok rep => failures := failures + (← check "page bound" (rep.count == 4 &&
      rep.skippedCount == 2 && rep.skipped.all (·.reason == "page 3 is not in the document")))
  | .error e => failures := failures + (← check "page bound" false e.message)
  -- 2. Samples.
  for e in samples do
    match ← readFile {} (dir / e.file).toString (pages := some 10) with
    | .error msg => failures := failures + (← check s!"{e.file} imports" false msg)
    | .ok rep =>
      let got := rep.items.map asMark
      let okMarks := got.length == e.marks.length && (got.zip e.marks).all fun (a, b) => sameContent a b
      failures := failures + (← check s!"{e.file} marks" okMarks
        s!"{reprStr (rep.items.map fun i => (i.page, i.color, i.kind))}")
      failures := failures + (← check s!"{e.file} skipped"
        (rep.skipped.map (·.element) == e.skipped && rep.skippedCount == e.skipped.length)
        s!"{reprStr rep.skipped}")
      failures := failures + (← check s!"{e.file} ignored" (rep.ignored == e.ignored)
        s!"{rep.ignored}")
      let (s, ids, _) := importItems {} rep.items
      failures := failures + (← check s!"{e.file} into a store"
        (ids == (List.range e.marks.length).map (· + 1) && s.marks.size == e.marks.length))
  -- 3. Hostile inputs.
  let file (n : String) : IO ByteArray := IO.FS.readBinFile (dir / n)
  failures := failures + (← hostile "billion laughs" (← file "billion-laughs.xfdf")
    fun | .dtd _ => true | _ => false)
  failures := failures + (← hostile "XXE" (← file "xxe.xfdf") fun | .dtd _ => true | _ => false)
  failures := failures + (← hostile "undeclared entity" (← file "undeclared-entity.xfdf")
    fun | .entity _ "nbsp" => true | _ => false)
  let rep (n : Nat) (s : String) : String := String.join (List.replicate n s)
  failures := failures + (← hostile "1,000,000 nested elements"
    ("<xfdf><annots>" ++ rep 1000000 "<a>").toUTF8 fun | .tooDeep _ 32 => true | _ => false)
  failures := failures + (← hostile "7 MiB attribute"
    ("<xfdf><annots><highlight page='0' coords='" ++ rep (7 * 1024 * 1024) "1" ++ "'/></annots></xfdf>").toUTF8
    fun | .tooLong _ "attribute value" _ => true | _ => false)
  failures := failures + (← hostile "9 MiB file"
    ("<xfdf>" ++ rep (9 * 1024 * 1024) " " ++ "</xfdf>").toUTF8 fun | .tooLarge .. => true | _ => false)
  failures := failures + (← hostile "100,000 attributes"
    ("<xfdf" ++ String.join ((List.range 100000).map (s!" a{·}='1'")) ++ "/>").toUTF8
    fun | .tooManyAttrs _ 32 => true | _ => false)
  failures := failures + (← hostile "300,000 elements"
    ("<xfdf><annots>" ++ rep 300000 "<b/>" ++ "</annots></xfdf>").toUTF8
    fun | .tooManyNodes _ => true | _ => false)
  failures := failures + (← hostile "not UTF-8" (ByteArray.mk #[0xFF, 0xFE, 0x3C, 0x00])
    fun | .notUtf8 => true | _ => false)
  return failures

end SafePdf.Tests.Xfdf
