import SafePdf.Core.Write.Incremental
import SafePdf.Core.Annot

/-!
# Annotation dictionaries for user marks (Plan.md §4 S8/C7, §6 Phase 9 "Persistence — annotations inside the PDF"; task 9.5b)

Turns the reader's marks (highlights and notes, task 9.4) into standard PDF annotation
dictionaries (ISO 32000-2 §12.5) with generated appearance streams, ready for the
incremental-update writer `Core.Write.Incremental.writeAnnots` (task 9.5a). Pure and total;
Core does not import the shell, so the shell converts its `Shell.App.Marks.Mark`s into the
small record `Mark` below (task 9.5c). Core has no clock: the caller supplies the date.

## The mark record (`Mark`)

Page index, kind (`highlight` | `note`), quads in PDF page space (`Quad`: upper-left,
upper-right, lower-left, lower-right), a rectangle (a note's icon box; a highlight's
fallback), an RGB colour in `[0, 1]`, an opacity, the comment text, the stable id (`/NM` is
`safepdf-mark-ID`, `nmOf`, the prefix of `Shell.App.Marks.nmPrefix`), the PDF date string
(`D:YYYYMMDDHHmmSSOHH'mm`) and an optional author.

## What is written (rules A1–A9)

* A1. **Highlight** (§12.5.6.10): `/Type /Annot /Subtype /Highlight /Rect /NM`, then
  `/QuadPoints` (per quad `x1 y1 x2 y2 x3 y3 x4 y4` = upper-left, upper-right, lower-left,
  lower-right: the order Acrobat and pdf.js write and read, and `Core.Annot.quadsOf`
  reads), `/C [r g b]`, `/CA` only when the opacity is below 1, `/F 4` (Print), `/Border
  [0 0 0]` (as pdf.js), `/M` and `/CreationDate` (the caller's date), `/T` when an author is
  given, `/Contents` when the comment is not empty, `/Popup` (see A3), `/P` (the page) and
  `/AP << /N … >>`. `/Rect` is the union of the quads, rounded outwards (A7), so it
  contains every rounded quad point.
* A2. **Note** (§12.5.6.4, `/Subtype /Text`): `/Rect` = the icon box, `/Contents` (always,
  possibly empty), `/Name /Comment`, `/C`, `/F 4`, `/M`, `/CreationDate`, `/T`, `/Open
  false`, `/P`, `/AP`. **Anchor**: a note attached to a text selection keeps its quads in
  `/QuadPoints`. That key is not defined for `/Text` (Table 172); readers ignore it (§7.3.7:
  unknown keys are ignored), task 9.5c reads it back to restore the anchor.
* A3. **"Highlight with comment"** follows what pdf.js writes (`src/core/annotation.js`,
  `MarkupAnnotation.createNewAnnotation` and `PopupAnnotation.createNewDict`, fetched
  2026-11-20): a highlight whose comment is not empty carries `/Contents` and `/Popup R`, and
  a second annotation `/Type /Annot /Subtype /Popup /Open false /Rect … /Parent R` (the
  highlight) follows it in `/Annots`; pdf.js uses neither a separate `/Text` nor `/IRT` for
  it. Our popup also gets `/NM safepdf-mark-ID-popup` (so every dictionary we write has an
  `/NM`; `Shell.App.Marks.idOfNm` returns `none` for it) and `/F 4`. `/Popup` annotations
  have no appearance and are never drawn (`Core.Annot.collect`, MuPDF).
* A4. **Highlight appearance** (as pdf.js `HighlightAnnotation.createNewAppearanceStream`):
  a form XObject `/Type /XObject /Subtype /Form /FormType 1 /BBox` = `/Rect`, `/Matrix` the
  identity (so the §12.5.5 matrix A is the identity), `/Resources << /ExtGState << /R0
  << /Type /ExtGState /BM /Multiply >> >> >>` (plus `/CA`, `/ca` when the opacity is below
  1); content `r g b rg /R0 gs`, then per quad `ul m ur l lr l ll l h`, then `f`.
  Multiply keeps black text black and tints the white paper.
* A5. **Note appearance**: a speech bubble filled with the colour and stroked in black with
  three dark text lines (`noteIcon`), drawn in `/BBox [0 0 20 20]` with the identity
  `/Matrix`; §12.5.5 maps that box onto `/Rect`.
* A6. **Text strings** (§7.9.2.2; `textBytes`): bytes of the string when every character is
  printable ASCII, TAB, LF or CR (the same bytes in PDFDocEncoding), else `FE FF` and
  UTF-16BE (`utf16be`, surrogate pairs above U+FFFF), as pdf.js `stringToAsciiOrUTF16BE`.
  `utf16_utf16be` proves that `Font.CMap.utf16` (the text-string decoder of
  `Core.Annot.textOf`) reads the UTF-16 form back exactly.
* A7. **Numbers** are written as decimals: coordinates rounded to 1/1000 (`/Rect` floor for
  the lower-left, ceiling for the upper-right corner), colours and opacities clamped to
  `[0, 1]` and rounded to 1/10000; always canonical (`decRound_canonical`).
* A8. **Object numbers** (`build`): marks are grouped by page in order of first occurrence;
  the annotations of all pages are numbered from the document's `/Size` in that order (a
  highlight with comment takes two: highlight, popup), exactly as `writeAnnots` numbers
  them (rule W3); the appearance streams follow in the same mark order (rule W9). `/P` is
  the page's own object reference from `Doc.pages`.
* A9. **Validation**: a page index out of range is `Error.malformed`; a highlight without
  quads is `Error.malformed`. The writer then checks every dictionary (canonical, references
  in range) and re-parses the result strictly (rules W2, W8).
* A10. **Edits of marks already in the file** (task 9.5g; `buildEdits`, `writeEdits`, writer
  rule W11). An `EditSet` holds new marks (`adds`, written as by A8), **superseded** marks
  (`SupMark`: the new mark record, the object `(num, gen)` of its annotation in the file, and
  its existing `/Popup` object if any) and **removed** annotations (`removes`: page index and
  object). A superseded mark's dictionary is built as for a new one (same `/NM`, so the
  shell finds it again) under its own number and generation, `/M` = the caller's date,
  `/CreationDate` = `Mark.created` (the original's, when the caller passes it), and a fresh
  appearance stream (a new auxiliary object, numbered after those of the added marks, in
  `sups` order; the old stream stays in the earlier revision). Its popup (A3): a highlight
  that keeps a comment and has a popup object supersedes that popup too (new `/NM`, `/M`); one
  that gains a comment gets a **new** popup object, appended to its page's `/Annots` after the
  page's added marks; one that loses its comment drops `/Contents` and `/Popup` and its popup
  reference is **removed** from the page's `/Annots`. Deleting a highlight with a comment is
  the caller's `removes` entries for both the highlight and its popup (`SupMark` /
  `removeMark`). Pages are touched (rewritten, W4) only when something is added to or removed
  from their `/Annots`; pure supersessions leave the page dictionary alone.
* A11. **Comment ids** (task 9.5g): the shell keeps a highlight's comment as a separate note
  mark with its own id. When `Mark.commentId` is set, the popup's `/NM` is
  `safepdf-mark-ID-popup-CID` (still not a mark name for `Shell.App.Marks.idOfNm`), so the
  comment note gets its id back on reopen; without it, `safepdf-mark-ID-popup` as before.
* A12. **Free text** (task 9.9, §12.5.6.6, as pdf.js `FreeTextAnnotation.createNewDict`):
  `/Subtype /FreeText`, `/Rect` = the text box (`freeTextBox`: upper-left corner at
  `Mark.rect`'s `(x0, y1)`, `ftPad` around the lines, line height `lineFactor` × size — pdf.js
  `LINE_FACTOR` 1.35 —, width the longest line in Helvetica's AFM widths), then `/Contents`
  (rule A6: ASCII, else UTF-16BE), `/DA (/Helv SIZE Tf R G B rg)`, `/F 4`, `/Border [0 0 0]`,
  `/M`, `/CreationDate`, `/T` (author), `/P`, `/AP`. No `/C` (pdf.js writes none; the colour
  is the text colour in `/DA`).
* A13. **Free-text appearance**: a form with `/Resources << /Font << /Helv << /Type /Font
  /Subtype /Type1 /BaseFont /Helvetica /Encoding /WinAnsiEncoding >> >> >>` (a standard-14
  font, nothing embedded), clipped to the box, one `Tj` per line from the first baseline
  `ftPad + size` below the top. **Characters outside WinAnsi** (Windows-1252,
  `Core.Annot.win1252`) are drawn as `·` (0xB7, MuPDF's replacement `Annot.code1252`), so the
  appearance shows a visible gap where Helvetica has no glyph; the exact text is always in
  `/Contents` (UTF-16BE when needed), which is what readers extract, edit and what we read
  back. pdf.js in that case writes no appearance at all and relies on the reader's own fonts;
  we keep an appearance so viewers that do not synthesise FreeText still draw the text.
* A14. **Ink** (§12.5.6.13, as pdf.js `InkAnnotation.createNewDict`): `/Subtype /Ink`,
  `/Rect` = the strokes' bounding box grown by the line width (`inkBox`), then `/InkList`
  (one array `x1 y1 x2 y2 …` per stroke, in stroke order: `inkListObj`, theorems
  `inkListObj_length`, `strokeNums_length`), `/BS << /W w >>`, `/C`, `/CA` below opacity 1,
  `/F 4`, `/M`, `/CreationDate`, `/T`, `/P`, `/AP`. A mark has at least one stroke and every
  stroke at least one point (A9: else `Error.malformed`).
* A15. **Ink appearance** (as pdf.js `InkAnnotation.createNewAppearanceStream`): `w w 1 J 1 j`
  (round caps and joins), `r g b RG`, `/R0 gs` with `/CA`/`/ca` below opacity 1, each stroke
  `m` then `l` per further point (a one-point stroke repeats its point: a round dot), `S`.
-/

namespace SafePdf.Core.Write.Annots

open SafePdf SafePdf.Core
open SafePdf.Core.Write.Incremental (Marks AuxStream)

/-! ## Names -/

/-- A name from a string. -/
def nm (s : String) : Name := Name.ofString s

/-- `/Type` (spelled as bytes so that key inequalities are decidable by `decide`). -/
def kType : Name := ⟨[84, 121, 112, 101]⟩
/-- `/Subtype`. -/
def kSubtype : Name := ⟨[83, 117, 98, 116, 121, 112, 101]⟩
/-- `/Rect`. -/
def kRect : Name := ⟨[82, 101, 99, 116]⟩
/-- `/NM`. -/
def kNM : Name := ⟨[78, 77]⟩

#guard kType == nm "Type" && kSubtype == nm "Subtype" && kRect == nm "Rect" && kNM == nm "NM"
/-- `/QuadPoints`. -/
def kQuadPoints : Name := nm "QuadPoints"
/-- `/C`. -/
def kC : Name := nm "C"
/-- `/Contents` (as bytes, so key inequalities are decidable). -/
def kContents : Name := ⟨[67, 111, 110, 116, 101, 110, 116, 115]⟩
/-- `/InkList` (as bytes). -/
def kInkList : Name := ⟨[73, 110, 107, 76, 105, 115, 116]⟩
/-- `/DA` (as bytes). -/
def kDA : Name := ⟨[68, 65]⟩

#guard kContents == nm "Contents" && kInkList == nm "InkList" && kDA == nm "DA"
/-- `/AP`. -/
def kAP : Name := nm "AP"
/-- `/Annot`. -/
def vAnnot : Name := nm "Annot"

/-! ## Text strings (rule A6) -/

/-- The UTF-16BE code units of a character, as bytes (a surrogate pair above U+FFFF). -/
def unit16 (c : Char) : List UInt8 :=
  let u := c.toNat
  if u < 65536 then [UInt8.ofNat (u / 256), UInt8.ofNat (u % 256)]
  else
    let v := u - 65536
    let hi := 55296 + v / 1024
    let lo := 56320 + v % 1024
    [UInt8.ofNat (hi / 256), UInt8.ofNat (hi % 256), UInt8.ofNat (lo / 256),
      UInt8.ofNat (lo % 256)]

/-- UTF-16BE of a list of characters (no byte-order mark). -/
def utf16be : List Char → List UInt8
  | [] => []
  | c :: cs => unit16 c ++ utf16be cs

/-- Whether a character is written as itself (printable ASCII, TAB, LF, CR). -/
def plainChar (c : Char) : Bool :=
  (32 ≤ c.toNat && c.toNat ≤ 126) || c.toNat == 9 || c.toNat == 10 || c.toNat == 13

/-- **A text string** (rule A6): ASCII bytes, or `FE FF` and UTF-16BE. -/
def textBytes (s : String) : List UInt8 :=
  if s.toList.all plainChar then s.toList.map fun c => UInt8.ofNat c.toNat
  else [0xFE, 0xFF] ++ utf16be s.toList

/-- A character's code is a Unicode scalar value. -/
theorem char_valid (c : Char) : c.toNat < 55296 ∨ (57343 < c.toNat ∧ c.toNat < 1114112) := by
  have h := c.valid
  unfold UInt32.isValidChar at h
  exact h

/-- `UInt8.ofNat` keeps the low byte. -/
theorem uint8_ofNat_toNat (n : Nat) : (UInt8.ofNat n).toNat = n % 256 := by
  simp [UInt8.toNat_ofNat']

/-- Selecting the true branch of an `if`. -/
theorem ite_pos' {α : Type} {p : Prop} [Decidable p] (h : p) (a b : α) :
    (if p then a else b) = a := by simp [h]

/-- Two bytes of a 16-bit value put back together. -/
theorem split16 {w : Nat} (h : w < 65536) : w / 256 % 256 * 256 + w % 256 % 256 = w := by
  omega

/-- The decoder reads one encoded character back. -/
theorem utf16_unit16 (c : Char) (rest : List UInt8) :
    Font.CMap.utf16 (unit16 c ++ rest) = c :: Font.CMap.utf16 rest := by
  have hv := char_valid c
  unfold unit16
  dsimp only
  split
  · rename_i hlt
    rw [Font.CMap.utf16.eq_def]
    simp only [List.cons_append, List.nil_append, uint8_ofNat_toNat]
    rw [split16 hlt]
    have h1 : ¬ (55296 ≤ c.toNat ∧ c.toNat ≤ 56319) := by omega
    have h2 : ¬ (56320 ≤ c.toNat ∧ c.toNat ≤ 57343) := by omega
    simp only [h1, h2, ↓reduceIte, Char.ofNat_toNat]
  · rename_i hge
    rw [Font.CMap.utf16.eq_def]
    simp only [List.cons_append, List.nil_append, uint8_ofNat_toNat]
    have e1 : (55296 + (c.toNat - 65536) / 1024) / 256 % 256 * 256 +
        (55296 + (c.toNat - 65536) / 1024) % 256 % 256 = 55296 + (c.toNat - 65536) / 1024 :=
      split16 (by omega)
    have e2 : (56320 + (c.toNat - 65536) % 1024) / 256 % 256 * 256 +
        (56320 + (c.toNat - 65536) % 1024) % 256 % 256 = 56320 + (c.toNat - 65536) % 1024 :=
      split16 (Nat.add_lt_of_lt_sub' (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)))
    have h1 : 55296 ≤ 55296 + (c.toNat - 65536) / 1024 ∧
        55296 + (c.toNat - 65536) / 1024 ≤ 56319 := by omega
    have h2 : 56320 ≤ 56320 + (c.toNat - 65536) % 1024 ∧
        56320 + (c.toNat - 65536) % 1024 ≤ 57343 := by omega
    have e3 : 65536 + (55296 + (c.toNat - 65536) / 1024 - 55296) * 1024 +
        (56320 + (c.toNat - 65536) % 1024 - 56320) = c.toNat := by omega
    rw [e1, e2, ite_pos' h1, ite_pos' h2, e3, Char.ofNat_toNat]

/-- **UTF-16 round trip**: the text-string decoder reads `utf16be` back exactly. -/
theorem utf16_utf16be (cs : List Char) : Font.CMap.utf16 (utf16be cs) = cs := by
  induction cs with
  | nil => simp [utf16be, Font.CMap.utf16]
  | cons c cs ih => rw [utf16be, utf16_unit16, ih]

/-- **Text-string round trip, UTF-16 form**: a string with a character outside the plain
ASCII set is written as `FE FF` + UTF-16BE, and `Core.Annot.textOf` (MuPDF's
`pdf_to_text_string`) reads it back exactly. -/
theorem textOf_textBytes_utf16 (s : String) (h : s.toList.all plainChar = false) :
    Annot.textOf (textBytes s) = s.toList := by
  simp only [textBytes, h, Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append]
  simp only [Annot.textOf, utf16_utf16be]

/-! ## Numbers (rule A7) -/

/-- `q` rounded half up to `places` decimals, canonical. -/
def decRound (places : Nat) (q : Rat) : Decimal :=
  Decimal.normalize ⟨(q * (10 ^ places : Nat) + 1 / 2).floor, places⟩

/-- `q` rounded down to `places` decimals. -/
def decFloor (places : Nat) (q : Rat) : Decimal :=
  Decimal.normalize ⟨(q * (10 ^ places : Nat)).floor, places⟩

/-- `q` rounded up to `places` decimals. -/
def decCeil (places : Nat) (q : Rat) : Decimal :=
  Decimal.normalize ⟨(q * (10 ^ places : Nat)).ceil, places⟩

/-- Every number we write is canonical (the printer's round-trip hypothesis). -/
theorem decRound_canonical (p : Nat) (q : Rat) : (decRound p q).IsCanonical :=
  Decimal.normalize_isCanonical _

/-- A coordinate (1/1000). -/
def coord (q : Rat) : PdfObject := .real (decRound 3 q)

/-- A value clamped into `[0, 1]`. -/
def unitClamp (q : Rat) : Rat := max 0 (min 1 q)

/-- A colour component or opacity (1/10000, clamped to `[0, 1]`). -/
def unitNum (q : Rat) : PdfObject := .real (decRound 4 (unitClamp q))

/-! ## The mark record -/

/-- A quadrilateral in page space: upper-left, upper-right, lower-left, lower-right. -/
structure Quad where
  /-- Upper-left corner. -/
  ul : Rat × Rat
  /-- Upper-right corner. -/
  ur : Rat × Rat
  /-- Lower-left corner. -/
  ll : Rat × Rat
  /-- Lower-right corner. -/
  lr : Rat × Rat
  deriving Repr, Inhabited, DecidableEq

/-- The quad of an axis-aligned box `[x0, x1] × [y0, y1]`. -/
def Quad.ofBox (x0 y0 x1 y1 : Rat) : Quad := ⟨(x0, y1), (x1, y1), (x0, y0), (x1, y0)⟩

/-- The eight `/QuadPoints` numbers of a quad, in the A1 order. -/
def Quad.points (q : Quad) : List Rat :=
  [q.ul.1, q.ul.2, q.ur.1, q.ur.2, q.ll.1, q.ll.2, q.lr.1, q.lr.2]

/-- A quad as `Core.Annot` reads it. -/
def Quad.toAnnot (q : Quad) : Annot.Quad := (q.ul, q.ur, q.ll, q.lr)

/-- A rectangle in page space. -/
structure Rect where
  /-- Left. -/
  x0 : Rat
  /-- Bottom. -/
  y0 : Rat
  /-- Right. -/
  x1 : Rat
  /-- Top. -/
  y1 : Rat
  deriving Repr, Inhabited, DecidableEq

/-- The kind of a mark. -/
inductive Kind where
  /-- A highlight over the quads. -/
  | highlight
  /-- A note (`/Text` icon at `Mark.rect`), anchored to the quads when there are any. -/
  | note
  /-- Free text (`/FreeText`, rule A12): `Mark.contents` in Helvetica at `Mark.fontSize`,
  upper-left corner at `Mark.rect`'s `(x0, y1)`. -/
  | freeText
  /-- Ink (`/Ink`, rule A14): the strokes `Mark.strokes`, `Mark.lineWidth` wide. -/
  | ink
  deriving Repr, Inhabited, DecidableEq

/-- **A user mark** as Core sees it (the shell converts its marks into these, task 9.5c). -/
structure Mark where
  /-- Page index (0-based). -/
  page : Nat
  /-- Highlight or note. -/
  kind : Kind
  /-- Quads in page space (a highlight's area; a note's anchor, possibly none). -/
  quads : List Quad
  /-- A note's icon box (page space); a highlight's `/Rect` when it has no quads. -/
  rect : Rect
  /-- Colour, components in `[0, 1]`. -/
  color : Rat × Rat × Rat
  /-- Opacity in `[0, 1]` (`/CA` written only below 1). -/
  opacity : Rat := 1
  /-- Comment text (a note's text; a highlight's comment, empty for none). -/
  contents : String := ""
  /-- Stable id (`/NM` = `safepdf-mark-ID`). -/
  id : Nat
  /-- PDF date string (`D:YYYYMMDDHHmmSSOHH'mm`), supplied by the caller. -/
  date : String
  /-- Author (`/T`), empty for none. -/
  author : String := ""
  /-- The `/CreationDate` to keep (rule A10, a superseded mark), empty for `date`. -/
  created : String := ""
  /-- The id of the comment note this highlight's popup stands for (rule A11). -/
  commentId : Option Nat := none
  /-- Font size of a free-text mark (rule A12). -/
  fontSize : Rat := 10
  /-- The strokes of an ink mark (rule A14): points in page space, in drawing order. -/
  strokes : List (List (Rat × Rat)) := []
  /-- Line width of an ink mark (`/BS /W`). -/
  lineWidth : Rat := 1
  deriving Repr, Inhabited

/-- Prefix of our `/NM` names (equal to `Shell.App.Marks.nmPrefix`). -/
def nmPrefix : String := "safepdf-mark-"

/-- The `/NM` of mark id `id`. -/
def nmOf (id : Nat) : String := nmPrefix ++ toString id

/-- Whether the mark gets a `/Popup` (rule A3: a highlight with a comment). -/
def Mark.hasPopup (m : Mark) : Bool := m.kind == .highlight && !m.contents.isEmpty

/-- How many annotation dictionaries the mark yields (1, or 2 with a popup). -/
def Mark.slots (m : Mark) : Nat := if m.hasPopup then 2 else 1

/-- The union of the quads' corners (`none` without quads). -/
def quadsBox : List Quad → Option Rect
  | [] => none
  | q :: qs =>
    let r := quadsBox qs
    let xs := [q.ul.1, q.ur.1, q.ll.1, q.lr.1]
    let ys := [q.ul.2, q.ur.2, q.ll.2, q.lr.2]
    let x0 := xs.foldl min q.ul.1
    let x1 := xs.foldl max q.ul.1
    let y0 := ys.foldl min q.ul.2
    let y1 := ys.foldl max q.ul.2
    match r with
    | none => some ⟨x0, y0, x1, y1⟩
    | some b => some ⟨min x0 b.x0, min y0 b.y0, max x1 b.x1, max y1 b.y1⟩

/-! ## Free-text layout and ink boxes (rules A12, A14) -/

/-- Line height per unit of font size (pdf.js `LINE_FACTOR`). -/
def lineFactor : Rat := 135 / 100

/-- Padding between the free-text box and its text (pdf.js `--freetext-padding`, 2 px at
100 %). -/
def ftPad : Rat := 2

/-- The character drawn for `c` (rule A13): itself in Windows-1252, else `·`. -/
def drawnChar (c : Char) : Char := if (Annot.win1252 c).isSome then c else '·'

/-- Advance of `c` in Helvetica, in em (Adobe AFM widths, `Core.Font.Std14`). -/
def helvAdvance (c : Char) : Rat := Annot.charWidth .helvetica (drawnChar c)

/-- The lines of a free text (line feeds; carriage returns dropped). -/
def textLines (s : String) : List (List Char) :=
  (s.toList.filter (· != '\r')).splitOn '\n'

/-- Width of a line in em. -/
def lineEm (l : List Char) : Rat := (l.map helvAdvance).sum

/-- **The free-text box** (rule A12) with upper-left corner `(x, yTop)` for `text` at font
size `size`: the longest line (at least one em) and the lines' height, `ftPad` around. -/
def freeTextBox (x yTop size : Rat) (text : String) : Rect :=
  let ls := textLines text
  let w := max size (((ls.map lineEm).foldl max 0) * size)
  let h := (ls.length : Rat) * lineFactor * size
  ⟨x, yTop - h - 2 * ftPad, x + w + 2 * ftPad, yTop⟩

/-- The bounding box of the points of some strokes (`none` without points). -/
def pointsBox (ps : List (Rat × Rat)) : Option Rect :=
  ps.foldl (fun acc p => match acc with
    | none => some ⟨p.1, p.2, p.1, p.2⟩
    | some b => some ⟨min b.x0 p.1, min b.y0 p.2, max b.x1 p.1, max b.y1 p.2⟩) none

/-- **The ink box** (rule A14): the strokes' bounding box grown by the line width on every
side (round caps reach half of it). -/
def inkBox (strokes : List (List (Rat × Rat))) (w : Rat) : Option Rect :=
  (pointsBox strokes.flatten).map fun b => ⟨b.x0 - w, b.y0 - w, b.x1 + w, b.y1 + w⟩

/-- The annotation rectangle (rule A1: a highlight's quads; a note's `rect`; free text: its
box at `rect`'s upper-left corner, A12; ink: its strokes' box, A14). -/
def Mark.annotRect (m : Mark) : Rect :=
  match m.kind with
  | .highlight => (quadsBox m.quads).getD m.rect
  | .note => m.rect
  | .freeText => freeTextBox m.rect.x0 m.rect.y1 m.fontSize m.contents
  | .ink => (inkBox m.strokes m.lineWidth).getD m.rect

/-- `/Rect`, rounded outwards (rule A7). -/
def rectObj (r : Rect) : PdfObject :=
  .array [.real (decFloor 3 (min r.x0 r.x1)), .real (decFloor 3 (min r.y0 r.y1)),
    .real (decCeil 3 (max r.x0 r.x1)), .real (decCeil 3 (max r.y0 r.y1))]

/-- The `/QuadPoints` numbers of the quads. -/
def quadPoints (qs : List Quad) : List Rat := qs.flatMap Quad.points

/-- `/QuadPoints`: eight coordinates per quad. -/
def quadPointsObj (qs : List Quad) : PdfObject := .array ((quadPoints qs).map coord)

/-- `/C`. -/
def colorObj (c : Rat × Rat × Rat) : PdfObject :=
  .array [unitNum c.1, unitNum c.2.1, unitNum c.2.2]

/-- A string object of ASCII text. -/
def asciiStr (s : String) : PdfObject := .string s.toUTF8.toList

/-- The bytes of a string (UTF-8; ASCII for the constants used here). -/
def ascii' (s : String) : List UInt8 := s.toUTF8.toList

/-! ## Annotation dictionaries (rules A1–A3) -/

/-- **Every annotation dictionary starts with** `/Type /Annot /Subtype s /Rect r /NM n`. -/
def mkAnnot (sub : String) (rect : PdfObject) (nmStr : String) (rest : Dict) : Dict :=
  (kType, .name vAnnot) :: (kSubtype, .name (nm sub)) :: (kRect, rect) ::
    (kNM, .string (textBytes nmStr)) :: rest

/-- What every dictionary we emit looks like (the head of `mkAnnot`). -/
def IsAnnot (d : Dict) : Prop :=
  ∃ sub rect n rest, d = (kType, .name vAnnot) :: (kSubtype, .name sub) :: (kRect, rect) ::
    (kNM, .string n) :: rest

/-- `mkAnnot` gives an `IsAnnot`. -/
theorem mkAnnot_isAnnot (sub : String) (rect : PdfObject) (n : String) (rest : Dict) :
    IsAnnot (mkAnnot sub rect n rest) := ⟨_, _, _, _, rfl⟩

/-- An optional entry. -/
def opt (b : Bool) (k : String) (v : PdfObject) : Dict := if b then [(nm k, v)] else []

/-- The entries common to highlights and notes (`/C`, `/CA`, `/F`, dates, author). -/
def common (m : Mark) : Dict :=
  [(kC, colorObj m.color)] ++ opt (decide (m.opacity < 1)) "CA" (unitNum m.opacity) ++
    [(nm "F", .int 4)] ++
    [(nm "M", asciiStr m.date),
      (nm "CreationDate", asciiStr (if m.created.isEmpty then m.date else m.created))] ++
    opt (!m.author.isEmpty) "T" (.string (textBytes m.author))

/-- The highlight dictionary (rule A1) with popup reference `popup` (used when the mark has
a comment), appearance stream `ap`, page reference `page`. -/
def highlightDictP (m : Mark) (popup : PdfObject) (ap : Nat) (page : PdfObject) : Dict :=
  mkAnnot "Highlight" (rectObj m.annotRect) (nmOf m.id) <|
    [(kQuadPoints, quadPointsObj m.quads)] ++ common m ++
    [(nm "Border", .array [.int 0, .int 0, .int 0])] ++
    opt m.hasPopup "Contents" (.string (textBytes m.contents)) ++
    opt m.hasPopup "Popup" popup ++
    [(nm "P", page), (kAP, .dict [(nm "N", .ref ap 0)])]

/-- The highlight dictionary (rule A1); `num` its own number, `ap` its appearance stream's,
`page` the page reference. -/
def highlightDict (m : Mark) (num ap : Nat) (page : PdfObject) : Dict :=
  highlightDictP m (.ref (num + 1) 0) ap page

/-- The popup's `/NM` (rules A3, A11). -/
def popupNm (m : Mark) : String :=
  nmOf m.id ++ "-popup" ++ match m.commentId with
    | some c => "-" ++ toString c
    | none => ""

/-- The popup of a highlight with comment (rule A3), with parent reference `parent`. -/
def popupDictP (m : Mark) (parent : PdfObject) (page : PdfObject) : Dict :=
  mkAnnot "Popup" (rectObj m.annotRect) (popupNm m)
    [(nm "Parent", parent), (nm "Open", .bool false), (nm "F", .int 4),
      (nm "M", asciiStr m.date), (nm "P", page)]

/-- The popup of a highlight with comment (rule A3); `parent` the highlight's number. -/
def popupDict (m : Mark) (parent : Nat) (page : PdfObject) : Dict :=
  popupDictP m (.ref parent 0) page

/-- The note dictionary (rule A2). -/
def noteDict (m : Mark) (ap : Nat) (page : PdfObject) : Dict :=
  mkAnnot "Text" (rectObj m.annotRect) (nmOf m.id) <|
    [(kContents, .string (textBytes m.contents)), (nm "Name", .name (nm "Comment"))] ++
    common m ++ [(nm "Open", .bool false)] ++
    opt (!m.quads.isEmpty) "QuadPoints" (quadPointsObj m.quads) ++
    [(nm "P", page), (kAP, .dict [(nm "N", .ref ap 0)])]

/-- The bytes of a colour's three components, separated by spaces. -/
def compBytes (c : Rat × Rat × Rat) : List UInt8 :=
  Print.printObj (unitNum c.1) ++ [32] ++ Print.printObj (unitNum c.2.1) ++ [32] ++
    Print.printObj (unitNum c.2.2)

/-- `/DA` of a free text (rule A12): `/Helv SIZE Tf R G B rg`. -/
def daBytes (m : Mark) : List UInt8 :=
  ascii' "/Helv " ++ Print.printObj (coord m.fontSize) ++ ascii' " Tf " ++ compBytes m.color ++
    ascii' " rg"

/-- The free-text dictionary (rule A12); `/Contents` comes first after the head. -/
def freeTextDict (m : Mark) (ap : Nat) (page : PdfObject) : Dict :=
  mkAnnot "FreeText" (rectObj m.annotRect) (nmOf m.id) <|
    [(kContents, .string (textBytes m.contents)), (kDA, .string (daBytes m)),
      (nm "F", .int 4), (nm "Border", .array [.int 0, .int 0, .int 0]),
      (nm "M", asciiStr m.date),
      (nm "CreationDate", asciiStr (if m.created.isEmpty then m.date else m.created))] ++
    opt (!m.author.isEmpty) "T" (.string (textBytes m.author)) ++
    [(nm "P", page), (kAP, .dict [(nm "N", .ref ap 0)])]

/-- The numbers of one stroke: `x1 y1 x2 y2 …` (rule A14). -/
def strokeNums (s : List (Rat × Rat)) : List PdfObject := s.flatMap fun p => [coord p.1, coord p.2]

/-- `/InkList`: one array per stroke, in order (rule A14). -/
def inkListObj (strokes : List (List (Rat × Rat))) : List PdfObject :=
  strokes.map fun s => .array (strokeNums s)

/-- The ink dictionary (rule A14); `/InkList` comes first after the head. -/
def inkDict (m : Mark) (ap : Nat) (page : PdfObject) : Dict :=
  mkAnnot "Ink" (rectObj m.annotRect) (nmOf m.id) <|
    [(kInkList, .array (inkListObj m.strokes)),
      (nm "BS", .dict [(nm "W", coord m.lineWidth)])] ++ common m ++
    [(nm "P", page), (kAP, .dict [(nm "N", .ref ap 0)])]

/-- The annotation dictionaries of one mark (`num` its first number). -/
def annotDicts (m : Mark) (num ap : Nat) (page : PdfObject) : List Dict :=
  match m.kind with
  | .highlight =>
    if m.hasPopup then [highlightDict m num ap page, popupDict m num page]
    else [highlightDict m num ap page]
  | .note => [noteDict m ap page]
  | .freeText => [freeTextDict m ap page]
  | .ink => [inkDict m ap page]

/-- A mark yields `slots` dictionaries (the numbering of rule A8 relies on it). -/
theorem annotDicts_length (m : Mark) (num ap : Nat) (page : PdfObject) :
    (annotDicts m num ap page).length = m.slots := by
  unfold annotDicts Mark.slots Mark.hasPopup
  cases hk : m.kind <;> simp <;> split <;> rfl

/-- **Every annotation dictionary we emit starts with `/Type /Annot`, `/Subtype`, `/Rect`,
`/NM`.** -/
theorem annotDicts_isAnnot (m : Mark) (num ap : Nat) (page : PdfObject) :
    ∀ d ∈ annotDicts m num ap page, IsAnnot d := by
  intro d hd
  unfold annotDicts at hd
  split at hd
  · split at hd
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl
      · exact mkAnnot_isAnnot _ _ _ _
      · exact mkAnnot_isAnnot _ _ _ _
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      subst hd
      exact mkAnnot_isAnnot _ _ _ _
  all_goals
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    subst hd
    exact mkAnnot_isAnnot _ _ _ _

/-- Looking up a key in an `IsAnnot` dictionary's head. -/
theorem IsAnnot.lookup {d : Dict} (h : IsAnnot d) :
    (Dict.lookup d kType = some (.name vAnnot)) ∧
    (∃ s, Dict.lookup d kSubtype = some (.name s)) ∧
    (∃ r, Dict.lookup d kRect = some r) ∧
    (∃ n, Dict.lookup d kNM = some (.string n)) := by
  obtain ⟨sub, rect, n, rest, rfl⟩ := h
  have h1 : kType ≠ kSubtype := by decide
  have h2 : kType ≠ kRect := by decide
  have h3 : kSubtype ≠ kRect := by decide
  have h4 : kType ≠ kNM := by decide
  have h5 : kSubtype ≠ kNM := by decide
  have h6 : kRect ≠ kNM := by decide
  refine ⟨by simp [Dict.lookup], ⟨sub, ?_⟩, ⟨rect, ?_⟩, ⟨n, ?_⟩⟩ <;>
    simp [Dict.lookup, h1, h2, h3, h4, h5, h6]

/-! ## Appearance streams (rules A4, A5) -/

/-- ASCII bytes. -/
def ascii (s : String) : List UInt8 := s.toUTF8.toList

/-- A content-stream operation: the operands (printed by `Print.printObj`), then the
operator, then LF. -/
def op (args : List PdfObject) (o : String) : List UInt8 :=
  args.flatMap (fun a => Print.printObj a ++ [32]) ++ ascii o ++ [10]

/-- The fill colour operation. -/
def fillColor (c : Rat × Rat × Rat) : List UInt8 :=
  op [unitNum c.1, unitNum c.2.1, unitNum c.2.2] "rg"

/-- A point's two coordinates. -/
def pt (p : Rat × Rat) : List PdfObject := [coord p.1, coord p.2]

/-- One quad as a closed path: ul → ur → lr → ll. -/
def quadPath (q : Quad) : List UInt8 :=
  op (pt q.ul) "m" ++ op (pt q.ur) "l" ++ op (pt q.lr) "l" ++ op (pt q.ll) "l" ++ op [] "h"

/-- The highlight content stream (rule A4). -/
def highlightContent (m : Mark) : List UInt8 :=
  fillColor m.color ++ op [.name (nm "R0")] "gs" ++ m.quads.flatMap quadPath ++ op [] "f"

/-- The identity matrix. -/
def identity : PdfObject := .array [.int 1, .int 0, .int 0, .int 1, .int 0, .int 0]

/-- A form XObject dictionary. -/
def formDict (bbox : PdfObject) (res : Dict) : Dict :=
  [(kType, .name (nm "XObject")), (kSubtype, .name (nm "Form")), (nm "FormType", .int 1),
    (nm "BBox", bbox), (nm "Matrix", identity), (nm "Resources", .dict res)]

/-- The highlight appearance stream (rule A4). -/
def highlightAp (m : Mark) : AuxStream :=
  let gs : Dict := [(kType, .name (nm "ExtGState")), (nm "BM", .name (nm "Multiply"))] ++
    (if m.opacity < 1 then [(nm "CA", unitNum m.opacity), (nm "ca", unitNum m.opacity)]
     else [])
  ⟨formDict (rectObj m.annotRect) [(nm "ExtGState", .dict [(nm "R0", .dict gs)])],
    highlightContent m⟩

/-- The speech-bubble icon in a 20 × 20 box (rule A5): a bubble with a tail, filled with the
mark's colour and outlined in black, and three dark lines of "text". -/
def noteIcon (c : Rat × Rat × Rat) : List UInt8 :=
  fillColor c ++ ascii
    ("0 G\n1 w\n1 j\n" ++
     "1.5 6 m\n1.5 18.5 l\n18.5 18.5 l\n18.5 6 l\n10 6 l\n4.5 1.5 l\n6 6 l\nh\nB\n" ++
     "0.2 G\n1.5 w\n0 J\n4.5 15 m\n15.5 15 l\n4.5 12 m\n15.5 12 l\n4.5 9 m\n11.5 9 l\nS\n")

/-- The note appearance stream (rule A5). -/
def noteAp (m : Mark) : AuxStream :=
  ⟨formDict (.array [.int 0, .int 0, .int 20, .int 20]) [], noteIcon m.color⟩

/-- The free-text content stream (rule A13): clip to the box, then one `Tj` per line. -/
def freeTextContent (m : Mark) : List UInt8 :=
  let r := m.annotRect
  let lh := lineFactor * m.fontSize
  let lines := textLines m.contents
  let first := op [coord (r.x0 + ftPad), coord (r.y1 - ftPad - m.fontSize)] "Td"
  let lineOps := (lines.zip (List.range lines.length)).flatMap fun (l, i) =>
    (if i == 0 then first else op [coord 0, coord (-lh)] "Td") ++
      ascii (Annot.litStr (l.map drawnChar)) ++ ascii " Tj\n"
  op [] "q" ++ op [coord r.x0, coord r.y0, coord (r.x1 - r.x0), coord (r.y1 - r.y0)] "re" ++
    op [] "W" ++ op [] "n" ++ op [] "BT" ++ fillColor m.color ++
    op [.name (nm "Helv"), coord m.fontSize] "Tf" ++ lineOps ++ op [] "ET" ++ op [] "Q"

/-- The Helvetica font resource of a free-text appearance (rule A13). -/
def helvFont : PdfObject :=
  .dict [(kType, .name (nm "Font")), (kSubtype, .name (nm "Type1")),
    (nm "BaseFont", .name (nm "Helvetica")), (nm "Encoding", .name (nm "WinAnsiEncoding"))]

/-- The free-text appearance stream (rule A13). -/
def freeTextAp (m : Mark) : AuxStream :=
  ⟨formDict (rectObj m.annotRect) [(nm "Font", .dict [(nm "Helv", helvFont)])],
    freeTextContent m⟩

/-- One stroke as a path: `m`, then `l` to every further point (a one-point stroke repeats
its point, which round caps draw as a dot). -/
def strokePath : List (Rat × Rat) → List UInt8
  | [] => []
  | [p] => op (pt p) "m" ++ op (pt p) "l"
  | p :: ps => op (pt p) "m" ++ ps.flatMap fun q => op (pt q) "l"

/-- The ink content stream (rule A15). -/
def inkContent (m : Mark) : List UInt8 :=
  op [coord m.lineWidth] "w" ++ op [.int 1] "J" ++ op [.int 1] "j" ++
    op [unitNum m.color.1, unitNum m.color.2.1, unitNum m.color.2.2] "RG" ++
    (if m.opacity < 1 then op [.name (nm "R0")] "gs" else []) ++
    m.strokes.flatMap fun st => strokePath st ++ op [] "S"

/-- The ink appearance stream (rule A15). -/
def inkAp (m : Mark) : AuxStream :=
  let res : Dict := if m.opacity < 1 then
      [(nm "ExtGState", .dict [(nm "R0", .dict [(kType, .name (nm "ExtGState")),
        (nm "CA", unitNum m.opacity), (nm "ca", unitNum m.opacity)])])]
    else []
  ⟨formDict (rectObj m.annotRect) res, inkContent m⟩

/-- The appearance stream of a mark. -/
def apOf (m : Mark) : AuxStream :=
  match m.kind with
  | .highlight => highlightAp m
  | .note => noteAp m
  | .freeText => freeTextAp m
  | .ink => inkAp m

/-- Why a mark cannot be written (rule A9), if it cannot: a highlight without quads, an ink
mark without strokes or with an empty stroke. -/
def Mark.invalid (m : Mark) : Option String :=
  match m.kind with
  | .highlight => if m.quads.isEmpty then some "highlight without quads" else none
  | .ink =>
    if m.strokes.isEmpty then some "ink without strokes"
    else if m.strokes.any List.isEmpty then some "ink stroke without points" else none
  | _ => none

/-! ## Building the writer's input (rules A8, A9) -/

/-- Page indices in order of first occurrence. -/
def pageOrder : List Mark → List Nat
  | [] => []
  | m :: ms => let r := pageOrder ms; m.page :: r.filter (· != m.page)

/-- The marks grouped by page (rule A8). -/
def grouped (ms : List Mark) : List (Nat × List Mark) :=
  (pageOrder ms).map fun p => (p, ms.filter (·.page == p))

/-- The page reference of page index `i`. -/
def pageRef (doc : Doc.Doc) (i : Nat) : Except Error PdfObject :=
  match doc.pages[i]? with
  | some p => .ok (.ref p.num p.gen)
  | none => .error (.malformed 0 s!"mark on page index {i}, out of range")

/-- The dictionaries of a page's marks, numbered from `num`, appearance streams from `ap`. -/
def pageDicts (page : PdfObject) : Nat → Nat → List Mark → List Dict
  | _, _, [] => []
  | num, ap, m :: ms => annotDicts m num ap page ++ pageDicts page (num + m.slots) (ap + 1) ms

/-- Total number of annotation dictionaries of some marks. -/
def slotCount (ms : List Mark) : Nat := (ms.map Mark.slots).sum

/-- Build every page's list from `num` / `ap` on. -/
def buildPages (doc : Doc.Doc) : Nat → Nat → List (Nat × List Mark) →
    Except Error (List (Nat × List Dict))
  | _, _, [] => .ok []
  | num, ap, (p, ms) :: rest =>
    match pageRef doc p with
    | .error e => .error e
    | .ok r =>
      match buildPages doc (num + slotCount ms) (ap + ms.length) rest with
      | .error e => .error e
      | .ok xs => .ok ((p, pageDicts r num ap ms) :: xs)

/-- **The writer's input for `marks`** (rules A1–A9): per page the annotation dictionaries,
and the appearance streams, numbered as `writeAnnots` will number them for `doc`. -/
def build (doc : Doc.Doc) (marks : List Mark) : Except Error (Marks × List AuxStream) :=
  match marks.findSome? Mark.invalid with
  | some why => .error (.malformed 0 why)
  | none =>
    let gs := grouped marks
    let base := doc.file.trailer.size
    let flat := gs.flatMap Prod.snd
    match buildPages doc base (base + slotCount flat) gs with
    | .error e => .error e
    | .ok pages => .ok (pages, flat.map apOf)

/-- **Write `marks` into `doc`** as an incremental update (tasks 9.5a + 9.5b); `ivSeed` as
for `writeEdits`. -/
def writeMarks (limits : Limits) (doc : Doc.Doc) (marks : List Mark)
    (ivSeed : ByteArray := ByteArray.empty) : Except Error ByteArray :=
  match build doc marks with
  | .error e => .error e
  | .ok (ms, aux) => Incremental.writeAnnots limits doc ms aux ivSeed

/-! ## Edits of saved marks (rules A10, A11; task 9.5g) -/

/-- A mark whose annotation is already in the file, to be superseded (rule A10). -/
structure SupMark where
  /-- The new mark record (same id). -/
  mark : Mark
  /-- The annotation object `(num, gen)` in the file. -/
  ref : Nat × Nat
  /-- Its existing `/Popup` object, if any. -/
  popup : Option (Nat × Nat) := none
  deriving Repr, Inhabited

/-- Whether the superseded highlight needs a new popup object (it gains a comment). -/
def SupMark.freshPopup (s : SupMark) : Bool := s.mark.hasPopup && s.popup.isNone

/-- The popup to remove from the page (the highlight loses its comment). -/
def SupMark.dropPopup (s : SupMark) : Option (Nat × Nat) :=
  if s.mark.hasPopup then none else s.popup

/-- The changes of one save (rule A10). -/
structure EditSet where
  /-- New marks. -/
  adds : List Mark := []
  /-- Marks already in the file, rewritten. -/
  sups : List SupMark := []
  /-- Annotations removed: page index and object `(num, gen)`. -/
  removes : List (Nat × Nat × Nat) := []
  deriving Repr, Inhabited

/-- The `removes` entries deleting a mark stored at `ref` with popup `popup` on page `page`
(rule A10: a highlight's popup goes with it). -/
def removeMark (page : Nat) (ref : Nat × Nat) (popup : Option (Nat × Nat)) :
    List (Nat × Nat × Nat) :=
  (page, ref.1, ref.2) :: (popup.map fun r => (page, r.1, r.2)).toList

/-- Distinct elements in order of first occurrence. -/
def dedup : List Nat → List Nat
  | [] => []
  | x :: xs => x :: (dedup xs).filter (· != x)

/-- The pages whose `/Annots` change (rule A10), in order of first occurrence. -/
def EditSet.pages (e : EditSet) : List Nat :=
  dedup (e.adds.map (·.page) ++
    (e.sups.filter fun s => s.freshPopup || s.dropPopup.isSome).map (·.mark.page) ++
    e.removes.map (·.1))

/-- Number a list from `n`. -/
def numbered {α : Type} : Nat → List α → List (α × Nat)
  | _, [] => []
  | n, a :: as => (a, n) :: numbered (n + 1) as

/-- The page edits of `pages` (rule A10): added marks' dictionaries numbered from `num`
(appearance streams from `ap`), then new popups of superseded highlights; removed references
(explicit ones, then popups dropped). Also returns the fresh popup number of each superseded
highlight that gains one. -/
def editPages (doc : Doc.Doc) (e : EditSet) : Nat → Nat → List Nat →
    Except Error (Incremental.Edits × List ((Nat × Nat) × Nat))
  | _, _, [] => .ok ([], [])
  | num, ap, p :: rest =>
    match pageRef doc p with
    | .error err => .error err
    | .ok r =>
      let ms := e.adds.filter (·.page == p)
      let n1 := num + slotCount ms
      let fp := numbered n1 (e.sups.filter fun s => s.mark.page == p && s.freshPopup)
      let pops := fp.map fun (s, _) => popupDictP s.mark (.ref s.ref.1 s.ref.2) r
      let rem := (e.removes.filter (·.1 == p)).map (fun x => (x.2.1, x.2.2)) ++
        (e.sups.filter (·.mark.page == p)).filterMap SupMark.dropPopup
      match editPages doc e (n1 + fp.length) (ap + ms.length) rest with
      | .error err => .error err
      | .ok (pes, fresh) =>
        .ok (⟨p, rem, pageDicts r num ap ms ++ pops⟩ :: pes,
          fp.map (fun (s, n) => (s.ref, n)) ++ fresh)

/-- The superseding objects of one mark (rule A10): its dictionary under its own number and
generation, and its kept popup's. -/
def supDicts (doc : Doc.Doc) (fresh : List ((Nat × Nat) × Nat)) (s : SupMark) (ap : Nat) :
    Except Error (List Incremental.Supersede) :=
  match pageRef doc s.mark.page with
  | .error err => .error err
  | .ok r =>
    let self : PdfObject := .ref s.ref.1 s.ref.2
    match s.mark.kind with
    | .note => .ok [(s.ref.1, s.ref.2, noteDict s.mark ap r)]
    | .freeText => .ok [(s.ref.1, s.ref.2, freeTextDict s.mark ap r)]
    | .ink => .ok [(s.ref.1, s.ref.2, inkDict s.mark ap r)]
    | .highlight =>
      let popRef : PdfObject := match s.popup with
        | some pr => .ref pr.1 pr.2
        | none => match fresh.lookup s.ref with
          | some n => .ref n 0
          | none => .null
      let keep := match s.popup with
        | some pr => if s.mark.hasPopup then [(pr.1, pr.2, popupDictP s.mark self r)] else []
        | none => []
      .ok ((s.ref.1, s.ref.2, highlightDictP s.mark popRef ap r) :: keep)

/-- All superseding objects, appearance streams numbered from `ap`. -/
def allSups (doc : Doc.Doc) (fresh : List ((Nat × Nat) × Nat)) :
    Nat → List SupMark → Except Error (List Incremental.Supersede)
  | _, [] => .ok []
  | ap, s :: ss =>
    match supDicts doc fresh s ap, allSups doc fresh (ap + 1) ss with
    | .ok a, .ok b => .ok (a ++ b)
    | .error err, _ => .error err
    | _, .error err => .error err

/-- **The writer's input for an edit set** (rules A1–A11): page edits, supersessions and
appearance streams, numbered as `Incremental.writeUpdate` will number them for `doc`. -/
def buildEdits (doc : Doc.Doc) (e : EditSet) :
    Except Error (Incremental.Edits × List Incremental.Supersede × List AuxStream) :=
  let all := e.adds ++ e.sups.map (·.mark)
  match all.findSome? Mark.invalid with
  | some why => .error (.malformed 0 why)
  | none =>
    let pages := e.pages
    let base := doc.file.trailer.size
    let nAnn := (pages.map fun p =>
      slotCount (e.adds.filter (·.page == p)) +
        (e.sups.filter fun s => s.mark.page == p && s.freshPopup).length).sum
    let apBase := base + nAnn
    match editPages doc e base apBase pages with
    | .error err => .error err
    | .ok (pes, fresh) =>
      let addAps := (pages.flatMap fun p => e.adds.filter (·.page == p)).map apOf
      match allSups doc fresh (apBase + addAps.length) e.sups with
      | .error err => .error err
      | .ok sups => .ok (pes, sups, addAps ++ e.sups.map (apOf ·.mark))

/-- **Write an edit set into `doc`** as one incremental update (tasks 9.5a, 9.5b, 9.5g);
`ivSeed` feeds the AES IVs of an encrypted document (task 12.4). -/
def writeEdits (limits : Limits) (doc : Doc.Doc) (e : EditSet)
    (ivSeed : ByteArray := ByteArray.empty) : Except Error ByteArray :=
  match buildEdits doc e with
  | .error err => .error err
  | .ok (pes, sups, aux) => Incremental.writeUpdate limits doc pes sups aux ivSeed

/-! ## Properties -/

/-- Every page's dictionaries are annotation dictionaries (`IsAnnot`). -/
theorem pageDicts_isAnnot (page : PdfObject) :
    ∀ (num ap : Nat) (ms : List Mark), ∀ d ∈ pageDicts page num ap ms, IsAnnot d
  | _, _, [] => by simp [pageDicts]
  | num, ap, m :: ms => by
    intro d hd
    simp only [pageDicts, List.mem_append] at hd
    rcases hd with hd | hd
    · exact annotDicts_isAnnot m num ap page d hd
    · exact pageDicts_isAnnot page _ _ ms d hd

/-- A page's dictionary count is its marks' slot count. -/
theorem pageDicts_length (page : PdfObject) :
    ∀ (num ap : Nat) (ms : List Mark), (pageDicts page num ap ms).length = slotCount ms
  | _, _, [] => by simp [pageDicts, slotCount]
  | num, ap, m :: ms => by
    simp only [pageDicts, List.length_append, annotDicts_length, pageDicts_length page _ _ ms,
      slotCount, List.map_cons, List.sum_cons]

/-- `buildPages` keeps the page indices and gives `IsAnnot` dictionaries. -/
theorem buildPages_ok (doc : Doc.Doc) :
    ∀ (num ap : Nat) (gs : List (Nat × List Mark)) (xs : List (Nat × List Dict)),
      buildPages doc num ap gs = .ok xs →
      xs.map Prod.fst = gs.map Prod.fst ∧ ∀ x ∈ xs, ∀ d ∈ x.2, IsAnnot d
  | _, _, [], xs, h => by
    simp only [buildPages, Except.ok.injEq] at h
    subst h
    simp
  | num, ap, (p, ms) :: rest, xs, h => by
    simp only [buildPages] at h
    split at h
    · cases h
    · rename_i r _
      split at h
      · cases h
      · rename_i ys hys
        cases h
        obtain ⟨h1, h2⟩ := buildPages_ok doc _ _ rest ys hys
        refine ⟨by simp [h1], ?_⟩
        intro x hx d hd
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact pageDicts_isAnnot r _ _ ms d hd
        · exact h2 x hx d hd

/-- **Every dictionary `build` emits is an annotation dictionary** with `/Type /Annot`,
`/Subtype`, `/Rect` and `/NM` (`IsAnnot`, `IsAnnot.lookup`); the pages are those of the
marks, in order of first occurrence, each once; there is one appearance stream per mark. -/
theorem build_ok {doc : Doc.Doc} {marks : List Mark} {ms : Marks} {aux : List AuxStream}
    (h : build doc marks = .ok (ms, aux)) :
    ms.map Prod.fst = pageOrder marks ∧ (∀ x ∈ ms, ∀ d ∈ x.2, IsAnnot d) ∧
      aux = ((grouped marks).flatMap Prod.snd).map apOf := by
  unfold build at h
  split at h
  · cases h
  · dsimp only at h
    split at h
    · cases h
    · rename_i pages hp
      cases h
      obtain ⟨h1, h2⟩ := buildPages_ok doc _ _ _ _ hp
      refine ⟨?_, h2, rfl⟩
      rw [h1]
      simp [grouped, Function.comp_def]

/-- **Quads map 1:1 (count)**: eight `/QuadPoints` numbers per quad. -/
theorem quadPoints_length (qs : List Quad) : (quadPoints qs).length = 8 * qs.length := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    simp only [quadPoints, List.flatMap_cons, List.length_append, Quad.points] at ih ⊢
    simp only [List.length_cons, List.length_nil, ih]
    omega

/-- Reading one quad's eight numbers in front of others. -/
theorem quadsOf_cons (q : Quad) (rest : List Rat) :
    Annot.quadsOf (q.points ++ rest) = q.toAnnot :: Annot.quadsOf rest := by
  unfold Annot.quadsOf
  have hl : ((q.points ++ rest).length + 7) / 8 = (rest.length + 7) / 8 + 1 := by
    simp [Quad.points]; omega
  rw [hl, List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map]
  congr 1

/-- **Quads map 1:1 (read back)**: `Core.Annot.quadsOf`, the `/QuadPoints` reader of our
annotation renderer, reads exactly the given quads from `quadPoints`. -/
theorem quadsOf_quadPoints (qs : List Quad) :
    Annot.quadsOf (quadPoints qs) = qs.map Quad.toAnnot := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    simp only [quadPoints, List.flatMap_cons] at ih ⊢
    rw [quadsOf_cons, ih, List.map_cons]

/-! ### Free text and ink (rules A12–A15) -/

/-- The head of `mkAnnot`: `/Subtype`, `/Rect` and `/NM` are the given ones. -/
theorem mkAnnot_lookup (sub : String) (rect : PdfObject) (n : String) (rest : Dict) :
    Dict.lookup (mkAnnot sub rect n rest) kSubtype = some (.name (nm sub)) ∧
    Dict.lookup (mkAnnot sub rect n rest) kRect = some rect ∧
    Dict.lookup (mkAnnot sub rect n rest) kNM = some (.string (textBytes n)) := by
  have h1 : kType ≠ kSubtype := by decide
  have h2 : kType ≠ kRect := by decide
  have h3 : kSubtype ≠ kRect := by decide
  have h4 : kType ≠ kNM := by decide
  have h5 : kSubtype ≠ kNM := by decide
  have h6 : kRect ≠ kNM := by decide
  refine ⟨?_, ?_, ?_⟩ <;> simp [mkAnnot, Dict.lookup, h1, h2, h3, h4, h5, h6]

/-- The first entry after the head of `mkAnnot` is found by its key (when that key is none of
`/Type`, `/Subtype`, `/Rect`, `/NM`). -/
theorem mkAnnot_lookup_first (sub : String) (rect : PdfObject) (n : String) (k : Name)
    (v : PdfObject) (rest : Dict) (h1 : kType ≠ k) (h2 : kSubtype ≠ k) (h3 : kRect ≠ k)
    (h4 : kNM ≠ k) : Dict.lookup (mkAnnot sub rect n ((k, v) :: rest)) k = some v := by
  simp [mkAnnot, Dict.lookup, h1, h2, h3, h4]

/-- **Free-text dictionary shape** (rule A12): `/Subtype /FreeText`, `/Rect` the text box,
`/NM` the mark's name, `/Contents` its text (rule A6). -/
theorem freeTextDict_shape (m : Mark) (ap : Nat) (page : PdfObject) :
    Dict.lookup (freeTextDict m ap page) kSubtype = some (.name (nm "FreeText")) ∧
    Dict.lookup (freeTextDict m ap page) kRect = some (rectObj m.annotRect) ∧
    Dict.lookup (freeTextDict m ap page) kNM = some (.string (textBytes (nmOf m.id))) ∧
    Dict.lookup (freeTextDict m ap page) kContents = some (.string (textBytes m.contents)) := by
  obtain ⟨a, b, c⟩ := mkAnnot_lookup "FreeText" (rectObj m.annotRect) (nmOf m.id)
    ([(kContents, .string (textBytes m.contents)), (kDA, .string (daBytes m)),
      (nm "F", .int 4), (nm "Border", .array [.int 0, .int 0, .int 0]),
      (nm "M", asciiStr m.date),
      (nm "CreationDate", asciiStr (if m.created.isEmpty then m.date else m.created))] ++
    opt (!m.author.isEmpty) "T" (.string (textBytes m.author)) ++
    [(nm "P", page), (kAP, .dict [(nm "N", .ref ap 0)])])
  refine ⟨a, b, c, ?_⟩
  exact mkAnnot_lookup_first _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide)

/-- **Ink dictionary shape** (rule A14): `/Subtype /Ink`, `/Rect` the ink box, `/NM` the
mark's name, `/InkList` one array per stroke (`inkListObj`). -/
theorem inkDict_shape (m : Mark) (ap : Nat) (page : PdfObject) :
    Dict.lookup (inkDict m ap page) kSubtype = some (.name (nm "Ink")) ∧
    Dict.lookup (inkDict m ap page) kRect = some (rectObj m.annotRect) ∧
    Dict.lookup (inkDict m ap page) kNM = some (.string (textBytes (nmOf m.id))) ∧
    Dict.lookup (inkDict m ap page) kInkList = some (.array (inkListObj m.strokes)) := by
  obtain ⟨a, b, c⟩ := mkAnnot_lookup "Ink" (rectObj m.annotRect) (nmOf m.id)
    ([(kInkList, .array (inkListObj m.strokes)),
      (nm "BS", .dict [(nm "W", coord m.lineWidth)])] ++ common m ++
    [(nm "P", page), (kAP, .dict [(nm "N", .ref ap 0)])])
  refine ⟨a, b, c, ?_⟩
  exact mkAnnot_lookup_first _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide)

/-- **InkList ↔ strokes 1:1 (count)**: one `/InkList` array per stroke. -/
theorem inkListObj_length (ss : List (List (Rat × Rat))) : (inkListObj ss).length = ss.length :=
  List.length_map ..

/-- **InkList ↔ strokes 1:1 (position)**: the `i`-th `/InkList` array is the `i`-th stroke's
numbers. -/
theorem inkListObj_getElem? (ss : List (List (Rat × Rat))) (i : Nat) :
    (inkListObj ss)[i]? = ss[i]?.map fun s => .array (strokeNums s) :=
  List.getElem?_map ..

/-- **Points ↔ numbers**: two numbers per point of a stroke. -/
theorem strokeNums_length (s : List (Rat × Rat)) : (strokeNums s).length = 2 * s.length := by
  induction s with
  | nil => rfl
  | cons p ps ih =>
    simp only [strokeNums, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil] at ih ⊢
    omega

/-- Free text and ink yield one dictionary each (no popup). -/
theorem slots_freeText_ink (m : Mark) (h : m.kind = .freeText ∨ m.kind = .ink) :
    m.slots = 1 := by
  rcases h with h | h <;> simp [Mark.slots, Mark.hasPopup, h]

/-- Printing a string object round-trips through the strict parser (M1's
`Spec.RoundTripCore.parseObject_print`, via `Spec.Write.serialize_roundtrip`'s hypotheses):
strings are always canonical, so every text string we write is read back exactly. -/
theorem string_canonical (bs : List UInt8) : (PdfObject.string bs).Canonical := rfl

/-- Every coordinate and colour number we write is canonical. -/
theorem coord_canonical (q : Rat) : (coord q).Canonical := decRound_canonical 3 q

/-! ## Compile-time checks -/

section Tests

#guard textBytes "Hi there\n" == ascii "Hi there\n"
#guard textBytes "é" == [0xFE, 0xFF, 0x00, 0xE9]
#guard textBytes "a😀" == [0xFE, 0xFF, 0x00, 0x61, 0xD8, 0x3D, 0xDE, 0x00]
#guard Annot.textOf (textBytes "Grüße 😀 €") == "Grüße 😀 €".toList
-- every plain character reads back as itself (PDFDocEncoding = ASCII there)
#guard (List.range 128).all fun n =>
  !plainChar (Char.ofNat n) || Annot.textOf [UInt8.ofNat n] == [Char.ofNat n]
#guard decRound 3 (1 / 3) == ⟨333, 3⟩
#guard decRound 4 (152 / 255) == ⟨5961, 4⟩
#guard decRound 3 100 == ⟨100, 0⟩
#guard decFloor 3 (-1 / 3) == ⟨-334, 3⟩ && decCeil 3 (1 / 3) == ⟨334, 3⟩
#guard (Quad.ofBox 1 2 3 4).points == [1, 4, 3, 4, 1, 2, 3, 2]
#guard Annot.quadsOf (Quad.ofBox 1 2 3 4).points == [(Quad.ofBox 1 2 3 4).toAnnot]
/-- A test note on page `p`. -/
private def tnote (p i : Nat) : Mark :=
  { page := p, kind := .note, quads := [], rect := ⟨0, 0, 1, 1⟩, color := (1, 1, 0), id := i,
    date := "" }

#guard pageOrder [tnote 2 1, tnote 0 2, tnote 2 3] == [2, 0]
#guard (grouped [tnote 2 1, tnote 0 2, tnote 2 3]).map (fun g => (g.1, g.2.map (·.id))) ==
  [(2, [1, 3]), (0, [2])]
#guard op [coord 1.5, coord 2] "m" == ascii "1.5 2. m\n"
#guard dedup [3, 1, 3, 2, 1] == [3, 1, 2]
#guard popupNm { tnote 0 4 with commentId := some 9 } == "safepdf-mark-4-popup-9"
#guard popupNm (tnote 0 4) == "safepdf-mark-4-popup"
#guard removeMark 1 (5, 0) (some (6, 0)) == [(1, 5, 0), (1, 6, 0)]
-- Free text: Helvetica widths (H 722, i 222, space 278, `·` 278 for ✓), 2 lines of 1.35 × 12.
#guard freeTextBox 100 700 12 "Hi ✓\nAB" == ⟨100, 3318 / 5, 122, 700⟩
#guard drawnChar '✓' == '·' && drawnChar 'é' == 'é' && drawnChar '€' == '€'
#guard textLines "a\r\nb" == [['a'], ['b']]
#guard daBytes { tnote 0 1 with kind := .freeText, color := (1, 0, 0), fontSize := 12 } ==
  ascii "/Helv 12. Tf 1. 0. 0. rg"
-- Ink: the box grows by the line width; a one-point stroke is a dot; `/R0 gs` below opacity 1.
#guard inkBox [[(10, 10), (20, 30)], [(5, 5)]] 3 == some ⟨2, 2, 23, 33⟩
#guard inkBox [] 3 == none
#guard strokePath [(5, 5)] == ascii "5. 5. m\n5. 5. l\n"
/-- A test ink mark. -/
private def tink : Mark :=
  { tnote 0 1 with kind := .ink, color := (0, 0, 1), opacity := 1 / 2,
                   strokes := [[(10, 10), (20, 30)]], lineWidth := 3 }

#guard inkContent tink ==
  ascii "3. w\n1 J\n1 j\n0. 0. 1. RG\n/R0 gs\n10. 10. m\n20. 30. l\nS\n"
#guard (Mark.invalid { tnote 0 1 with kind := .ink }).isSome &&
  (Mark.invalid { tnote 0 1 with kind := .ink, strokes := [[]] }).isSome &&
  (Mark.invalid { tnote 0 1 with kind := .ink, strokes := [[(1, 1)]] }).isNone

end Tests

end SafePdf.Core.Write.Annots
