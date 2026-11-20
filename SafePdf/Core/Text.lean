import SafePdf.Core.Content.Run
import SafePdf.Core.Font.Widths
import SafePdf.Core.Font.Type1
import SafePdf.Core.Font.CFF
import SafePdf.Core.Font.TrueType
import SafePdf.Core.Font.CMap
import SafePdf.Core.Doc

/-!
# Text extraction from the display list (Plan.md §6 Phase 6, §3 C3 and C6; task 6.5)

Fonts of a page are resolved once, the page is run through the content runner
(`Core.Content.runBytes`, task 5.2b) **with real glyph advances**, and text is read back
**only** from the `glyphRun` items of the display list that this run produced. ISO 32000-2
references: §9.4.4 (glyph positioning), §9.6–9.7 (simple and composite fonts), §9.10
(extraction of text content), §9.3.3 (word spacing applies to the single-byte code 32).

## Fonts (`FontInfo`, `loadFonts`)

Fonts are identified by their **object** (task 6.7a), as the runner records it in
`FontRef.id` (`Core.Content.Run`): the font table (`FontTable`) is keyed by `FontKey`, the
indirect reference of the font dictionary, or, for a direct dictionary, the resource name in
the resources of its owner (the page, or the form XObject whose own `/Resources` hold it). So
a form whose `/F1` differs from the page's `/F1` gets its own metrics and Unicode map, a font
object shared under several names or by several forms is parsed once, and an ExtGState
`/Font` (`gs`) is found by its reference. `loadFonts` collects the `/Font` and ExtGState
`/Font` entries of the page's resources and, through the page's form XObjects recursively, of
every form with its own `/Resources` (at most `maxFormFonts` resource dictionaries, each form
once, at most `maxFormFonts` XObjects inspected per dictionary). A name a form's own resources
do not define falls back to the page's font of that name (`FontTable.get`; sloppy producers
rely on it); a name no resources define, or a font object that is not a dictionary, gets
MuPDF's substitute Times-Roman (`FontInfo.unknown`, task 6.12). Every collected font object becomes a `FontInfo`:

* **Code splitting** (`SplitKind`): one byte for simple fonts; two bytes for Type0 with
  `Identity-H`/`-V`; for other Type0 fonts the `codespacerange` of an embedded `/Encoding` CMap,
  else of the `/ToUnicode` CMap, else two bytes. Every split concatenates back to the shown
  string (`SplitKind.codes_flatten`).
* **Widths** (text-space `w0`, glyph width / 1000): `Font.FontMetrics.ofDict` (task 6.4); for a
  simple Type 1 font whose width is unknown there (no `/Widths`, not a standard 14 font) the
  embedded program (`/FontDescriptor /FontFile`, `Font.Type1.parse`, task 6.3) gives the
  advance of the glyph the font's encoding names, and likewise an embedded CFF program
  (`/FontFile3 /Subtype /Type1C`, `Font.CFF.parse`, tasks 6.2/6.2b: the glyph the encoding
  names through the CFF charset, else the glyph the code selects through the CFF's own
  encoding); Type 3 widths are scaled by `/FontMatrix`; Type0 fonts take `/W`, then `/DW`;
  a CID with neither, in a `/CIDFontType0` descendant with an embedded CFF
  (`/FontFile3 /Subtype /CIDFontType0C`), takes the CFF advance of that CID (CID → GID
  through the CFF charset, `CFFFont.advanceOfCID`); in a `/CIDFontType2` descendant with an
  embedded TrueType program (`/FontFile2`, `Font.TrueType.parse`, task 6.1) the CID selects a
  glyph through `/CIDToGIDMap` (`/Identity`, the default, or a stream of 2-byte GIDs,
  `CIDToGID`; a CID past the stream's end has no glyph) and takes its `hmtx` advance scaled by
  `unitsPerEm` (task 6.7c); a CID without any of these takes 1000. A simple `/TrueType` font
  with an embedded program takes, for every code that `/Widths` (or, with `/Widths`,
  `/MissingWidth`) does not cover, the advance of the code's glyph under the cmap rules of
  §9.6.6.4 (`TTFont.advanceText`; symbolic per the descriptor's `/Flags` bit 3, otherwise
  through the font's encoding), ahead of the standard 14 metrics (`ttWidthTable`). Each
  program is parsed once per font object (`loadFonts` builds every `FontKey` once) and only
  when some width needs it. Type0 fonts with another CMap than
  `Identity-H/V` use CID = code value (an approximation: CID mapping through non-identity
  CMaps is not implemented). `/FontFile3 /Subtype /OpenType` is not read (unsupported).
* **Unicode** (§9.10.2), in order: the `/ToUnicode` CMap (`Font.CMap`; for simple fonts a
  mapping to control characters only is ignored as a producer error); for simple fonts the
  encoding's glyph name through the Adobe Glyph List (`Font.glyphToUnicode`; the encoding uses
  the embedded Type 1 or CFF program's built-in encoding as base when the program was parsed —
  for CFF, the code's glyph name through the CFF encoding and charset,
  `CFFFont.glyphNameOfCode`; the program is also read when a `/ToUnicode` CMap leaves a code
  with a non-zero width unmapped, `toUnicodeCovers`; glyph names through the full AGL and the
  TeX glyph list, task 6.7b); for Type 3 fonts only (as MuPDF) a code in `32..126` without a
  glyph name or whose glyph name the glyph list does not know, as that ASCII character (dvips
  Type 3 bitmap fonts); for Type0
  fonts with a predefined `UCS2`/`UTF16` CMap the code read as UTF-16BE; otherwise nothing
  (`Identity-H` with `Adobe-Identity`: no mapping, §9.10.2) and the glyph's text is U+FFFD.
  Ligatures U+FB00–FB06 are decomposed (`fi` → "fi"), control characters become spaces.
* Every embedded program is parsed under `Limits` (Type 1: `maxFontGlyphs`, `maxFontSubrs`,
  `glyphFuel`; CFF: `maxCFFGlyphs`, `maxFontSubrs`, `maxFontDicts`, `glyphFuel`, `fontFuel`)
  and only when its metrics or encoding are needed; a program that fails to parse (malformed
  or over a limit) is ignored and the dictionary's own information is used.
* Object fetches for font dictionaries use the source's state at font-loading time and drop
  the state change (fetching is not charged by the document source); stream decodes
  (`/ToUnicode`, `/FontFile`, embedded CMaps) are threaded through the source state, i.e.
  charged to the document's decode budget.

## Positions (`runGlyphs`)

The advance handed to the runner (`advanceFn`) is, per code, `((w0 · Tfs) + Tc + Tw?) · Th`
(`Tw` only for the single-byte code 32), the per-string sum; `TJ` numbers are applied by the
interpreter itself. Extraction recomputes the same sums inside each run: the glyph at text-space
offset `tx` has its origin at `(tx, Ts)` mapped by `Tm × CTM` (equal to `(0, 0)` mapped by the
text rendering matrix of §9.4.4), its width is the page-space extent of its advance along its baseline direction, and its
page-space font size is `|Tfs| · √|det(diag(Th, 1) × M)|` for `M = Tm × CTM` (`expansion`,
MuPDF's `fz_matrix_expansion` of its text rendering matrix, task 6.8e; times an em estimate
for Type 3 fonts, whose glyph space has no em: `type3SizeScale`). Its own advance
`w0 · Tfs · Th` without `Tc`/`Tw` is `Glyph.adv`, its exact baseline direction
`Glyph.dirX/dirY`. Type 3 advances are
truncated to multiples of `1/1000` em as MuPDF's integer metrics table (`type3TruncWidth`,
task 7.3l).

## Reading order (`layout`; heuristic, tested not proven, Plan.md §6)

Glyphs are taken in content-stream order (filtered to visible ones unless
`Options.includeInvisible`, the default being to keep invisible text such as OCR layers, and
leaving out glyphs whose box — advance × [−0.2, 0.8] of the size, `Glyph.bounds` — lies
entirely outside `Options.pageBox`, the CropBox for document pages: MuPDF's `FZ_STEXT_CLIP`,
task 6.8b; e.g. a mailing panel drawn above the CropBox of a cover page; glyphs entirely
outside the bounding box of their run's clip are already gone from `PageText.shown`,
`unclipped`, task 6.8f). A glyph joins the current line when its baseline is within `lineTol`
(‰ of **its own** font size, as MuPDF measures offsets in units of the glyph added; task 6.8e)
of the line's, when it continues the line's last glyph as MuPDF's text device would
(`nearPrev`: baseline offset below `baseMax`, distance from that glyph's pen below `spaceMax`,
both 0.8 em; e.g. a raised radical sign `√`), or when it is a **sub/superscript** of the line (`scriptJoin`, task 6.7c): a glyph of
smaller size raised by at most `scriptRaise` ‰ of the line's size, or a larger glyph lying that
far below a line of smaller glyphs (a footnote begun by its marker), provided it continues the
line horizontally (`continuesLine`: from `scriptBack` before to `scriptAhead` after the line's
end); otherwise it starts a new line. A line's baseline is that of its largest glyphs. The
expected results follow MuPDF (`mutool draw -F txt`), except that stacked scripts stay on the
line (`Tests/TextLayout.lean`). Lines keep content-stream order (which follows columns
in TeX and word-processor output; a global top-to-bottom sort would interleave columns), glyphs
inside a line are sorted left to right (stable), except that a glyph **attached** to the glyph
shown before it — moved back behind that glyph's origin, but by less than `attachBack` ‰ of the
size past its advance end, i.e. overlapping it — keeps content order (`lineOrder`, task 6.7d):
an accent built as a separate glyph and drawn before its base letter (TeX's `\c{c}`, `\.z`)
stays before it, as in MuPDF (`¸ca`, `˙z`). A space is inserted where the gap between a
glyph's **pen** — its origin plus its own advance `w0 · Tfs · Th`, without `Tc` and `Tw`
(`Glyph.adv`), as MuPDF — and the next origin exceeds `wordGap` ‰ of the next glyph's font size
(gaps from `TJ` numbers, `Td` moves and character spacing alike, so letter-spaced capitals read
`R A I L`; 0.15 em, MuPDF's `SPACE_DIST`; task 6.8e), unless either side already is a
space or the text before the gap ends in a character after which MuPDF never inserts one
(`spaceMayFollow`: U+0700 and above outside U+2000–U+20CF, e.g. the math operators of `a −b`,
`c ≤d`, and CJK); an overprinted duplicate
(same text from the same code bytes, origin within 10 % of the size: fake bold) is dropped
(an `/ActualText` character placed on another code, e.g. a dot leader's space shown as '.'
next to a real '.', is not a duplicate; task 6.8d). Lines are separated by a
newline, with a blank line when the baselines are more than `paraGap` ‰ of the font size of the
second line apart (`lineSep`).
Lines need the same quarter turn (`dirOf`: the quarter turn nearest to the image of the text x
axis) and the same exact baseline direction (`Frame.same`: cosine at least 0.999, MuPDF's
test); positions are measured in the exact frame of a line's first glyph (`Glyph.dirX/dirY`,
task 6.8e), so text rotated by any angle — 90° pages, 45° or 30° chart labels — groups and
orders like upright text. (`Glyph.u`/`v`/`bounds` stay in the quarter-turn frame, the boxes the
API and the viewer draw.)

## `/ActualText` (`shownItems`, task 6.8d; as MuPDF 1.25.1 `stext-device.c`)

The interpreter brackets marked content whose property list has `/ActualText` (inline, or a
`/Properties` resource) by `actualTextBegin text` … `actualTextEnd` items. The glyphs as shown
(`PageText.shown`, from which lines and text are laid out) replace each glyph inside such a
sequence by the next ActualText character, at the glyph's own position and advance (MuPDF
`do_extract_within_actualtext`); the innermost sequence applies; glyphs beyond the characters,
and every glyph of an empty ActualText, are dropped; characters left when the sequence closes
(or at the end of the page) are placed as zero-width glyphs at the advance end of the last glyph
placed (MuPDF's pen, `flush_actualtext`). E.g. an NTSB table-of-contents leader: a space shown
under `/ActualText (.)` reads `.`. Not done: MuPDF's prefix/postfix matching (it compares glyph
ids with Unicode values, so it only fires by coincidence), `/ActualText` of the structure
element an `/MCID` points to, and the text of a sequence closed before any glyph of the page
was placed (MuPDF puts it at the bounds of the sequence's images and paths; here it is
dropped). A form's sequences left open at its end are closed only at the end of the page (MuPDF
closes them with the form). `PageText.glyphs` stays the plain extraction (C3/C6 below);
without `/ActualText` marks the two are equal (`shownItems_eq_extract`).

## Properties

* **C6, extracted = displayed** (`extractPage_glyphs`, `extract_from_items`): the glyphs of a
  page are exactly `extractItems` of the display list the runner produced in the same pass, and
  every glyph is recomputed from a `glyphRun` item of that list (its index `item`).
* **C3, text ↔ position** (`extract_from_items`, `runGlyphs_codes`): from a glyph's provenance
  `(item, seq)` the display list alone recomputes the very same glyph — text, code bytes,
  origin, width, size (`(runGlyphs fonts g.item r)[g.seq]? = some g`) — and the code bytes of a
  run's glyphs concatenate to the bytes the run showed (no byte dropped or invented). The
  reading-order heuristic is outside the theorem (tested).
-/

namespace SafePdf.Core.Text

open SafePdf
open SafePdf.Core.Content
open SafePdf.Core.Font (Encoding FontMetrics SimpleMetrics CIDMetrics WidthSource glyphToUnicode
  getR glyphNameOf)

/-! ## Small helpers -/

/-- Absolute value. -/
def fabs (x : Fixed) : Fixed := if x.raw < 0 then Fixed.neg x else x

/-- Maximum. -/
def fmax (x y : Fixed) : Fixed := if x.raw < y.raw then y else x

/-- A name. -/
def nm (s : String) : Name := Name.ofString s

/-- The text of a name. -/
def nameStr? : Option PdfObject → Option String
  | some (.name n) => some (glyphNameOf n.bytes)
  | _ => none

/-- U+FFFD as a string. -/
def replacementStr : String := String.ofList [Font.CMap.replacement]

/-- Compatibility decomposition of the Latin ligatures U+FB00–FB06; control characters
become spaces (NUL is dropped). -/
def normChar (c : Char) : List Char :=
  match c.toNat with
  | 0xFB00 => ['f', 'f']
  | 0xFB01 => ['f', 'i']
  | 0xFB02 => ['f', 'l']
  | 0xFB03 => ['f', 'f', 'i']
  | 0xFB04 => ['f', 'f', 'l']
  | 0xFB05 => ['s', 't']
  | 0xFB06 => ['s', 't']
  | 0 => []
  | n => if n < 32 then [' '] else [c]

/-- Normalise extracted text (see `normChar`). -/
def normalize (s : String) : String := String.ofList (s.toList.flatMap normChar)

/-! ## Code splitting -/

/-- Two-byte codes; a trailing odd byte is a code of its own. -/
def pairs : List UInt8 → List (List UInt8)
  | a :: b :: rest => [a, b] :: pairs rest
  | [a] => [[a]]
  | [] => []

/-- Two-byte splitting consumes the string. -/
theorem pairs_flatten : ∀ bs : List UInt8, (pairs bs).flatten = bs
  | a :: b :: rest => by simp [pairs, pairs_flatten rest]
  | [a] => by simp [pairs]
  | [] => by simp [pairs]

/-- How a font's strings split into character codes. -/
inductive SplitKind where
  /-- Simple fonts: one byte per code. -/
  | one
  /-- Two bytes per code (Identity-H/V and the fallback for Type0). -/
  | two
  /-- By the codespace ranges of a CMap. -/
  | cmap (m : Font.CMap.CMap)

/-- The codes of a shown string. -/
def SplitKind.codes : SplitKind → List UInt8 → List (List UInt8)
  | .one, bs => bs.map fun b => [b]
  | .two, bs => pairs bs
  | .cmap m, bs => m.codes bs

/-- **Splitting consumes the string**: the codes concatenate to the shown bytes. -/
theorem SplitKind.codes_flatten (k : SplitKind) (bs : List UInt8) : (k.codes bs).flatten = bs := by
  cases k with
  | one => induction bs with
    | nil => rfl
    | cons b bs ih => simpa [SplitKind.codes] using ih
  | two => exact pairs_flatten bs
  | cmap m => exact m.codes_flatten bs

/-! ## Fonts -/

/-- What extraction and positioning need from a font. -/
structure FontInfo where
  /-- Code splitting. -/
  split : SplitKind
  /-- Horizontal advance `w0` of a code, in text space units per unit of font size. -/
  width : List UInt8 → Fixed
  /-- Unicode text of a code (before `normalize`), when known. -/
  unicode : List UInt8 → Option String
  /-- Short description (subtype, base font, sources), for diagnostics. -/
  desc : String
  /-- Em size in text space per unit of font size (1, except Type 3: `type3SizeScale`): the
  page-space font size is `|Tfs| · sizeScale · scale`. -/
  sizeScale : Fixed := Fixed.one

/-- The font dictionary of the substitute for a missing font: a non-embedded Times-Roman
(what MuPDF's `pdf_load_hail_mary_font` loads: `pdf_load_simple_font` of no dictionary, whose
empty `/BaseFont` becomes Times-Roman with `StandardEncoding`). -/
def hailMaryDict : Dict :=
  [(nm "Type", .name (nm "Font")), (nm "Subtype", .name (nm "Type1")),
    (nm "BaseFont", .name (nm "Times-Roman"))]

/-- The metrics of `hailMaryDict` (standard 14 Times-Roman widths, `StandardEncoding`). -/
def hailMaryMetrics : SimpleMetrics := SimpleMetrics.ofDict id hailMaryDict none

/-- The font used when `Tf` names no font resource, or one that is not a dictionary (task
6.12): as MuPDF, the "hail mary" font — one-byte codes, Times-Roman widths, Unicode through
`StandardEncoding` and the glyph list. A page without `/Resources` (as the encrypted fixtures
of `Tests/adversarial/encrypted/`) thus keeps its text and its glyph positions. -/
def FontInfo.unknown : FontInfo :=
  { split := .one
    width := fun c => match c with
      | [b] => (hailMaryMetrics.width b.toNat).1
      | _ => Fixed.zero
    unicode := fun c => match c with
      | [b] => (hailMaryMetrics.encoding.glyph b.toNat).bind (Font.glyphToUnicodeIn false)
      | _ => none
    desc := "missing (Times-Roman substitute)" }

instance : Inhabited FontInfo := ⟨FontInfo.unknown⟩

/-- The key of a font in a page's font table (see the module doc): the font dictionary's
indirect object, or a resource name in the resources of `owner` (`FontId.res`). -/
inductive FontKey where
  /-- Font dictionary object `num gen`. -/
  | obj (num gen : Nat)
  /-- Entry `name` of the `/Font` resources of `owner` (0: the page; else a form object). -/
  | res (owner : Nat) (name : Name)
  deriving DecidableEq, Repr, Inhabited

/-- The table key of a font reference (its `FontId`, with its name for `.res`). -/
def fontKey (f : FontRef) : FontKey :=
  match f.id with
  | .ref n g => .obj n g
  | .res o => .res o f.name

/-- Fonts by key; a referenced font is also listed under its resource names (`.res`), so the
fallback of `get` finds page fonts by name. -/
abbrev FontTable := List (FontKey × FontInfo)

/-- The font of a font reference: by its key, else (a name a form's resources do not define)
the page's font of that name, else `FontInfo.unknown`. -/
def FontTable.get (t : FontTable) (f : FontRef) : FontInfo :=
  match t.lookup (fontKey f) with
  | some fi => fi
  | none => (t.lookup (.res 0 f.name)).getD FontInfo.unknown

/-- Whether word spacing applies to a code (§9.3.3: the single-byte code 32). -/
def isSpaceCode (c : List UInt8) : Bool := c == [32]

/-- Displacement of one code in text space, `Th` included (§9.4.4, without `TJ` numbers). -/
def codeAdvance (fi : FontInfo) (ts : TextState) (size : Fixed) (c : List UInt8) : Fixed :=
  let th := Fixed.div ts.horizScaling (Fixed.ofInt 100)
  let tw := if isSpaceCode c then ts.wordSpacing else Fixed.zero
  Fixed.mul (Fixed.add (Fixed.add (Fixed.mul (fi.width c) size) ts.charSpacing) tw) th

/-- Sequential sum of code advances from `tx`. -/
def endTx (fi : FontInfo) (ts : TextState) (size : Fixed) (tx : Fixed) (cs : List (List UInt8)) :
    Fixed :=
  cs.foldl (fun t c => Fixed.add t (codeAdvance fi ts size c)) tx

/-- The advance the interpreter applies for a shown string (`Config.advance`). -/
def advanceFn (t : FontTable) (ts : TextState) (bs : List UInt8) : Fixed :=
  match ts.font with
  | some f =>
    let fi := t.get f
    endTx fi ts f.size Fixed.zero (fi.split.codes bs)
  | none => Fixed.zero

/-! ### Loading fonts through a `Source` -/

/-- Fetch a stream by reference and decode it: its dictionary and bytes. -/
def fetchStream {σ : Type} (src : Source σ) (s : σ) : PdfObject → Option (Dict × ByteArray) × σ
  | .ref n g =>
    match src.fetch s n g with
    | (.ok (.stream st), s1) =>
      match src.decode s1 n st with
      | (.ok b, s2) => (some (st.dict, b), s2)
      | (.error _, s2) => (none, s2)
    | (_, s1) => (none, s1)
  | _ => (none, s)

/-- A CMap stream entry `key` of `d`, parsed. -/
def cmapOf {σ : Type} (src : Source σ) (s : σ) (d : Dict) (key : String) :
    Option Font.CMap.CMap × σ :=
  match Dict.get? d (nm key) with
  | some o =>
    match fetchStream src s o with
    | (some (_, b), s') => (some (Font.CMap.parse b), s')
    | (none, s') => (none, s')
  | none => (none, s)

/-- Parse the embedded Type 1 program (`/FontDescriptor /FontFile`) of a font dictionary. -/
def loadType1 {σ : Type} (limits : Limits) (src : Source σ) (s : σ)
    (resolve : PdfObject → PdfObject) (fd : Dict) : Option Font.Type1.Font1 × σ :=
  match getR resolve fd "FontDescriptor" with
  | some (.dict desc) =>
    match Dict.get? desc (nm "FontFile") with
    | some o =>
      match fetchStream src s o with
      | (some (sd, bytes), s') =>
        let len (k : String) : Option Nat :=
          match getR resolve sd k with
          | some (.int i) => if 0 ≤ i then some i.toNat else none
          | _ => none
        match Font.Type1.parse limits bytes (len "Length1") (len "Length2") with
        | .ok f => (some f, s')
        | .error _ => (none, s')
      | (none, s') => (none, s')
    | none => (none, s)
  | _ => (none, s)

/-- Parse the embedded CFF program (`/FontFile3`) of a font dictionary `fd` (a simple font, or
the descendant CIDFont of a Type0 font) when the stream's `/Subtype` is one of `subtypes`. -/
def loadCFF {σ : Type} (limits : Limits) (src : Source σ) (s : σ)
    (resolve : PdfObject → PdfObject) (fd : Dict) (subtypes : List String) :
    Option Font.CFF.CFFFont × σ :=
  match getR resolve fd "FontDescriptor" with
  | some (.dict desc) =>
    match Dict.get? desc (nm "FontFile3") with
    | some o =>
      match fetchStream src s o with
      | (some (sd, bytes), s') =>
        if subtypes.contains ((nameStr? (getR resolve sd "Subtype")).getD "") then
          ((Font.CFF.parse limits bytes).toOption, s')
        else (none, s')
      | (none, s') => (none, s')
    | none => (none, s)
  | _ => (none, s)

/-- Parse the embedded TrueType program (`/FontDescriptor /FontFile2`) of a font dictionary `fd`
(a simple `/TrueType` font, or the `/CIDFontType2` descendant of a Type0 font). -/
def loadTT {σ : Type} (limits : Limits) (src : Source σ) (s : σ)
    (resolve : PdfObject → PdfObject) (fd : Dict) : Option Font.TrueType.TTFont × σ :=
  match getR resolve fd "FontDescriptor" with
  | some (.dict desc) =>
    match Dict.get? desc (nm "FontFile2") with
    | some o =>
      match fetchStream src s o with
      | (some (_, bytes), s') => ((Font.TrueType.parse limits bytes).toOption, s')
      | (none, s') => (none, s')
    | none => (none, s)
  | _ => (none, s)

/-- The `/CIDToGIDMap` of a `/CIDFontType2` font (§9.7.4.2). -/
inductive CIDToGID where
  /-- `/Identity` (also the default when the entry is absent or not understood): GID = CID. -/
  | identity
  /-- A stream of big-endian 2-byte GIDs indexed by CID (its decoded bytes; the decode is
  bounded by `Limits.maxDecodedStreamBytes` and charged to the document budget). -/
  | table (b : ByteArray)

/-- The glyph of a CID: GID = CID for `/Identity`; the 2-byte entry `cid` of the map stream,
`none` past its end. -/
def CIDToGID.gid : CIDToGID → Nat → Option Nat
  | .identity, cid => some cid
  | .table b, cid =>
    match b[2 * cid]?, b[2 * cid + 1]? with
    | some h, some l => some (h.toNat * 256 + l.toNat)
    | _, _ => none

/-- A stream-map GID is a 2-byte value. -/
theorem CIDToGID.gid_table_lt {b : ByteArray} {cid g : Nat}
    (h : (CIDToGID.table b).gid cid = some g) : g < 65536 := by
  simp only [CIDToGID.gid] at h
  split at h
  · rename_i hb lb _ _
    cases h
    have := hb.toNat_lt
    have := lb.toNat_lt
    omega
  · cases h

/-- Read the `/CIDToGIDMap` of a CIDFont dictionary: a stream is fetched and decoded, any
other value (the name `/Identity`, absent, malformed) is the identity. -/
def loadCIDToGID {σ : Type} (src : Source σ) (s : σ) (desc : Dict) : CIDToGID × σ :=
  match Dict.get? desc (nm "CIDToGIDMap") with
  | some (.ref n g) =>
    match fetchStream src s (.ref n g) with
    | (some (_, b), s') => (.table b, s')
    | (none, s') => (.identity, s')
  | _ => (.identity, s)

/-- The text-space advance of a CID from an embedded TrueType program: CID → GID through the
`/CIDToGIDMap`, then the `hmtx` advance of that glyph scaled by `unitsPerEm`. -/
def ttCIDAdvance (f : Font.TrueType.TTFont) (m : CIDToGID) (cid : Nat) : Option Fixed :=
  (m.gid cid).bind f.advanceOfGlyphText

/-- Whether a simple font is symbolic: bit 3 (value 4) of the font descriptor's `/Flags`
(§9.8.2), which selects the cmap rules of §9.6.6.4. -/
def isSymbolic (resolve : PdfObject → PdfObject) (fontDict : Dict) : Bool :=
  match (Font.fontDescriptor? resolve fontDict).bind (Font.getInt? resolve · "Flags") with
  | some f => f.toNat / 4 % 2 == 1
  | none => false

/-- The width table (256 codes) of a simple `/TrueType` font with an embedded program: the 6.4
metrics where `/Widths` (or, when the font has `/Widths`, `/MissingWidth`) give the width, else
the program's advance of the code's glyph (`TTFont.advanceText`, §9.6.6.4 cmap rules with the
font's encoding), else the 6.4 value. Without `/Widths` the program wins over the standard 14
metrics and `/MissingWidth`. Computed once per font. -/
def ttWidthTable (sm : SimpleMetrics) (hasWidths symbolic : Bool) (f : Font.TrueType.TTFont) :
    Array Fixed :=
  Array.ofFn (n := 256) fun i =>
    let prog := f.advanceText i.val.toUInt8 symbolic sm.encoding
    match sm.width i.val with
    | (w, .widths) => w
    | (w, .missingWidth) => if hasWidths then w else prog.getD w
    | (w, _) => prog.getD w

/-- The built-in encoding of a name-keyed CFF program: code ↦ the glyph name its CFF encoding
selects (`CFFFont.glyphNameOfCode`). -/
def cffEncoding (f : Font.CFF.CFFFont) : Encoding :=
  Array.ofFn (n := 256) fun i => f.glyphNameOfCode i.val.toUInt8

/-- The text-space advance of a one-byte code from an embedded CFF program: the glyph the
font's encoding names (looked up by name in the CFF charset), else the glyph the code selects
through the CFF's own encoding. -/
def cffCodeAdvance (f : Font.CFF.CFFFont) (enc : Encoding) (code : Nat) : Option Fixed :=
  match (enc.glyph code).bind f.gidOfName? |>.bind f.advanceOfGid with
  | some w => some w
  | none => f.advance code.toUInt8

/-- The width table (256 codes) of a simple font with an embedded CFF program: the 6.4
metrics, except where they know nothing (`unknown`, or `/MissingWidth` of a font without
`/Widths`), which take `cffCodeAdvance`. Computed once per font. -/
def cffWidthTable (sm : SimpleMetrics) (hasWidths : Bool) (f : Font.CFF.CFFFont) : Array Fixed :=
  Array.ofFn (n := 256) fun i =>
    match sm.width i.val with
    | (w, .unknown) => (cffCodeAdvance f sm.encoding i.val).getD w
    | (w, .missingWidth) =>
      if hasWidths then w else (cffCodeAdvance f sm.encoding i.val).getD w
    | (w, _) => w

/-- The width of a CID of a Type0 font: its `/W` entry, else `/DW` when the CIDFont has one,
else the embedded program's advance of that CID (`prog`: CFF `advanceOfCID`, or TrueType
`ttCIDAdvance`), else the default 1000. -/
def cidWidth (cm : CIDMetrics) (hasDW : Bool) (prog : Nat → Option Fixed) (cid : Nat) :
    Fixed :=
  match cm.table[cid]? with
  | some (some w) => w
  | _ =>
    if hasDW then cm.dw
    else match prog cid with
      | some w => w
      | none => cm.dw

/-- The width of a one-byte code of a simple font: the 6.4 metrics, else the embedded Type 1
program's advance of the encoded glyph. -/
def simpleWidth (sm : SimpleMetrics) (t1 : Option Font.Type1.Font1) (code : Nat) : Fixed :=
  match sm.width code with
  | (w, .unknown) =>
    match t1, sm.encoding.glyph code with
    | some f, some g =>
      match f.glyph? g with
      | some gl => Font.Type1.textAdvance f.matrixA f.matrixC gl.wx gl.wy
      | none => w
    | _, _ => w
  | (w, _) => w

/-- Whether a ToUnicode result has a printable character (a mapping to control characters
only, e.g. `<63> <000d>`, is a producer error and falls through). -/
def printable (s : String) : Bool := s.toList.any fun (c : Char) => 32 ≤ c.toNat

/-- The Unicode of a one-byte code of a simple font (§9.10.2 fallback chain). `dingbats`
enables the ZapfDingbats `aNN` glyph names (task 6.4b), which other fonts reuse for unrelated
glyphs. Only in a Type 3 font (`type3`) does a code in `32..126` read as that ASCII character
when the encoding names no glyph for it or one the glyph list does not know (dvips bitmap fonts
name glyphs arbitrarily). In other fonts such a code is unmapped (U+FFFD), as in MuPDF: the
names of TeX math and extension fonts (`parenleftbig`, `suppress`, …) say nothing about the
ASCII character at their code, and a code the font's encoding leaves out shows `.notdef`
(task 6.7b). -/
def simpleUnicode (dingbats type3 : Bool) (tu : Option Font.CMap.CMap) (enc : Encoding)
    (c : List UInt8) : Option String :=
  match c with
  | [b] =>
    match (tu.bind (·.lookup c)).filter printable with
    | some u => some u
    | none =>
      let ascii := if type3 ∧ 32 ≤ b.toNat ∧ b.toNat ≤ 126 then
          some (String.ofList [Char.ofNat b.toNat])
        else none
      match enc.glyph b.toNat with
      | some g =>
        match Font.glyphToUnicodeIn dingbats g with
        | some u => some u
        | none => ascii
      | none => ascii
  | _ => tu.bind (·.lookup c)

/-- Whether a simple font's `/ToUnicode` CMap maps, to printable text, every code of
`/FirstChar` + `/Widths` whose width is not zero (codes past 255 are ignored). When it does not
(a partial CMap, e.g. pdfTeX's for CMEX glyphs without a Unicode name), the embedded program's
built-in encoding is still needed for the codes it leaves out (task 6.7b). -/
def toUnicodeCovers (resolve : PdfObject → PdfObject) (fd : Dict) (tu : Font.CMap.CMap) : Bool :=
  let first : Nat := match getR resolve fd "FirstChar" with
    | some (.int i) => i.toNat
    | _ => 0
  let ws : List PdfObject := match getR resolve fd "Widths" with
    | some (.array ws) => ws
    | _ => []
  (List.range ws.length).all fun k =>
    let code := first + k
    let zero := match ws[k]?.bind (fun w => Interp.num? (resolve w)) with
      | some w => w.raw == 0
      | none => true
    zero || 255 < code || ((tu.lookup [code.toUInt8]).filter printable).isSome

/-- The em size of a Type 3 font relative to text space, estimated as twice the mean non-zero
`/Widths` entry (scaled by `FontMatrix a`): a Type 3 glyph space has no em (bitmap fonts of
dvips use `/FontMatrix [1 0 0 -1 0 0]` with pixel widths). Falls back to the matrix scale. -/
def type3SizeScale (sm : SimpleMetrics) (scale : Fixed) : Fixed :=
  let ws := sm.table.toList.filterMap fun (w, src) =>
    match src with
    | .widths => if w.raw ≠ 0 then some (fabs w).raw else none
    | _ => none
  match ws with
  | [] => fabs scale
  | _ => fabs (Fixed.mul (Fixed.clamp (2 * ws.foldl (· + ·) 0 / ws.length)) scale)

/-- MuPDF's Type 3 advance (task 7.3l): `pdf_load_type3_font` stores `/Widths` × `FontMatrix.a`
× 1000 in its integer metrics table (`pdf_add_hmtx`), so an advance (in em, `Fixed`) is
truncated toward zero to a multiple of `1/1000`. -/
def type3TruncWidth (w : Fixed) : Fixed := Fixed.clamp (Int.tdiv w.raw 1000 * 1000)

/-- Whether a string contains `pat`. -/
def hasInfix (s pat : String) : Bool := (s.splitOn pat).length > 1

/-- Build the `FontInfo` of a font dictionary (`resolve` reads objects in state `s0`). -/
def buildFontDict {σ : Type} (limits : Limits) (src : Source σ) (s0 : σ)
    (resolve : PdfObject → PdfObject) (fd : Dict) : FontInfo × σ :=
  let subtype := (nameStr? (getR resolve fd "Subtype")).getD ""
  let base := (nameStr? (getR resolve fd "BaseFont")).getD "?"
  let (tu, s1) := cmapOf src s0 fd "ToUnicode"
  let tuDesc := if tu.isSome then " ToUnicode" else ""
  if subtype == "Type0" then
    let encName := (nameStr? (getR resolve fd "Encoding")).getD ""
    let desc : Dict :=
      match getR resolve fd "DescendantFonts" with
      | some (.array (d :: _)) =>
        match resolve d with
        | .dict dd => dd
        | _ => []
      | _ => []
    let cm := CIDMetrics.ofCIDFont resolve desc
    let hasDW := (getR resolve desc "DW").isSome
    -- the CFF program is read only when some width could need it (no `/DW`)
    let needCFF := !hasDW && nameStr? (getR resolve desc "Subtype") == some "CIDFontType0"
    let (cff, s1) := if needCFF then
        loadCFF limits src s1 resolve desc ["CIDFontType0C", "Type1C"]
      else (none, s1)
    let needTT := !hasDW && nameStr? (getR resolve desc "Subtype") == some "CIDFontType2"
    let (tt, s1) := if needTT then loadTT limits src s1 resolve desc else (none, s1)
    let (c2g, s1) := if tt.isSome then loadCIDToGID src s1 desc else (.identity, s1)
    let prog : Nat → Option Fixed := match cff, tt with
      | some f, _ => f.advanceOfCID
      | none, some f => ttCIDAdvance f c2g
      | none, none => fun _ => none
    let cffDesc := if cff.isSome then " FontFile3" else if tt.isSome then " FontFile2" else ""
    match Font.identityEncoding? resolve fd with
    | some _ =>
      (⟨.two, (fun c => match c with
          | [h, l] => cidWidth cm hasDW prog (h.toNat * 256 + l.toNat)
          | _ => Fixed.zero),
        (fun c => tu.bind (·.lookup c)), s!"Type0 {base} {encName}{tuDesc}{cffDesc}", Fixed.one⟩,
        s1)
    | none =>
      let (enc, s2) := cmapOf src s1 fd "Encoding"
      let split : SplitKind :=
        match enc, tu with
        | some e, _ => if e.codespace.isEmpty then .two else .cmap e
        | none, some t => if t.codespace.isEmpty then .two else .cmap t
        | none, none => .two
      let ucs := hasInfix encName "UCS2" || hasInfix encName "UTF16"
      (⟨split, (fun c => cidWidth cm hasDW prog (Font.CMap.beValue c)),
        (fun c => match tu.bind (·.lookup c) with
          | some u => some u
          | none => if ucs then some (Font.CMap.ofUtf16 c) else none),
        s!"Type0 {base} {encName} (CID = code){tuDesc}{cffDesc}", Fixed.one⟩, s2)
  else if subtype == "Type3" then
    let sm := SimpleMetrics.ofDict resolve fd none
    let a : Fixed :=
      match getR resolve fd "FontMatrix" with
      | some (.array (x :: _)) => (Interp.num? (resolve x)).getD (Fixed.div Fixed.one (Fixed.ofInt 1000))
      | _ => Fixed.div Fixed.one (Fixed.ofInt 1000)
    let scale := Fixed.mul a (Fixed.ofInt 1000)
    (⟨.one, (fun c => match c with
        | [b] => type3TruncWidth (Fixed.mul (sm.width b.toNat).1 scale)
        | _ => Fixed.zero),
      simpleUnicode (sm.std14 == some .zapfDingbats) true tu sm.encoding, s!"Type3{tuDesc}", type3SizeScale sm scale⟩, s1)
  else
    let hasWidths := match getR resolve fd "Widths" with
      | some (.array _) => true
      | _ => false
    let encIsName := match getR resolve fd "Encoding" with
      | some (.name _) => true
      | _ => false
    -- the program is read for its widths, or for its built-in encoding when no named
    -- `/Encoding` replaces it and the ToUnicode CMap (if any) leaves codes unmapped
    let tuCovers := match tu with
      | some t => toUnicodeCovers resolve fd t
      | none => false
    let needT1 := (subtype == "Type1" || subtype == "MMType1") &&
      (!hasWidths || (!tuCovers && !encIsName))
    let (t1, s2) := if needT1 then loadType1 limits src s1 resolve fd else (none, s1)
    -- no Type 1 program: an embedded CFF (`/FontFile3 /Subtype /Type1C`) plays its role
    let (cff, s3) := if needT1 && t1.isNone then loadCFF limits src s2 resolve fd ["Type1C"]
      else (none, s2)
    let builtin : Option Encoding := match t1, cff with
      | some f, _ => some f.encoding
      | none, some f => some (cffEncoding f)
      | none, none => none
    let sm := SimpleMetrics.ofDict resolve fd builtin
    -- a TrueType program is read when some width is not given by `/Widths`/`/MissingWidth`
    let needTT := subtype == "TrueType" &&
      (!hasWidths || sm.table.any fun e => e.2 == .unknown)
    let (tt, s4) := if needTT then loadTT limits src s3 resolve fd else (none, s3)
    let progDesc := if t1.isSome then " FontFile" else if cff.isSome then " FontFile3"
      else if tt.isSome then " FontFile2" else ""
    let width : Nat → Fixed := match cff, tt with
      | some f, _ =>
        let tbl := cffWidthTable sm hasWidths f
        fun code => tbl.getD code Fixed.zero
      | none, some f =>
        let tbl := ttWidthTable sm hasWidths (isSymbolic resolve fd) f
        fun code => tbl.getD code Fixed.zero
      | none, none => simpleWidth sm t1
    (⟨.one, (fun c => match c with
        | [b] => width b.toNat
        | _ => Fixed.zero),
      simpleUnicode (sm.std14 == some .zapfDingbats) false tu sm.encoding,
      s!"{subtype} {base}{tuDesc}{progDesc}", Fixed.one⟩, s4)

/-- Build the `FontInfo` of a font object; an object that is not a dictionary gets the
substitute `FontInfo.unknown` (as MuPDF's `pdf_load_hail_mary_font`). -/
def buildFont {σ : Type} (limits : Limits) (src : Source σ) (s0 : σ) (fontObj : PdfObject) :
    FontInfo × σ :=
  let resolve := fun o => (Run.resolve src s0 o).1
  match resolve fontObj with
  | .dict fd => buildFontDict limits src s0 resolve fd
  | _ => (FontInfo.unknown, s0)

/-- Maximum number of font objects loaded per page. -/
def maxFonts : Nat := 1024

/-- Maximum number of resource dictionaries (page and forms) whose fonts are collected per
page, and of XObjects inspected per dictionary. -/
def maxFormFonts : Nat := 64

/-- A font found in resources: its key, every key it is known under, the font object. -/
abbrev FontEntry := FontKey × List FontKey × PdfObject

/-- The `/Font` entries of a resource dictionary. -/
def fontEntries {σ : Type} (src : Source σ) (s : σ) (res : Dict) : Dict × σ :=
  match Dict.get? res (nm "Font") with
  | some o => Run.dictOf src s o
  | none => ([], s)

/-- The fonts of the resources `res` of `owner`: its `/Font` entries (a reference is keyed by
its object and also listed under its name) and the `/Font [ref size]` entries of its
ExtGState dictionaries. -/
def resFonts {σ : Type} (src : Source σ) (s : σ) (owner : Nat) (res : Dict) :
    List FontEntry × σ :=
  let (fs, s) := fontEntries src s res
  let named : List FontEntry := fs.map fun (n, o) =>
    match o with
    | .ref num g => (.obj num g, [.obj num g, .res owner n], o)
    | _ => (.res owner n, [.res owner n], o)
  let (gss, s) := match Dict.get? res (nm "ExtGState") with
    | some o => Run.dictOf src s o
    | none => ([], s)
  let (gsFonts, s) := gss.foldl (fun (acc : List FontEntry × σ) (_, o) =>
    let (d, s) := Run.dictOf src acc.2 o
    match Dict.get? d (nm "Font") with
    | some f =>
      match Run.resolve src s f with
      | (.array (.ref num g :: _), s) => (acc.1 ++ [(.obj num g, [.obj num g], .ref num g)], s)
      | (_, s) => (acc.1, s)
    | none => (acc.1, s)) ([], s)
  (named ++ gsFonts, s)

/-- The form XObjects of `res` that have their own `/Resources` (as `Run.formResources`
decides): object number and resources. At most `maxFormFonts` XObjects are inspected. -/
def formChildren {σ : Type} (src : Source σ) (s : σ) (res : Dict) : List (Nat × Dict) × σ :=
  match Dict.get? res (nm "XObject") with
  | none => ([], s)
  | some o =>
    let (xs, s) := Run.dictOf src s o
    (xs.take maxFormFonts).foldl (fun (acc : List (Nat × Dict) × σ) (_, x) =>
      match x with
      | .ref n g =>
        match src.fetch acc.2 n g with
        | (.ok (.stream st), s1) =>
          if Dict.get? st.dict (nm "Subtype") == some (.name (nm "Form")) then
            match Run.formResources src s1 st.dict [] 0 n with
            | ((rd, ow), s2) => if ow = n ∧ n ≠ 0 then (acc.1 ++ [(n, rd)], s2) else (acc.1, s2)
          else (acc.1, s1)
        | (_, s1) => (acc.1, s1)
      | _ => acc) ([], s)

/-- Collect fonts breadth-first over a worklist of resource dictionaries (owner, resources),
each form at most once (`seen`); `fuel` bounds the dictionaries scanned. -/
def scanFonts {σ : Type} (src : Source σ) :
    Nat → List (Nat × Dict) → List Nat → List FontEntry → σ → List FontEntry × σ
  | 0, _, _, acc, s => (acc, s)
  | _, [], _, acc, s => (acc, s)
  | f + 1, (owner, res) :: rest, seen, acc, s =>
    let (es, s) := resFonts src s owner res
    let (kids, s) := formChildren src s res
    let (new, seen) := kids.foldl (fun (acc : List (Nat × Dict) × List Nat) (n, d) =>
      if acc.2.contains n then acc else (acc.1 ++ [(n, d)], n :: acc.2)) ([], seen)
    scanFonts src f (rest ++ new) seen (acc ++ es) s

/-- **Font table of a page**: every font collected by `scanFonts` from the page's resources
(owner 0), each font object built once (`buildFont`); at most `maxFonts` objects. -/
def loadFonts {σ : Type} (limits : Limits) (src : Source σ) (s : σ) (res : Dict) :
    FontTable × σ :=
  let (es, s) := scanFonts src (maxFormFonts + 1) [(0, res)] [] [] s
  let (t, _, s) := es.foldl (fun (acc : FontTable × Nat × σ) (e : FontEntry) =>
    let (t, k, s) := acc
    let (key, keys, o) := e
    let add (fi : FontInfo) : FontTable :=
      t ++ (keys.filter fun k' => (t.lookup k').isNone).map fun k' => (k', fi)
    match t.lookup key with
    | some fi => (add fi, k, s)
    | none =>
      if maxFonts ≤ k then acc
      else
        let (fi, s') := buildFont limits src s o
        (add fi, k + 1, s')) (([] : FontTable), 0, s)
  (t, s)

/-! ## Glyphs -/

/-- One extracted glyph. -/
structure Glyph where
  /-- Unicode text (normalised; U+FFFD when unmapped). -/
  text : String
  /-- The character code bytes shown. -/
  code : List UInt8
  /-- Index of the `glyphRun` item in the display list. -/
  item : Nat
  /-- Index of the glyph within its run. -/
  seq : Nat
  /-- Origin, page space. -/
  x : Fixed
  /-- Origin (baseline), page space. -/
  y : Fixed
  /-- Page-space extent of the advance along the baseline direction (the glyph box width). -/
  width : Fixed
  /-- Baseline direction in quarter turns: 0 left-to-right, 1 upwards, 2 right-to-left
  (upside down), 3 downwards. -/
  dir : Nat
  /-- Page-space font size. -/
  fontSize : Fixed
  /-- Whether the run's render mode paints (not `Tr 3`/`Tr 7`). -/
  visible : Bool
  /-- Page-space length, along the exact baseline direction (`dirX`, `dirY`), of the glyph's
  own advance `w0 · Tfs · Th` — without character and word spacing (`Tc`, `Tw`): the pen
  position after the glyph that MuPDF measures word gaps from (task 6.8e). Defaults to
  `width`. -/
  adv : Fixed := width
  /-- The exact baseline direction in page space, a unit vector (x component; `Fixed` rounding):
  the normalised image of the text x axis under `Tm × CTM` (task 6.8e). Defaults to the
  quarter turn `dir`. Layout measures lines in this frame (`Glyph.frame`), so text rotated
  by other angles than quarter turns (45° chart labels) groups and orders like upright text. -/
  dirX : Fixed := match dir with | 1 | 3 => Fixed.zero | 2 => Fixed.neg Fixed.one | _ => Fixed.one
  /-- The exact baseline direction, y component (see `dirX`). -/
  dirY : Fixed := match dir with | 1 => Fixed.one | 3 => Fixed.neg Fixed.one | _ => Fixed.zero
  deriving Repr, Inhabited, DecidableEq

/-- The text state a run was shown with. -/
def runTextState (r : GlyphRun) : TextState :=
  { charSpacing := r.charSpacing, wordSpacing := r.wordSpacing,
    horizScaling := r.horizScaling, font := some r.font, renderMode := r.renderMode,
    rise := r.rise }

/-- Each code with its text-space offset and advance. -/
def offsets (fi : FontInfo) (ts : TextState) (size : Fixed) :
    Fixed → List (List UInt8) → List (List UInt8 × Fixed × Fixed)
  | _, [] => []
  | tx, c :: cs =>
    let a := codeAdvance fi ts size c
    (c, tx, a) :: offsets fi ts size (Fixed.add tx a) cs

/-- `offsets` keeps the codes, in order. -/
theorem offsets_codes (fi : FontInfo) (ts : TextState) (size : Fixed) :
    ∀ (tx : Fixed) (cs : List (List UInt8)), (offsets fi ts size tx cs).map (·.1) = cs
  | _, [] => rfl
  | tx, c :: cs => by simp [offsets, offsets_codes fi ts size _ cs]

/-- The bytes shown by the strings of a run, string by string. -/
def strParts : List TextPart → List (List UInt8)
  | [] => []
  | .str bs :: rest => bs :: strParts rest
  | .adjust _ :: rest => strParts rest

/-- Lay out the parts of a run: every code with its offset and advance. -/
def layoutParts (fi : FontInfo) (ts : TextState) (size : Fixed) :
    Fixed → List TextPart → List (List UInt8 × Fixed × Fixed)
  | _, [] => []
  | tx, .str bs :: rest =>
    let cs := fi.split.codes bs
    offsets fi ts size tx cs ++ layoutParts fi ts size (endTx fi ts size tx cs) rest
  | tx, .adjust a :: rest => layoutParts fi ts size (Fixed.add tx (Interp.adjustTx ts size a)) rest

/-- The laid-out codes of a run are the split codes of its strings, in order. -/
theorem layoutParts_codes (fi : FontInfo) (ts : TextState) (size : Fixed) :
    ∀ (tx : Fixed) (ps : List TextPart),
      (layoutParts fi ts size tx ps).map (·.1) = (strParts ps).flatMap fi.split.codes
  | _, [] => rfl
  | tx, .str bs :: rest => by
    simp [layoutParts, strParts, offsets_codes, layoutParts_codes fi ts size _ rest]
  | tx, .adjust a :: rest => by
    simp [layoutParts, strParts, layoutParts_codes fi ts size _ rest]

/-- Unicode text of a code (normalised, U+FFFD when unmapped). -/
def textOf (fi : FontInfo) (c : List UInt8) : String :=
  normalize ((fi.unicode c).getD replacementStr)

/-- The baseline direction of a text-to-page matrix (the image of the x axis), in quarter
turns. -/
def dirOf (m : Matrix) : Nat :=
  if (fabs m.b).raw ≤ (fabs m.a).raw then (if m.a.raw < 0 then 2 else 0)
  else if 0 < m.b.raw then 1 else 3

/-- Coordinates rotated into a direction's frame: along the baseline, and across it (up). -/
def rotFrame (dir : Nat) (x y : Fixed) : Fixed × Fixed :=
  match dir with
  | 1 => (y, Fixed.neg x)
  | 2 => (Fixed.neg x, Fixed.neg y)
  | 3 => (Fixed.neg y, x)
  | _ => (x, y)

/-- The unit vector of the baseline direction `(m.a, m.b)` of a text-to-page matrix, in
`Fixed` (normalised with the integer square root of the raw values, so an axis-aligned
direction gives exactly `(±1, 0)` or `(0, ±1)`); the quarter turn `dir` for a degenerate
matrix. -/
def unitDir (m : Matrix) (dir : Nat) : Fixed × Fixed :=
  let n := Nat.sqrt (m.a.raw.natAbs * m.a.raw.natAbs + m.b.raw.natAbs * m.b.raw.natAbs)
  if n = 0 then
    match dir with
    | 1 => (Fixed.zero, Fixed.one)
    | 2 => (Fixed.neg Fixed.one, Fixed.zero)
    | 3 => (Fixed.zero, Fixed.neg Fixed.one)
    | _ => (Fixed.one, Fixed.zero)
  else
    (Fixed.clamp (m.a.raw * fixedScale / (n : Int)), Fixed.clamp (m.b.raw * fixedScale / (n : Int)))

/-- The glyph's own advance in text space, `w0 · Tfs · Th` (no `Tc`, `Tw`): what MuPDF's text
device advances its pen by (`fz_add_stext_char`'s `adv`), computed from the code's full
displacement `a = (w0 · Tfs + Tc + Tw) · Th` (`codeAdvance`) by taking the spacing back out, so
the font's width function is not evaluated a second time. -/
def fontAdvance (r : GlyphRun) (c : List UInt8) (a : Fixed) : Fixed :=
  let th := Fixed.div r.horizScaling (Fixed.ofInt 100)
  let tw := if isSpaceCode c then r.wordSpacing else Fixed.zero
  Fixed.sub a (Fixed.mul (Fixed.add r.charSpacing tw) th)

/-- The **expansion** of the text rendering matrix per unit of font size: `√|det|` of
`diag(Th, 1) × m` (MuPDF's `fz_matrix_expansion` of its `trm`, task 6.8e): the size of an em of a
glyph whose text space is scaled non-uniformly or by `Tz`, the size MuPDF measures word gaps and
baseline offsets in. Computed with the integer square root of the raw determinant. -/
def expansion (m : Matrix) (horizScaling : Fixed) : Fixed :=
  let th := Fixed.div horizScaling (Fixed.ofInt 100)
  let det := (Fixed.mul m.a th).raw * m.d.raw - (Fixed.mul m.b th).raw * m.c.raw
  Fixed.clamp (Nat.sqrt det.natAbs : Int)

/-- A positioned glyph from a laid-out code (provenance fields set by `runGlyphs`). -/
def mkGlyph (fi : FontInfo) (r : GlyphRun) (e : List UInt8 × Fixed × Fixed) : Glyph :=
  let m := Matrix.mul r.tm r.ctm
  let p0 := Matrix.apply m ⟨e.2.1, r.rise⟩
  let p1 := Matrix.apply m ⟨Fixed.add e.2.1 e.2.2, r.rise⟩
  let p2 := Matrix.apply m ⟨Fixed.add e.2.1 (fontAdvance r e.1 e.2.2), r.rise⟩
  let d := dirOf m
  let (ux, uy) := unitDir m d
  { text := textOf fi e.1, code := e.1, item := 0, seq := 0, x := p0.x, y := p0.y,
    width := Fixed.sub (rotFrame d p1.x p1.y).1 (rotFrame d p0.x p0.y).1, dir := d,
    fontSize := Fixed.mul (Fixed.mul (fabs r.font.size) fi.sizeScale) (expansion m r.horizScaling),
    visible := r.renderMode.paints,
    adv := Fixed.add (Fixed.mul (Fixed.sub p2.x p0.x) ux) (Fixed.mul (Fixed.sub p2.y p0.y) uy),
    dirX := ux, dirY := uy }

/-- The glyphs of the run at display-list index `i`, in show order. -/
def runGlyphs (fonts : FontTable) (i : Nat) (r : GlyphRun) : List Glyph :=
  let fi := fonts.get r.font
  (layoutParts fi (runTextState r) r.font.size Fixed.zero r.parts).mapIdx fun j e =>
    { mkGlyph fi r e with item := i, seq := j }

/-- The glyphs of one display item. -/
def itemGlyphs (fonts : FontTable) (i : Nat) : DisplayItem → List Glyph
  | .glyphRun r _ => runGlyphs fonts i r
  | _ => []

/-- The glyphs of a display list from index `i` on. -/
def extractAux (fonts : FontTable) : Nat → List DisplayItem → List Glyph
  | _, [] => []
  | i, it :: rest => itemGlyphs fonts i it ++ extractAux fonts (i + 1) rest

/-- **Extraction**: the glyphs of a display list, in content order. Reads `glyphRun` items
only. -/
def extractItems (fonts : FontTable) (items : List DisplayItem) : List Glyph :=
  extractAux fonts 0 items

/-! ### C3 / C6 -/

/-- A glyph of `runGlyphs` sits at its own `seq` and carries the run's index. -/
theorem runGlyphs_self {fonts : FontTable} {i : Nat} {r : GlyphRun} {g : Glyph}
    (h : g ∈ runGlyphs fonts i r) : g.item = i ∧ (runGlyphs fonts i r)[g.seq]? = some g := by
  simp only [runGlyphs] at h ⊢
  obtain ⟨j, hj, rfl⟩ := List.mem_mapIdx.mp h
  exact ⟨rfl, by rw [List.getElem?_mapIdx, List.getElem?_eq_getElem hj]; rfl⟩

/-- A glyph of `extractAux` comes from a `glyphRun` item at its offset `j`. -/
theorem extractAux_mem (fonts : FontTable) :
    ∀ (i : Nat) (items : List DisplayItem) (g : Glyph), g ∈ extractAux fonts i items →
      ∃ j r clip, items[j]? = some (.glyphRun r clip) ∧ g ∈ runGlyphs fonts (i + j) r
  | _, [], g, h => by simp [extractAux] at h
  | i, it :: rest, g, h => by
    simp only [extractAux, List.mem_append] at h
    rcases h with h | h
    · cases it with
      | glyphRun r clip => exact ⟨0, r, clip, rfl, by simpa [itemGlyphs] using h⟩
      | _ => simp [itemGlyphs] at h
    · obtain ⟨j, r, clip, hj, hg⟩ := extractAux_mem fonts (i + 1) rest g h
      exact ⟨j + 1, r, clip, by simpa using hj, by rw [show i + (j + 1) = i + 1 + j by omega]; exact hg⟩

/-- **C6 and C3 (provenance round trip).** Every extracted glyph comes from a `glyphRun` item
of the display list, at index `g.item`, and recomputing that item's glyphs from the display
list alone gives back exactly `g` at position `g.seq` (same text, code bytes, origin, width,
size, visibility). -/
theorem extract_from_items (fonts : FontTable) (items : List DisplayItem) (g : Glyph)
    (h : g ∈ extractItems fonts items) :
    ∃ r clip, items[g.item]? = some (.glyphRun r clip) ∧
      (runGlyphs fonts g.item r)[g.seq]? = some g := by
  obtain ⟨j, r, clip, hj, hg⟩ := extractAux_mem fonts 0 items g h
  simp only [Nat.zero_add] at hg
  obtain ⟨hi, hs⟩ := runGlyphs_self hg
  exact ⟨r, clip, by rw [hi]; exact hj, by rw [hi]; exact hs⟩

/-- **C3 (bytes)**: the code bytes of a run's glyphs, concatenated, are exactly the bytes its
strings showed, in order. -/
theorem runGlyphs_codes (fonts : FontTable) (i : Nat) (r : GlyphRun) :
    ((runGlyphs fonts i r).map Glyph.code).flatten = (strParts r.parts).flatten := by
  have h1 : (runGlyphs fonts i r).map Glyph.code =
      (layoutParts (fonts.get r.font) (runTextState r) r.font.size Fixed.zero r.parts).map (·.1) := by
    apply List.ext_getElem?
    intro k
    simp [runGlyphs, List.getElem?_mapIdx, mkGlyph]
    cases (layoutParts (fonts.get r.font) (runTextState r) r.font.size Fixed.zero r.parts)[k]? <;>
      rfl
  rw [h1, layoutParts_codes]
  generalize strParts r.parts = l
  induction l with
  | nil => rfl
  | cons x xs ih => simp [List.flatMap_cons, List.flatten_append, SplitKind.codes_flatten, ih]

/-! ## Reading order (heuristic; tested) -/

/-- Layout parameters (per mille of the font size). -/
structure Options where
  /-- Keep glyphs of invisible runs (`Tr 3`, `Tr 7`), e.g. OCR text layers. -/
  includeInvisible : Bool := true
  /-- Baseline tolerance for one line. -/
  lineTol : Nat := 500
  /-- Minimum gap that becomes a space (MuPDF's `SPACE_DIST`, 0.15 em). -/
  wordGap : Nat := 150
  /-- Baseline distance above which a blank line separates lines. -/
  paraGap : Nat := 2000
  /-- Largest raise of a smaller-font run (superscript) above the line's baseline, ‰ of the
  line's (larger) font size, for it to stay on the line (`scriptJoin`). -/
  scriptRaise : Nat := 600
  /-- How far a script run may start before the end of the line (‰ of the larger size):
  stacked sub/superscripts, italic corrections. -/
  scriptBack : Nat := 500
  /-- How far after the end of the line a script run may start (‰ of the larger size). -/
  scriptAhead : Nat := 1000
  /-- How far past the previous glyph's advance end a backward-moving glyph may start and still
  keep content order (`attached`); MuPDF's `SPACE_MAX_DIST` (0.8 em). -/
  attachBack : Nat := 800
  /-- Largest baseline offset from the previous glyph (‰ of the size of the glyph added) for
  a glyph that continues it (`nearPrev`); MuPDF's `BASE_MAX_DIST` (0.8 em, task 6.8e). -/
  baseMax : Nat := 800
  /-- Largest distance along the baseline between the previous glyph's pen and the origin of a
  glyph that continues it (`nearPrev`, ‰ of the size of the glyph added); MuPDF's
  `SPACE_MAX_DIST` (0.8 em, task 6.8e). -/
  spaceMax : Nat := 800
  /-- The visible page area in default user space, `(llx, lly, urx, ury)`: glyphs lying
  entirely outside it are left out of the lines and the text (`Glyph.offPage`; MuPDF's
  `FZ_STEXT_CLIP`, which `mutool draw` sets). `none`: no clipping. `extractDocPage` fills it
  with the page's CropBox (`Options.forPage`). -/
  pageBox : Option (Fixed × Fixed × Fixed × Fixed) := none

/-- Position along the baseline direction. -/
def Glyph.u (g : Glyph) : Fixed := (rotFrame g.dir g.x g.y).1

/-- Position across the baseline direction. -/
def Glyph.v (g : Glyph) : Fixed := (rotFrame g.dir g.x g.y).2

/-- Minimum. -/
def fmin (x y : Fixed) : Fixed := if y.raw < x.raw then y else x

/-- The end of a glyph's advance along its baseline direction. -/
def Glyph.uEnd (g : Glyph) : Fixed := Fixed.add g.u g.width

/-- Coordinates of a direction's frame mapped back to page space (inverse of `rotFrame`). -/
def unFrame (dir : Nat) (u v : Fixed) : Fixed × Fixed :=
  match dir with
  | 1 => (Fixed.neg v, u)
  | 2 => (Fixed.neg u, Fixed.neg v)
  | 3 => (v, Fixed.neg u)
  | _ => (u, v)

/-- The page-space box `(x0, y0, x1, y1)` of a glyph: its advance along the baseline, and
across it from `0.2` of the size below the baseline to `0.8` above (the API's `glyphBox`; an
estimate of the ink box MuPDF takes from the outline). -/
def Glyph.bounds (g : Glyph) : Fixed × Fixed × Fixed × Fixed :=
  let s := fabs g.fontSize
  let v0 := Fixed.sub g.v (Fixed.div s (Fixed.ofInt 5))
  let v1 := Fixed.add g.v (Fixed.div (Fixed.mul s (Fixed.ofInt 4)) (Fixed.ofInt 5))
  let p := unFrame g.dir (fmin g.u g.uEnd) v0
  let q := unFrame g.dir (fmax g.u g.uEnd) v1
  (fmin p.1 q.1, fmin p.2 q.2, fmax p.1 q.1, fmax p.2 q.2)

/-- Whether a glyph lies **entirely outside** the box `(llx, lly, urx, ury)` (touching its
edge from outside counts as outside), as MuPDF's `fz_glyph_entirely_outside_box`. -/
def Glyph.offPage (b : Fixed × Fixed × Fixed × Fixed) (g : Glyph) : Bool :=
  let (x0, y0, x1, y1) := g.bounds
  x1.raw ≤ b.1.raw || y1.raw ≤ b.2.1.raw || b.2.2.1.raw ≤ x0.raw || b.2.2.2.raw ≤ y0.raw

/-- Whether layout keeps a glyph: visible (or invisible text kept) and not entirely outside
`pageBox`. -/
def Options.keeps (o : Options) (g : Glyph) : Bool :=
  (o.includeInvisible || g.visible) &&
    match o.pageBox with
    | some b => !g.offPage b
    | none => true

/-- A layout frame: the unit vector `(x, y)` of a baseline direction in page space
(`Glyph.dirX`, `Glyph.dirY`). Lines are measured in the frame of their first glyph. -/
abbrev Frame := Fixed × Fixed

/-- The frame of a glyph's own baseline. -/
def Glyph.frame (g : Glyph) : Frame := (g.dirX, g.dirY)

/-- Position of a glyph's origin along the frame's baseline direction. -/
def Frame.u (f : Frame) (g : Glyph) : Fixed := Fixed.add (Fixed.mul g.x f.1) (Fixed.mul g.y f.2)

/-- Position of a glyph's origin across the frame's baseline direction (up). -/
def Frame.v (f : Frame) (g : Glyph) : Fixed := Fixed.sub (Fixed.mul g.y f.1) (Fixed.mul g.x f.2)

/-- The pen after a glyph along the frame (origin plus the glyph's own advance `adv`). -/
def Frame.uEnd (f : Frame) (g : Glyph) : Fixed := Fixed.add (f.u g) g.adv

/-- Whether two frames are the same direction for layout: cosine of the angle between them at
least `0.999` (MuPDF starts a new line when `vec_dot(ndir, line->dir) < 0.999`). -/
def Frame.same (f h : Frame) : Bool :=
  (Fixed.add (Fixed.mul f.1 h.1) (Fixed.mul f.2 h.2)).raw * 1000 ≥ 999 * fixedScale

/-- A line: glyphs in content order, the baseline of its largest-size glyphs, its largest
size, and its extent along the baseline. Positions are taken in the line's `frame`. -/
structure Line where
  /-- Glyphs, content order. -/
  glyphs : Array Glyph
  /-- Baseline direction (of the first glyph). -/
  dir : Nat
  /-- Baseline, across the direction: of the first glyph, moved to the baseline of a glyph of
  larger size when one joins (so a line begun by a superscript marker takes the baseline of
  the body text that follows it). -/
  v : Fixed
  /-- Largest font size. -/
  size : Fixed
  /-- Smallest glyph start along the baseline. -/
  lo : Fixed
  /-- Largest glyph end along the baseline. -/
  hi : Fixed
  /-- The exact baseline direction of the line (of its first glyph; task 6.8e): `v`, `lo`,
  `hi` and the order of the glyphs are measured in it. -/
  frame : Frame := (Fixed.one, Fixed.zero)
  deriving Repr, Inhabited

/-- A line of one glyph. -/
def Line.ofGlyph (g : Glyph) : Line :=
  let f := g.frame
  { glyphs := #[g], dir := g.dir, v := f.v g, size := g.fontSize,
    lo := fmin (f.u g) (f.uEnd g), hi := fmax (f.u g) (f.uEnd g), frame := f }

/-- `x ≤ k‰ of s` on raw values. -/
def withinPermille (x s : Fixed) (k : Nat) : Bool := (fabs x).raw * 1000 ≤ (fabs s).raw * k

/-- Whether `g` starts where the line ends: no more than `scriptBack` ‰ of `size` before the
line's end and no more than `scriptAhead` ‰ after it. -/
def continuesLine (o : Options) (l : Line) (g : Glyph) (size : Fixed) : Bool :=
  let d := Fixed.sub (l.frame.u g) l.hi
  if d.raw < 0 then withinPermille d size o.scriptBack else withinPermille d size o.scriptAhead

/-- **Sub/superscripts** (heuristic): `g` joins line `l` although its baseline is further than
`lineTol` away when one side is a smaller-font script of the other and `g` continues the line
horizontally: a smaller `g` raised above the line's baseline by at most `scriptRaise` ‰ of the
line's size (footnote marker, exponent), or a larger `g` whose baseline lies below that of a
line of smaller glyphs by at most `scriptRaise` ‰ of `g`'s size (a line begun by a marker). -/
def scriptJoin (o : Options) (l : Line) (g : Glyph) : Bool :=
  let d := Fixed.sub (l.frame.v g) l.v
  if g.fontSize.raw < l.size.raw then
    0 < d.raw && withinPermille d l.size o.scriptRaise && continuesLine o l g l.size
  else if l.size.raw < g.fontSize.raw then
    d.raw < 0 && withinPermille d g.fontSize o.scriptRaise && continuesLine o l g g.fontSize
  else false

/-- Whether `g` continues the last glyph `p` of line `l` as MuPDF's text device would keep it
on `p`'s line (`fz_add_stext_char`, task 6.8e): its baseline is less than `baseMax` ‰ of `g`'s
size off `p`'s, and its origin less than `spaceMax` ‰ of `g`'s size from `p`'s pen along the
baseline (forwards or backwards). E.g. a radical sign raised 0.78 em right after a word
(`by √dk`), or an underbar 0.7 em below its letter. -/
def nearPrev (o : Options) (l : Line) (g : Glyph) : Bool :=
  match l.glyphs.back? with
  | none => false
  | some p =>
    let f := l.frame
    let dv := Fixed.sub (f.v g) (f.v p)
    let du := Fixed.sub (f.u g) (f.uEnd p)
    (fabs dv).raw * 1000 < (fabs g.fontSize).raw * o.baseMax &&
      (fabs du).raw * 1000 < (fabs g.fontSize).raw * o.spaceMax

/-- Whether `g` continues line `l`: same baseline direction (quarter turn and exact frame,
`Frame.same`), and its baseline is within `lineTol` ‰ of **its own** size of the line's (MuPDF
measures baseline offsets in units of the size of the glyph being added: a small caption below
a huge title starts a line of its own, task 6.8e), or it continues the line's last glyph
(`nearPrev`), or it is a sub/superscript of the line (`scriptJoin`). -/
def sameLine (o : Options) (l : Line) (g : Glyph) : Bool :=
  g.dir == l.dir && l.frame.same g.frame &&
    (withinPermille (Fixed.sub (l.frame.v g) l.v) g.fontSize o.lineTol ||
      nearPrev o l g || scriptJoin o l g)

/-- Add a glyph to a line; a glyph of larger size than the line's moves the baseline to its
own. -/
def Line.push (l : Line) (g : Glyph) : Line :=
  let f := l.frame
  { l with glyphs := l.glyphs.push g, size := fmax l.size g.fontSize,
           v := if l.size.raw < g.fontSize.raw then f.v g else l.v,
           lo := fmin l.lo (fmin (f.u g) (f.uEnd g)), hi := fmax l.hi (fmax (f.u g) (f.uEnd g)) }

/-- Group glyphs (content order) into lines. -/
def groupLines (o : Options) (gs : List Glyph) : Array Line :=
  let (done, cur) := gs.foldl (fun (acc : Array Line × Option Line) g =>
    match acc.2 with
    | some l =>
      if sameLine o l g then (acc.1, some (l.push g))
      else (acc.1.push l, some (Line.ofGlyph g))
    | none => (acc.1, some (Line.ofGlyph g))) (#[], none)
  match cur with
  | some l => done.push l
  | none => done

/-- Whether a space may follow text ending in `s` (MuPDF's `may_add_space`): its last
character is not a space and lies below U+0700 (Latin, Greek, Cyrillic, Hebrew, Arabic, …) or in
U+2000–U+20CF (general punctuation, super/subscripts, currency). After mathematical operators,
arrows or CJK no space is inserted (`a −b`, `≤d`, `∞∈`, as MuPDF). Empty text allows one. -/
def spaceMayFollow (s : String) : Bool :=
  match s.toList.getLast? with
  | none => true
  | some c => c != ' ' && (c.toNat < 0x700 || (0x2000 ≤ c.toNat && c.toNat ≤ 0x20CF))

/-- Whether `g`, shown right after `p`, is **attached** to it in frame `f`: it starts before
`p`'s origin (a backward move) but by less than `attachBack` ‰ of the size past `p`'s pen
(`Frame.uEnd`) — overlapping glyph boxes, such as a base letter drawn after its accent (TeX's
`\c{c}`, `\.z`). Attached glyphs keep content order (as MuPDF, which keeps such glyphs on the
line in content order). -/
def attached (o : Options) (f : Frame) (p g : Glyph) : Bool :=
  g.dir == p.dir && (f.u g).raw < (f.u p).raw &&
    withinPermille (Fixed.sub (f.u g) (f.uEnd p)) (fmax p.fontSize g.fontSize) o.attachBack

/-- Sort keys of a line's glyphs (content order) in frame `f`: a glyph's own position along the
baseline, or the key of the glyph before it when it is `attached` to it. -/
def sortKeys (o : Options) (f : Frame) (gs : List Glyph) : List (Glyph × Int) :=
  let (out, _) := gs.foldl (fun (acc : Array (Glyph × Int) × Option (Glyph × Int)) g =>
    let k := match acc.2 with
      | some (p, kp) => if attached o f p g then kp else (f.u g).raw
      | none => (f.u g).raw
    (acc.1.push (g, k), some (g, k))) (#[], none)
  out.toList

/-- The glyphs of a line in reading order: left to right by `sortKeys` (stable), so glyphs
attached to their predecessor (accents before their base letter) keep content order. -/
def lineOrder (o : Options) (l : Line) : List Glyph :=
  ((sortKeys o l.frame l.glyphs.toList).mergeSort fun a b => a.2 ≤ b.2).map (·.1)

/-- What goes before glyph `g` that follows `p` in a line of frame `f`: `none` when `g` is an
overprinted duplicate of `p` (same text from the same code bytes, origin within 10 % of the
size: fake bold), which is dropped; else `" "` at a **word gap** and `""` otherwise. A word gap
is MuPDF's (`fz_add_stext_char`, task 6.8e): the distance from `p`'s pen — its origin plus its
own advance `w0 · Tfs · Th`, **without** `Tc` and `Tw` (`Glyph.adv`) — to `g`'s origin exceeds
`wordGap` ‰ of `g`'s size (so letter-spaced text, `Tc` above 0.15 em, reads `R A I L`, and a
superscript 1.4 pt after its base letter is a word of its own: `W O`), unless
`g` starts with a space or the text of `p` ends in a character after which MuPDF never inserts
one (`spaceMayFollow`). -/
def glyphSep (o : Options) (f : Frame) (p g : Glyph) : Option String :=
  let sz := fmax p.fontSize g.fontSize
  let dup := p.text == g.text && p.code == g.code &&
    withinPermille (Fixed.sub (f.u g) (f.u p)) sz 100 &&
    withinPermille (Fixed.sub (f.v g) (f.v p)) sz 100
  if dup then none
  else
    let gap := Fixed.sub (f.u g) (f.uEnd p)
    let space := gap.raw > 0 && !withinPermille gap g.fontSize o.wordGap &&
      spaceMayFollow p.text && !g.text.startsWith " "
    some (if space then " " else "")

/-- The text of a line: glyphs in `lineOrder`, separated as `glyphSep` says (spaces at word
gaps, overprints dropped). -/
def lineText (o : Options) (l : Line) : String :=
  let sorted := lineOrder o l
  let (out, _) := sorted.foldl (fun (acc : String × Option Glyph) g =>
    match acc.2 with
    | none => (acc.1 ++ g.text, some g)
    | some p =>
      match glyphSep o l.frame p g with
      | none => acc
      | some sep => (acc.1 ++ sep ++ g.text, some g)) ("", none)
  out

/-- The separator before line `l` after line `prev`: nothing for the first line, a newline,
or a blank line when both run in the same direction and their baselines are more than
`paraGap` ‰ of the size of `l` apart (MuPDF measures in units of the glyph added, task 6.8e: a
caption 40 pt below a 100 pt title is a paragraph of its own). -/
def lineSep (o : Options) (prev : Option Line) (l : Line) : String :=
  match prev with
  | none => ""
  | some p =>
    if l.dir != p.dir || !l.frame.same p.frame ||
        withinPermille (Fixed.sub l.v p.v) l.size o.paraGap then "\n"
    else "\n\n"

/-- **Reading order**: the page text of a glyph list (see the module doc). -/
def layout (o : Options) (gs : List Glyph) : Array Line × String :=
  let lines := groupLines o (gs.filter o.keeps)
  let (text, _) := lines.foldl (fun (acc : String × Option Line) l =>
    (acc.1 ++ lineSep o acc.2 l ++ lineText o l, some l)) ("", none)
  (lines, text)

/-! ## `/ActualText` (task 6.8d; heuristic as MuPDF, tested) -/

/-- The characters of a PDF text string (ISO 32000-2 §7.9.2.2), as MuPDF's
`pdf_to_text_string`: UTF-16BE after `FE FF`, UTF-16LE after `FF FE`, UTF-8 after `EF BB BF`,
else PDFDocEncoding through the glyph list (tab, line feed and carriage return kept, other
undefined bytes U+FFFD). Decoding stops at the first NUL, as MuPDF reads the result as a C
string. -/
def actualChars (bs : List UInt8) : List Char :=
  let pdfDoc (bs : List UInt8) : List Char :=
    bs.flatMap fun (b : UInt8) =>
      if b == 9 || b == 10 || b == 13 then [Char.ofNat b.toNat]
      else match (Font.pdfDocEncoding.glyph b.toNat).bind glyphToUnicode with
        | some t => t.toList
        | none => [Font.CMap.replacement]
  let swap : List UInt8 → List UInt8 := fun bs =>
    (pairs bs).flatMap fun p => match p with
      | [a, b] => [b, a]
      | q => q
  let cs := match bs with
    | 0xFE :: 0xFF :: rest => (Font.CMap.ofUtf16 rest).toList
    | 0xFF :: 0xFE :: rest => (Font.CMap.ofUtf16 (swap rest)).toList
    | 0xEF :: 0xBB :: 0xBF :: rest =>
      match String.fromUTF8? ⟨rest.toArray⟩ with
      | some t => t.toList
      | none => pdfDoc rest
    | _ => pdfDoc bs
  cs.takeWhile (· != Char.ofNat 0)

/-- The extraction state of `/ActualText` sequences: the characters still to place of every
open sequence (innermost first), and the last glyph placed (its advance end is MuPDF's pen). -/
structure ActState where
  /-- Remaining characters of the open `/ActualText` sequences, innermost first. -/
  open_ : List (List Char) := []
  /-- The last glyph placed. -/
  last : Option Glyph := none

/-- The leftover characters `cs` of a closing sequence, placed at MuPDF's pen: zero-width
glyphs at the advance end of the last glyph placed (`flush_actualtext`; nothing without a
previous glyph, or when that glyph lies entirely outside `box`, MuPDF's `last.clipped`). -/
def flushChars (box : Option (Fixed × Fixed × Fixed × Fixed)) (last : Option Glyph)
    (cs : List Char) : List Glyph :=
  match last with
  | none => []
  | some g =>
    if (match box with | some b => g.offPage b | none => false) then []
    else
      let p := unFrame g.dir g.uEnd g.v
      cs.map fun ch => { g with text := normalize (String.singleton ch), code := [], x := p.1,
                                 y := p.2, width := Fixed.zero, adv := Fixed.zero }

/-- One glyph under the innermost open `/ActualText` sequence (MuPDF
`do_extract_within_actualtext` without its prefix/postfix matching, which compares glyph ids
with Unicode values): it takes the sequence's next character, keeping its position and
advance; once the characters are used up (or the `/ActualText` is empty) it is dropped. -/
def actGlyph (st : ActState) (g : Glyph) : ActState × List Glyph :=
  match st.open_ with
  | [] => ({ st with last := some g }, [g])
  | [] :: _ => (st, [])
  | (ch :: more) :: rest =>
    let g' := { g with text := normalize (String.singleton ch) }
    ({ open_ := more :: rest, last := some g' }, [g'])

/-- The glyphs of a list under the `/ActualText` state, in order. -/
def actGlyphs (st : ActState) : List Glyph → ActState × List Glyph
  | [] => (st, [])
  | g :: gs =>
    let (st, out) := actGlyph st g
    let (st, out2) := actGlyphs st gs
    (st, out ++ out2)

/-- One display item under the `/ActualText` state: a glyph run's glyphs (`runGlyphs`) through
`actGlyph`; `actualTextBegin` opens a sequence; `actualTextEnd` closes the innermost one,
placing its unused characters at the pen (`flushChars`; MuPDF `fz_stext_end_metatext`). -/
def actItem (fonts : FontTable) (box : Option (Fixed × Fixed × Fixed × Fixed)) (i : Nat)
    (st : ActState) : DisplayItem → ActState × List Glyph
  | .glyphRun r _ => actGlyphs st (runGlyphs fonts i r)
  | .actualTextBegin t => ({ st with open_ := actualChars t :: st.open_ }, [])
  | .actualTextEnd =>
    match st.open_ with
    | [] => (st, [])
    | cs :: rest => ({ st with open_ := rest }, flushChars box st.last cs)
  | _ => (st, [])

/-- The glyphs of a display list from index `i` on, `/ActualText` applied. -/
def actualAux (fonts : FontTable) (box : Option (Fixed × Fixed × Fixed × Fixed)) :
    Nat → ActState → List DisplayItem → ActState × List Glyph
  | _, st, [] => (st, [])
  | i, st, it :: rest =>
    let (st, out) := actItem fonts box i st it
    let (st, out2) := actualAux fonts box (i + 1) st rest
    (st, out ++ out2)

/-- Close every sequence still open at the end (MuPDF `clear_marked_content` at the end of the
page), innermost first. -/
def closeAll (box : Option (Fixed × Fixed × Fixed × Fixed)) :
    List (List Char) → Option Glyph → List Glyph
  | [], _ => []
  | cs :: rest, last => flushChars box last cs ++ closeAll box rest last

/-- **The glyphs as shown** (task 6.8d): the extraction of the display list with the
`/ActualText` of marked content applied, as MuPDF's structured-text device does — each glyph
inside an `/ActualText` sequence takes the next character of the sequence at its own position
(the innermost sequence applies; glyphs beyond its characters, and all glyphs of an empty
`/ActualText`, are dropped), unused characters go to the pen when the sequence closes, and
sequences open at the end of the list are closed there. `box` is the page box glyphs are
clipped to (`Options.pageBox`). Without `actualTextBegin` items this is `extractItems`
(`shownItems_eq_extract`). -/
def shownItems (fonts : FontTable) (box : Option (Fixed × Fixed × Fixed × Fixed))
    (items : List DisplayItem) : List Glyph :=
  shownAux fonts box 0 items
where
  /-- `shownItems` from index `i` on (annotation items continue the page's indices). -/
  shownAux (fonts : FontTable) (box : Option (Fixed × Fixed × Fixed × Fixed)) (i : Nat)
      (items : List DisplayItem) : List Glyph :=
    let (st, out) := actualAux fonts box i {} items
    out ++ closeAll box st.open_ st.last

/-- Whether a display item is an `/ActualText` mark. -/
def isActualMark : DisplayItem → Bool
  | .actualTextBegin _ | .actualTextEnd => true
  | _ => false

/-- Outside `/ActualText` sequences glyphs pass through unchanged. -/
theorem actGlyphs_none (gs : List Glyph) (last : Option Glyph) :
    (actGlyphs { open_ := [], last } gs).2 = gs ∧
      (actGlyphs { open_ := [], last } gs).1.open_ = [] := by
  induction gs generalizing last with
  | nil => simp [actGlyphs]
  | cons g gs ih =>
    have := ih (some g)
    simp only [actGlyphs, actGlyph] at this ⊢
    exact ⟨by rw [this.1]; rfl, this.2⟩

/-- Without `/ActualText` marks, `actualAux` is `extractAux` and leaves nothing open. -/
theorem actualAux_none (fonts : FontTable) (box : Option (Fixed × Fixed × Fixed × Fixed)) :
    ∀ (i : Nat) (last : Option Glyph) (items : List DisplayItem),
      items.all (fun it => !isActualMark it) = true →
      (actualAux fonts box i { open_ := [], last } items).2 = extractAux fonts i items ∧
        (actualAux fonts box i { open_ := [], last } items).1.open_ = []
  | _, _, [], _ => by simp [actualAux, extractAux]
  | i, last, it :: rest, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    cases it with
    | glyphRun r clip =>
      have hg := actGlyphs_none (runGlyphs fonts i r) last
      simp only [actualAux, actItem, extractAux, itemGlyphs]
      generalize actGlyphs { open_ := [], last } (runGlyphs fonts i r) = q at hg
      obtain ⟨st, out⟩ := q
      obtain ⟨st0, st1⟩ := st
      simp only at hg
      obtain ⟨rfl, rfl⟩ := hg
      have := actualAux_none fonts box (i + 1) st1 rest h.2
      exact ⟨by rw [this.1], this.2⟩
    | actualTextBegin t => simp [isActualMark] at h
    | actualTextEnd => simp [isActualMark] at h
    | _ =>
      have := actualAux_none fonts box (i + 1) last rest h.2
      simp only [actualAux, actItem, extractAux, itemGlyphs, List.nil_append]
      exact this

/-- **No `/ActualText`, no change**: when a display list has no `/ActualText` marks, the
glyphs as shown are exactly the extracted glyphs (`extractItems`, with its C3/C6 provenance). -/
theorem shownItems_eq_extract (fonts : FontTable) (box : Option (Fixed × Fixed × Fixed × Fixed))
    (items : List DisplayItem) (h : items.all (fun it => !isActualMark it) = true) :
    shownItems fonts box items = extractItems fonts items := by
  have := actualAux_none fonts box 0 none items h
  simp only [shownItems, shownItems.shownAux, extractItems]
  generalize actualAux fonts box 0 { open_ := [], last := none } items = q at this
  obtain ⟨⟨op, last⟩, out⟩ := q
  simp only at this
  obtain ⟨rfl, rfl⟩ := this
  simp [closeAll]

/-! ## Clipping (task 6.8f; as MuPDF's `FZ_STEXT_CLIP`) -/

/-- A page-space box `(x0, y0, x1, y1)`. -/
abbrev Box := Fixed × Fixed × Fixed × Fixed

/-- The bounding box of the points of a path, curve control points included (MuPDF's
`fz_bound_path`); `none` for a path without points. -/
def pathBox (p : Path) : Option Box :=
  let grow (b : Option Box) (q : Point) : Option Box :=
    match b with
    | none => some (q.x, q.y, q.x, q.y)
    | some (x0, y0, x1, y1) => some (fmin x0 q.x, fmin y0 q.y, fmax x1 q.x, fmax y1 q.y)
  p.segs.foldl (fun b s => match s with
    | .moveTo q | .lineTo q => grow b q
    | .curveTo c1 c2 q => grow (grow (grow b c1) c2) q
    | .closePath => b) none

/-- The **scissor** of a clip: the intersection of the bounding boxes of its paths (MuPDF's
device clip stack, `fz_device_current_scissor`); `none` when unclipped. An empty intersection
(or a path without points) is a box with `x1 < x0`. -/
def scissor (c : Clip) : Option Box :=
  c.foldl (fun acc cp =>
    let b := (pathBox cp.path).getD (Fixed.one, Fixed.one, Fixed.zero, Fixed.zero)
    match acc with
    | none => some b
    | some (x0, y0, x1, y1) =>
      some (fmax x0 b.1, fmax y0 b.2.1, fmin x1 b.2.2.1, fmin y1 b.2.2.2)) none

/-- Whether glyph `g` is hidden by the scissor `s`: the box is empty, or the glyph's box
(`Glyph.bounds`) lies entirely outside it (`Glyph.offPage`; MuPDF
`fz_glyph_entirely_outside_box`). -/
def hiddenBy (s : Option Box) (g : Glyph) : Bool :=
  match s with
  | none => false
  | some b => b.2.2.1.raw < b.1.raw || b.2.2.2.raw < b.2.1.raw || g.offPage b

/-- The scissor of every display item: that of its clip for a glyph run, `none` otherwise
(computed once per run). -/
def itemScissors (items : Array DisplayItem) : Array (Option Box) :=
  items.map fun it => match it with
    | .glyphRun _ c => scissor c
    | _ => none

/-- **Clipped text** (task 6.8f): the glyphs whose glyph run (`Glyph.item`, an index into
`items`) was clipped so that the glyph lies entirely outside the scissor of the clip are left
out, as MuPDF's text device does under `FZ_STEXT_CLIP` (which `mutool draw` sets): e.g. the
labels of a matplotlib figure drawn outside its axes clip, invisible on the rendered page.
Glyphs whose `item` is not a glyph run of `items` (an annotation's) are kept. -/
def unclipped (items : Array DisplayItem) (gs : List Glyph) : List Glyph :=
  let sc := itemScissors items
  gs.filter fun g => !hiddenBy (sc[g.item]?.getD none) g

/-- Without clips nothing is hidden. -/
theorem unclipped_of_none (items : Array DisplayItem) (gs : List Glyph)
    (h : ∀ g ∈ gs, (itemScissors items)[g.item]?.getD none = none) :
    unclipped items gs = gs := by
  unfold unclipped
  rw [List.filter_eq_self]
  intro g hg
  simp [h g hg, hiddenBy]

/-! ## Pages -/

/-- The text of a page, with everything it was computed from. -/
structure PageText where
  /-- The fonts used (by `FontKey`). -/
  fonts : FontTable
  /-- The display list of the page (the runner's output, fonts' advances applied). -/
  items : DisplayList
  /-- All glyphs, content order (`extractItems fonts items`). -/
  glyphs : List Glyph
  /-- The glyphs as shown (task 6.8d): `glyphs` with the `/ActualText` of marked content
  applied (`shownItems`; equal to `glyphs` when the page has none, `shownItems_eq_extract`),
  without the glyphs the clip hides (`unclipped`, task 6.8f; nothing is hidden on an
  unclipped page, `unclipped_of_none`). Lines and text are laid out from these. -/
  shown : List Glyph
  /-- Lines in reading order. -/
  lines : Array Line
  /-- The page text. -/
  text : String
  /-- Interpreter warnings. -/
  warnings : Nat
  /-- Operators the page run executed (page and forms). Task 8.3b: the annotations of the page
  get what is left of `Limits.maxOpsPerPage` (`Annot.Budget.after`). -/
  ops : Nat := 0
  /-- Forms the page run expanded; the annotations get what is left of
  `Limits.maxFormsPerPage`. -/
  forms : Nat := 0

/-- The runner environment with the fonts' advances. -/
def textEnv {σ : Type} (limits : Limits) (src : Source σ) (fonts : FontTable) : Env σ Unit :=
  { cfg := { limits, advance := advanceFn fonts }, src, observe := fun u _ _ _ => u }

/-- **Entry point.** Extract the text of decoded page content `content` with resources `res`:
load fonts, run the content once, read the glyph runs of that run's display list. Total. -/
def extractPage {σ : Type} (limits : Limits) (src : Source σ) (res : Dict) (content : ByteArray)
    (s : σ) (o : Options := {}) : PageText × σ :=
  let (fonts, s) := loadFonts limits src s res
  let st := runBytes (textEnv limits src fonts) res content s ()
  let gs := extractItems fonts st.items.toList
  let sh := unclipped st.items (shownItems fonts o.pageBox st.items.toList)
  let (lines, text) := layout o sh
  ({ fonts := fonts, items := st.items, glyphs := gs, shown := sh, lines := lines, text := text,
     warnings := st.warnings, ops := st.ops, forms := st.forms }, st.s)

/-- **C6 (same pass)**: the page's glyphs are the extraction of the page's own display list,
under its own fonts — the list the runner produced, not a second interpretation. -/
theorem extractPage_glyphs {σ : Type} (limits : Limits) (src : Source σ) (res : Dict)
    (content : ByteArray) (s : σ) (o : Options) :
    (extractPage limits src res content s o).1.glyphs =
      extractItems (extractPage limits src res content s o).1.fonts
        (extractPage limits src res content s o).1.items.toList := rfl

/-- **C6 (display list)**: the page's display list is the runner's output for the page content
with the fonts' advances. -/
theorem extractPage_items {σ : Type} (limits : Limits) (src : Source σ) (res : Dict)
    (content : ByteArray) (s : σ) (o : Options) :
    (extractPage limits src res content s o).1.items =
      (runBytes (textEnv limits src (loadFonts limits src s res).1) res content
        (loadFonts limits src s res).2 ()).items := rfl

/-! ### Documents -/

open SafePdf.Core.Doc
open SafePdf.Core.Filter (Budget)

/-- Document access for the runner: `OpenDoc.getObject`, and stream decoding under the
document budget (`decodeBodyB`, rules D1–D2, as `Doc.decodeStreamOf` without a second fetch;
an image codec is an error, rule D3). Shared with the inspector's `svg`/`ops` views. -/
def docSource (limits : Limits) (doc : Doc) : Source Budget :=
  ⟨fun b n g => (doc.file.getObject limits n g, b),
   fun b n st =>
     let r := decodeBodyB doc.file limits b (offsetOf doc.file n) (.stream st)
     (contentData (offsetOf doc.file n) r.1, r.2)⟩

/-- Concatenate decoded content parts with one space byte between them (§7.8.2). -/
def joinParts : List ByteArray → ByteArray
  | [] => ByteArray.empty
  | p :: ps => ps.foldl (fun acc b => (acc.push 32) ++ b) p

/-- The options for a page: `pageBox` defaults to the page's CropBox (which lies inside its
MediaBox, `Doc.cropBox_sub_media`), the area MuPDF's text device clips to. -/
def Options.forPage (o : Options) (page : Page) : Options :=
  match o.pageBox with
  | some _ => o
  | none =>
    let c := page.cropBox
    { o with pageBox := some (Fixed.ofDecimal c.llx, Fixed.ofDecimal c.lly,
                              Fixed.ofDecimal c.urx, Fixed.ofDecimal c.ury) }

/-- Extract the text of a page of an opened document, charging `budget`. Lines and text leave
out glyphs entirely outside the page's CropBox (`Options.forPage`); `glyphs` keeps them. -/
def extractDocPage (limits : Limits) (doc : Doc) (page : Page) (budget : Budget)
    (o : Options := {}) : (Except Error PageText) × Budget :=
  match doc.decodeContentsB limits budget page with
  | (.error e, b) => (.error e, b)
  | (.ok parts, b) =>
    let (pt, b) := extractPage limits (docSource limits doc) (page.resources.getD [])
      (joinParts parts) b (o.forPage page)
    (.ok pt, b)

/-! ## Spot checks -/

section Tests

/-- A PDF whose objects `1 …` are the given bodies (as `Core.Doc`'s tests). -/
private def mkPdf (objs : List String) : ByteArray := Id.run do
  let mut body := "%PDF-1.4\n"
  let mut offs : List Nat := []
  let mut i := 1
  for o in objs do
    offs := offs ++ [body.utf8ByteSize]
    body := body ++ s!"{i} 0 obj\n{o}\nendobj\n"
    i := i + 1
  let row (o : Nat) : String :=
    let s := toString o
    String.ofList (List.replicate (10 - s.length) '0') ++ s ++ " 00000 n \n"
  let x := body.utf8ByteSize
  let rows := String.join (offs.map row)
  (body ++ s!"xref\n0 {objs.length + 1}\n0000000000 65535 f \n" ++ rows ++
    s!"trailer\n<< /Size {objs.length + 1} /Root 1 0 R >>\nstartxref\n{x}\n%%EOF\n").toUTF8

/-- A stream object body. -/
private def strmObj (d data : String) : String :=
  s!"<< {d} /Length {data.utf8ByteSize} >>\nstream\n{data}\nendstream"

/-- One page with content `c` and font resources `fonts`; extra objects from 5 on. -/
private def page (fonts c : String) (extra : List String := []) : ByteArray := mkPdf ([
  "<< /Type /Catalog /Pages 2 0 R >>",
  "<< /Type /Pages /Kids [3 0 R] /Count 1 /MediaBox [0 0 612 792] >>",
  s!"<< /Type /Page /Parent 2 0 R /Resources << /Font << {fonts} >> >> /Contents 4 0 R >>",
  strmObj "" c] ++ extra)

/-- Extract page 1. -/
private def ext (b : ByteArray) (o : Options := {}) : Option PageText :=
  match openDoc {} b with
  | .ok doc =>
    match doc.pages.toList with
    | p :: _ =>
      match (extractDocPage {} doc p (Budget.init {}) o).1 with
      | .ok t => some t
      | .error _ => none
    | [] => none
  | .error _ => none

private def txt (b : ByteArray) (o : Options := {}) : String := ((ext b o).map (·.text)).getD "<error>"

/-- Glyph origins as `(text, x·1000, y·1000)` (exact in thousandths). -/
private def pos (b : ByteArray) : List (String × Int × Int) :=
  ((ext b).map fun t => t.glyphs.map fun g => (g.text, g.x.raw / 1000, g.y.raw / 1000)).getD []

private def helv : String := "/F1 5 0 R"
private def helvObj : String :=
  "<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica /Encoding /WinAnsiEncoding >>"

private def hello : ByteArray := page helv "BT /F1 12 Tf 72 700 Td (Hello World) Tj ET" [helvObj]

-- Helvetica: H 722, e 556, l 222, o 556, space 278 (×12/1000)
#guard txt hello == "Hello World"
#guard (pos hello).take 3 == [("H", 72000, 700000), ("e", 80664, 700000), ("l", 87336, 700000)]
#guard ((pos hello).find? (·.1 == "W")).map (·.2.1) == some 102672
#guard ((ext hello).map fun t => t.glyphs.map (·.fontSize.raw)).getD [] |>.all (· == 12000000)
-- the display list carries the advance: a second Tj continues where the first ended
#guard (pos (page helv "BT /F1 12 Tf 72 700 Td (He) Tj (l) Tj ET" [helvObj])).map (·.2.1) ==
  [72000, 80664, 87336]
-- TJ gap and Td move become spaces; two lines; blank line on a large gap
#guard txt (page helv "BT /F1 10 Tf 72 700 Td [(Hello) -300 (World)] TJ ET" [helvObj]) ==
  "Hello World"
#guard txt (page helv "BT /F1 10 Tf 72 700 Td (Line) Tj 30 0 Td (one) Tj 0 -12 Td (Line two) Tj ET"
  [helvObj]) == "Line one\nLine two"
#guard txt (page helv "BT /F1 10 Tf 72 700 Td (A) Tj 0 -40 Td (B) Tj ET" [helvObj]) == "A\n\nB"
-- left-to-right inside a line even when shown right to left; kerning (small TJ) is no space
#guard txt (page helv "BT /F1 10 Tf 100 700 Td (World) Tj -50 0 Td (Hello) Tj ET" [helvObj]) ==
  "Hello World"
#guard txt (page helv "BT /F1 10 Tf 72 700 Td [(W) 80 (orld)] TJ ET" [helvObj]) == "World"
-- text rotated by 90° (an arXiv stamp): grouped along its own baseline
#guard txt (page helv "BT /F1 10 Tf 0 1 -1 0 30 100 Tm (arXiv) Tj 0 1 -1 0 30 140 Tm (stamp) Tj ET"
  [helvObj]) == "arXiv stamp"
-- invisible text (Tr 3): kept by default, dropped on request
#guard txt (page helv "BT /F1 10 Tf 3 Tr 72 700 Td (ocr) Tj ET" [helvObj]) == "ocr"
#guard txt (page helv "BT /F1 10 Tf 3 Tr 72 700 Td (ocr) Tj ET" [helvObj])
  { includeInvisible := false } == ""
-- task 6.8b: glyphs entirely outside the CropBox (here the MediaBox [0 0 612 792]) are left out
-- of the text one by one ("Edg" past x = 612: MuPDF's FZ_STEXT_CLIP), but kept in `glyphs`
#guard txt (page helv "BT /F1 12 Tf 72 900 Td (Above) Tj ET BT /F1 12 Tf 72 700 Td (In) Tj ET"
  [helvObj]) == "In"
#guard txt (page helv "BT /F1 12 Tf 592 700 Td (Edge) Tj ET" [helvObj]) == "Edg"
#guard ((ext (page helv "BT /F1 12 Tf 72 900 Td (Above) Tj ET" [helvObj])).map
  (·.glyphs.length)) == some 5
-- an explicit `pageBox` wins over the CropBox
#guard txt (page helv "BT /F1 12 Tf 72 900 Td (Above) Tj ET" [helvObj])
  { pageBox := some (Fixed.zero, Fixed.zero, Fixed.ofInt 1000, Fixed.ofInt 1000) } == "Above"
-- the box of a glyph drawn downwards (quarter turn 3): its advance downwards, ink towards +x
private def gDown : Glyph :=
  { text := "A", code := [65], item := 0, seq := 0, x := Fixed.ofInt 100, y := Fixed.ofInt 500,
    width := Fixed.ofInt 10, dir := 3, fontSize := Fixed.ofInt 10, visible := true }
#guard gDown.bounds == (Fixed.ofInt 98, Fixed.ofInt 490, Fixed.ofInt 108, Fixed.ofInt 500)

-- a superscript raised 0.55 em by `Ts` stays on its line (beyond `lineTol`: `scriptJoin`, and
-- `nearPrev` — 5.5 pt is below 0.8 of its 7 pt size); with both off it starts a line
#guard txt (page helv "BT /F1 10 Tf 72 700 Td (mc) Tj /F1 7 Tf 5.5 Ts (2) Tj /F1 10 Tf 0 Ts ( x) Tj ET"
  [helvObj]) == "mc2 x"
#guard txt (page helv "BT /F1 10 Tf 72 700 Td (mc) Tj /F1 7 Tf 5.5 Ts (2) Tj /F1 10 Tf 0 Ts ( x) Tj ET"
  [helvObj] ) { scriptRaise := 500, baseMax := 500 } == "mc\n2\n x"

/-- A Type0 Identity-H font with `/W` and a ToUnicode CMap (2-byte codes, a `bfrange`). -/
private def cidPdf : ByteArray := page "/F2 5 0 R" "BT /F2 10 Tf 72 700 Td <000100020003> Tj ET" [
  "<< /Type /Font /Subtype /Type0 /BaseFont /X /Encoding /Identity-H /DescendantFonts [6 0 R] /ToUnicode 7 0 R >>",
  "<< /Type /Font /Subtype /CIDFontType2 /BaseFont /X /W [1 [500 600]] /DW 1000 >>",
  strmObj "" "1 begincodespacerange <0000> <FFFF> endcodespacerange\n1 beginbfrange <0001> <0003> <0041> endbfrange"]

#guard txt cidPdf == "ABC"
#guard (pos cidPdf).map (·.2.1) == [72000, 77000, 83000]
#guard ((ext cidPdf).map fun t => t.glyphs.map (·.code)).getD [] == [[0, 1], [0, 2], [0, 3]]

/-- A ligature through `/Differences` (glyph name `fi`) on Times-Roman, no `/Widths`. -/
private def ligPdf : ByteArray := page "/F3 5 0 R" "BT /F3 10 Tf 72 700 Td (\\001le) Tj ET" [
  "<< /Type /Font /Subtype /Type1 /BaseFont /Times-Roman /Encoding << /Differences [1 /fi] >> >>"]

#guard txt ligPdf == "file"
#guard ((ext ligPdf).map fun t => t.glyphs.map (·.text)).getD [] == ["fi", "l", "e"]

-- 6.7d: an accent drawn before its (overlapping) base letter keeps content order; no space
-- after a math operator (U+2212), but after a Latin letter and after × (U+00D7)
#guard txt (page helv "BT /F1 10 Tf 72 700 Td [(\\270) 416 (ca)] TJ ET" [helvObj]) == "¸ca"
#guard spaceMayFollow "a" && spaceMayFollow "×" && spaceMayFollow "†" && spaceMayFollow ""
#guard !spaceMayFollow "−" && !spaceMayFollow "≤" && !spaceMayFollow "中" && !spaceMayFollow "a "

-- 6.12: a font that is not a resource (or not a dictionary) gets MuPDF's substitute
-- Times-Roman: StandardEncoding text (0x27 is quoteright), Times widths (a = 444)
#guard txt (page helv "BT /F9 10 Tf 72 700 Td (a') Tj ET" [helvObj]) == "a’"
#guard (pos (page helv "BT /F9 10 Tf 72 700 Td (ab) Tj ET" [helvObj])).map (·.2.1) == [72000, 76440]
#guard txt (page "/F1 42" "BT /F1 10 Tf 72 700 Td (Hi) Tj ET" []) == "Hi"

-- C3 bytes, on a run: glyph codes concatenate to the shown bytes
#guard ((ext hello).map fun t => (t.glyphs.map Glyph.code).flatten) == some "Hello World".toUTF8.toList
-- Type 3 advances truncate toward zero to 1/1000 em (MuPDF's integer metrics)
#guard (type3TruncWidth (Fixed.clamp 556999)).raw == 556000
#guard (type3TruncWidth (Fixed.clamp (-556999))).raw == -556000

end Tests

end SafePdf.Core.Text
