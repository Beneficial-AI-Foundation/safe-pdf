import SafePdf.Core.Doc.Nav
import SafePdf.Core.Font.CMap

/-!
# Embedded files: the attachments panel's data (task 9.r10)

Plan.md §6 Phase 9 (the viewer: sidebar panels after PDF.js, the document's `/PageMode
/UseAttachments`), §4 S2 (totality), S3 (limits), §5.2 (bounded work, visited sets).
ISO 32000-2 §7.11 (file specifications: `/F`, `/UF`, `/Desc`, `/EF`), §7.11.4 (embedded file
streams: `/Subtype`, `/Params` with `/Size`, `/CreationDate`, `/ModDate`), §7.7.4 (the
`/Names /EmbeddedFiles` name tree), §7.9.6 (name trees), §7.9.2.2 (text strings), §7.9.4
(dates), §12.5.6.15 (file attachment annotations, `/FS`).

`list doc limits` finds every embedded file a viewer shows; `decode doc limits e` gives its
bytes. Both are pure and total. Like `Nav`, listing **never fails the document**: a value of
the wrong shape, a failed fetch, a cycle is skipped and counted, or kept on the entry as a
`Problem`. Decoding errors are values (`Except Error`), one per entry.

**Nothing here opens, launches or interprets an attachment**: an entry is data (names, sizes,
a stream reference); the bytes are only decoded through the filter pipeline.

## Rules

* A1. **Sources.** First the `/Names /EmbeddedFiles` name tree of the catalog, enumerated by
  `Nav.treeEntries` (rule N2: visited set, fuel `objectCount`, a `/Kids` cycle is cut and
  counted), in key order as stored; then, page by page, the `/FileAttachment` annotations of
  each page's `/Annots` (at most `maxAnnotsPerPage` elements per page are looked at), their
  `/FS` value. Values are resolved one level (`Nav.getL`, rule N1).
* A2. **One entry per file specification.** An annotation whose `/FS` is a reference to a file
  specification already listed (same object number) adds no entry; its icon points at the
  existing one, which takes the annotation's page if it had none. At most `maxAttachments`
  entries are kept; more set `truncated`.
* A3. **Names** (§7.11.3): `/UF` (a text string) when it is a string, else `/F`, else the
  name-tree key, else `"attachment"`. Decoded as a text string (`textChars`: UTF-16BE after
  `FE FF`, UTF-8 after `EF BB BF`, else PDFDocEncoding) and **sanitized** (`clean`): C0/C1
  controls, DEL, the bidi embedding/override/isolate marks, LRM/RLM, the line/paragraph
  separators and U+FEFF are dropped (tab, line feed and carriage return become a space),
  spaces at both ends removed, at most `maxNameChars` characters (a longer name ends in `…`).
  `/Desc` the same way with `maxDescChars`. A file specification that is a plain string is
  its own `/F`.
* A4. **Default file name** (`fileNameOf`): the sanitized name's last path component (after
  the last `/` or `\`), with `:*?"<>|` replaced by `_`, leading dots and spaces and trailing
  dots and spaces removed, at most `maxFileNameBytes` bytes of UTF-8; empty → `attachment`.
  It never contains `/` (`fileNameOf_noSlash`) and is never `.` or `..`.
* A5. **Stream** (§7.11.4): `/EF` (a dictionary) `/F`, else `/EF /UF`, must be an indirect
  reference to a stream. Its dictionary gives `/Subtype` (a name: the MIME type, sanitized),
  `/Params /Size` (a non-negative integer: the declared size), `/Params /CreationDate` and
  `/ModDate` (dates `D:YYYYMMDDHHmmSS…` shown as `YYYY-MM-DD HH:mm`; anything else sanitized
  as is). No `/EF`: `Problem.notEmbedded`; `/EF` without a reference: `badEF`; the reference
  is not a stream or cannot be fetched: `notAStream`.
* A6. **Decoding** (`decode`): the stream through `Doc.decodeStreamOf` (the filter chain under
  `limits`, with a fresh document budget `Budget.init` per call). A decompression bomb is
  `Error.limitExceeded`; a chain ending in an image codec is `unsupported` (an embedded file
  is bytes, not an image). The size shown is `/Params /Size`, else the decoded length.

## Work bounds

The tree walk fetches at most `objectCount` nodes (`Nav.treeWalk_visited_le`). Per page: one
page fetch, at most `maxAnnotsPerPage` one-level resolutions plus a fixed number per
attachment annotation. Per entry: a fixed number of one-level resolutions and one object
fetch. Strings are cut before decoding (`maxNameChars`·4 bytes). Deduplication is quadratic
in the number of entries, at most `maxAttachments`.

## Theorems

* `list_entries_le`: at most `maxAttachments` entries.
* `clean_length_le`, `clean_safe`: a sanitized string is bounded and has no hidden character.
* `fileNameOf_noSlash`: a default file name has no `/`.
* `decode_size_le`: decoded bytes are at most `limits.maxDecodedStreamBytes`.
-/

namespace SafePdf.Core.Doc.Attachments

open SafePdf
open SafePdf.Core.Doc
open SafePdf.Core.Doc.Nav

/-! ## Bounds -/

/-- At most this many attachments are listed (rule A2). -/
def maxAttachments : Nat := 1024

/-- At most this many `/Annots` elements of one page are looked at (rule A1). -/
def maxAnnotsPerPage : Nat := 4096

/-- Longest display name, in characters (rule A3). -/
def maxNameChars : Nat := 200

/-- Longest description, in characters (rule A3). -/
def maxDescChars : Nat := 1000

/-- Longest default file name, in UTF-8 bytes (rule A4). -/
def maxFileNameBytes : Nat := 200

/-! ## Text (rules A3, A4) -/

/-- Whether a character is dropped from displayed text (rule A3): C0/C1 controls, DEL, the
bidi embedding, override and isolate controls, LRM/RLM, ALM, the line and paragraph separators
and the zero-width no-break space (they could hide, reorder or break the text around them). -/
def hidden (c : Char) : Bool :=
  c.toNat < 0x20 || (0x7F ≤ c.toNat && c.toNat < 0xA0) ||
  (0x202A ≤ c.toNat && c.toNat ≤ 0x202E) || (0x2066 ≤ c.toNat && c.toNat ≤ 0x2069) ||
  c.toNat == 0x200E || c.toNat == 0x200F || c.toNat == 0x061C ||
  c.toNat == 0x2028 || c.toNat == 0x2029 || c.toNat == 0xFEFF

/-- One PDFDocEncoding byte as characters (the glyph list); undefined bytes are U+FFFD. -/
def pdfDocChars (b : UInt8) : List Char :=
  if b == 9 || b == 10 || b == 13 then [Char.ofNat b.toNat]
  else match (Font.pdfDocEncoding.glyph b.toNat).bind Font.glyphToUnicode with
    | some s => s.toList
    | none => [Font.CMap.replacement]

/-- A text string's characters (§7.9.2.2): UTF-16BE after `FE FF`, UTF-8 after `EF BB BF`
(PDF 2.0; invalid UTF-8 falls back to PDFDocEncoding), else PDFDocEncoding. -/
def textChars (bs : List UInt8) : List Char :=
  match bs with
  | 0xFE :: 0xFF :: rest => Font.CMap.utf16 rest
  | 0xEF :: 0xBB :: 0xBF :: rest =>
    match String.fromUTF8? ⟨rest.toArray⟩ with
    | some s => s.toList
    | none => rest.flatMap pdfDocChars
  | _ => bs.flatMap pdfDocChars

/-- Tab, line feed and carriage return become spaces; other hidden characters go. -/
def scrub (cs : List Char) : List Char :=
  cs.filterMap fun c =>
    if c == '\t' || c == '\n' || c == '\r' then some ' '
    else if hidden c then none else some c

/-- Spaces at both ends removed. -/
def trimSpaces (cs : List Char) : List Char :=
  ((cs.dropWhile (· == ' ')).reverse.dropWhile (· == ' ')).reverse

/-- At most `m` characters; a longer list keeps `m - 1` and ends in `…` (for `m ≥ 1`). -/
def cut (m : Nat) (cs : List Char) : List Char :=
  if cs.length ≤ m then cs else cs.take (m - 1) ++ ['…']

/-- **Sanitize** text for display (rule A3): hidden characters dropped (whitespace controls as
spaces), trimmed, at most `m` characters (`m ≥ 1`). -/
def clean (m : Nat) (cs : List Char) : List Char := cut m (trimSpaces (scrub cs))

/-- A text string sanitized for display (rule A3), at most `m` characters; bytes beyond
`4 * m + 3` are not decoded (no more characters could be kept). -/
def displayText (m : Nat) (bs : List UInt8) : String :=
  String.ofList (clean m (textChars (bs.take (4 * m + 3))))

/-- Whether a character is replaced in a default file name (rule A4). -/
def badFileChar (c : Char) : Bool := "\\/:*?\"<>|".toList.contains c

/-- The characters after the last `/` or `\`. -/
def baseName (cs : List Char) : List Char :=
  (cs.reverse.takeWhile (fun c => c != '/' && c != '\\')).reverse

/-- Leading characters kept while their UTF-8 size stays within `budget` bytes. -/
def takeBytes : Nat → List Char → List Char
  | _, [] => []
  | budget, c :: cs => if c.utf8Size ≤ budget then c :: takeBytes (budget - c.utf8Size) cs else []

/-- The characters of a default file name (rule A4) from sanitized name characters. -/
def fileNameChars (cs : List Char) : List Char :=
  let b := (baseName cs).map fun c => if badFileChar c then '_' else c
  let t := ((b.dropWhile (fun c => c == '.' || c == ' ')).reverse.dropWhile
    (fun c => c == '.' || c == ' ')).reverse
  let t := takeBytes maxFileNameBytes t
  if t.isEmpty then "attachment".toList else t

/-- **The default file name** of an attachment named `name` (rule A4). -/
def fileNameOf (name : String) : String := String.ofList (fileNameChars name.toList)

/-- Two digits of a date part, if both are digits. -/
def digitsOf (cs : List Char) : Option (List Char) :=
  if cs.all Char.isDigit then some cs else none

/-- A PDF date (§7.9.4) `D:YYYYMMDDHHmmSS…` as `YYYY-MM-DD HH:mm` (as many parts as given,
the year required); anything else is shown sanitized as it is (rule A5). -/
def dateText (bs : List UInt8) : String :=
  let cs := textChars (bs.take 64)
  let ds := match cs with
    | 'D' :: ':' :: r => r
    | r => r
  let ds := ds.takeWhile Char.isDigit
  if ds.length < 4 then String.ofList (clean 40 cs)
  else
    let part (i : Nat) (sep : String) : String :=
      let p := (ds.drop i).take 2
      if p.length == 2 then sep ++ String.ofList p else ""
    let mo := part 4 "-"
    let dd := if mo.isEmpty then "" else part 6 "-"
    let hh := if dd.isEmpty then "" else part 8 " "
    let mi := if hh.isEmpty then "" else part 10 ":"
    String.ofList (ds.take 4) ++ mo ++ dd ++ hh ++ mi

/-! ## Entries (rules A1–A5) -/

/-- Why an entry has no stream to decode (rule A5). -/
inductive Problem where
  /-- The file specification has no `/EF` (a reference to an external file). -/
  | notEmbedded
  /-- `/EF` is not a dictionary with an indirect `/F` or `/UF`. -/
  | badEF
  /-- `/EF /F` does not lead to a stream. -/
  | notAStream
  deriving DecidableEq, Repr, Inhabited

/-- A status-line text for a problem. -/
def Problem.message : Problem → String
  | .notEmbedded => "not embedded in the file (an external file reference)"
  | .badEF => "invalid /EF entry"
  | .notAStream => "the embedded file is not a stream"

/-- One listed attachment. -/
structure Attachment where
  /-- Display name (rule A3). -/
  name : String
  /-- Default file name for saving (rule A4). -/
  fileName : String
  /-- `/Desc`, sanitized. -/
  desc : Option String := none
  /-- `/Params /Size`: the declared (decoded) size. -/
  size : Option Nat := none
  /-- `/Subtype` of the stream: the MIME type, sanitized. -/
  mime : Option String := none
  /-- `/Params /CreationDate`. -/
  created : Option String := none
  /-- `/Params /ModDate`. -/
  modified : Option String := none
  /-- The page index of the (first) file attachment annotation, if any. -/
  page : Option Nat := none
  /-- Whether the entry comes from the `/EmbeddedFiles` name tree (else an annotation). -/
  inTree : Bool := false
  /-- Object number of the file specification, when it is indirect (rule A2). -/
  specNum : Option Nat := none
  /-- The embedded file stream (object and generation number). -/
  stream : Option (Nat × Nat) := none
  /-- Why there is no stream. -/
  problem : Option Problem := none
  deriving Repr, Inhabited

/-- A file attachment annotation's icon: page index, `/Rect`, and the entry it shows. -/
structure Icon where
  /-- Page index. -/
  page : Nat
  /-- The annotation's rectangle (normalized). -/
  rect : Rect
  /-- Index into `Listing.entries`. -/
  entry : Nat

/-- The attachments of a document. -/
structure Listing where
  /-- Entries, name-tree ones first, at most `maxAttachments`. -/
  entries : List Attachment
  /-- File attachment annotations with a valid `/Rect`, in page order. -/
  icons : List Icon
  /-- Problems skipped (name-tree warnings, entries that are not file specifications). -/
  warnings : Nat
  /-- Whether entries beyond `maxAttachments` were dropped. -/
  truncated : Bool

/-- A string value, if it is one. -/
def strOf : PdfObject → Option (List UInt8)
  | .string s => some s
  | _ => none

/-- The stream dictionary of object `n g`, if it is a stream. -/
def streamDict (doc : Doc) (limits : Limits) (n g : Nat) : Option Dict :=
  match doc.file.getObject limits n g with
  | .ok (.stream s) => some s.dict
  | _ => none

/-- The stream reference of an `/EF` value (rule A5). -/
def efRef : PdfObject → Except Problem (Nat × Nat)
  | .null => .error .notEmbedded
  | .dict ef =>
    match raw ef "F", raw ef "UF" with
    | some (.ref n g), _ => .ok (n, g)
    | _, some (.ref n g) => .ok (n, g)
    | _, _ => .error .badEF
  | _ => .error .badEF

/-- Fills in what the embedded file stream's dictionary says (rule A5). -/
def withStream (doc : Doc) (limits : Limits) (e : Attachment) (n g : Nat) : Attachment :=
  match streamDict doc limits n g with
  | none => { e with problem := some .notAStream }
  | some sd =>
    let mime := match getL doc limits sd "Subtype" with
      | .name nm => some (displayText 100 nm.bytes)
      | _ => none
    let (size, created, modified) := match getL doc limits sd "Params" with
      | .dict p =>
        (match getL doc limits p "Size" with
          | .int i => if 0 ≤ i then some i.toNat else none
          | _ => none,
         (strOf (getL doc limits p "CreationDate")).map dateText,
         (strOf (getL doc limits p "ModDate")).map dateText)
      | _ => (none, none, none)
    { e with stream := some (n, g), mime, size, created, modified }

/-- The entry of a file specification value `fs` (resolved one level), with `key` the
name-tree key if any (rules A3–A5). `none`: not a file specification (counted). -/
def entryOf (doc : Doc) (limits : Limits) (specNum : Option Nat) (key : Option (List UInt8))
    (fs : PdfObject) : Option Attachment :=
  let named (bs : Option (List UInt8)) : String × String :=
    let n := match bs.map (displayText maxNameChars) with
      | some s => if s.isEmpty then "attachment" else s
      | none => "attachment"
    (n, fileNameOf n)
  match fs with
  | .string s =>
    let (n, f) := named (some s)
    some { name := n, fileName := f, specNum, problem := some .notEmbedded }
  | .dict d =>
    let nm := (strOf (getL doc limits d "UF")).orElse fun _ =>
      (strOf (getL doc limits d "F")).orElse fun _ => key
    let (n, f) := named nm
    let desc := (strOf (getL doc limits d "Desc")).map (displayText maxDescChars)
    let e : Attachment := { name := n, fileName := f, desc := desc.filter (!·.isEmpty), specNum }
    match efRef (getL doc limits d "EF") with
    | .error p => some { e with problem := some p }
    | .ok (sn, sg) => some (withStream doc limits e sn sg)
  | _ => none

/-- The object number of a reference. -/
def refNum : PdfObject → Option Nat
  | .ref n _ => some n
  | _ => none

/-- The entries of the `/Names /EmbeddedFiles` tree (rule A1), and the number of warnings. -/
def treeList (doc : Doc) (limits : Limits) : List Attachment × Nat :=
  let root := match getL doc limits doc.catalog "Names" with
    | .dict nd => (raw nd "EmbeddedFiles").getD .null
    | _ => .null
  let w := treeWalk doc limits nameTree none root
  let r := w.out.reverse.foldr (fun (k, v) (acc : List Attachment × Nat) =>
    match entryOf doc limits (refNum v) (some k) (res doc limits v) with
    | some e => ({ e with inTree := true } :: acc.1, acc.2)
    | none => (acc.1, acc.2 + 1)) ([], 0)
  (r.1, r.2 + w.warnings)

/-- Whether an annotation dictionary is a `/FileAttachment` (§12.5.6.15). -/
def isFileAttachment (doc : Doc) (limits : Limits) (ad : Dict) : Bool :=
  match getL doc limits ad "Subtype" with
  | .name s => s = Name.ofString "FileAttachment"
  | _ => false

/-- The file attachment annotations of page `i` (rule A1): (raw `/FS`, `/Rect`), in
`/Annots` order, at most `maxAnnotsPerPage` elements looked at. -/
def pageAttachments (doc : Doc) (limits : Limits) (p : Page) :
    List (PdfObject × Option Rect) :=
  match fetchDict doc limits p.num p.gen with
  | none => []
  | some pd =>
    match getL doc limits pd "Annots" with
    | .array xs =>
      (xs.take maxAnnotsPerPage).filterMap fun a =>
        match res doc limits a with
        | .dict ad =>
          if isFileAttachment doc limits ad then
            some ((raw ad "FS").getD .null, rectOf (getL doc limits ad "Rect"))
          else none
        | _ => none
    | _ => []

/-- The listing state while adding annotation attachments. -/
structure Acc where
  /-- Entries, newest last. -/
  entries : Array Attachment
  /-- Icons, newest first. -/
  icons : List Icon
  /-- Warnings. -/
  warnings : Nat
  /-- Entries dropped by the cap. -/
  truncated : Bool

/-- The index of the entry whose file specification is object `n`. -/
def findSpec (es : Array Attachment) (n : Nat) : Option Nat :=
  (List.range es.size).find? fun i => (es[i]?.bind (·.specNum)) == some n

/-- Adds an entry under the cap (rule A2); returns its index. -/
def Acc.add (a : Acc) (e : Attachment) : Acc × Option Nat :=
  if a.entries.size < maxAttachments then ({ a with entries := a.entries.push e }, some a.entries.size)
  else ({ a with truncated := true }, none)

/-- Adds one file attachment annotation of page `pg` (rules A1, A2). -/
def addAnnot (doc : Doc) (limits : Limits) (pg : Nat) (a : Acc) (x : PdfObject × Option Rect) :
    Acc :=
  let (fs, rect) := x
  let icon (a : Acc) (i : Nat) : Acc :=
    match rect with
    | some r => { a with icons := ⟨pg, r, i⟩ :: a.icons }
    | none => a
  match (refNum fs).bind (findSpec a.entries) with
  | some i =>
    let a := { a with entries := a.entries.modify i fun e =>
      if e.page.isNone then { e with page := some pg } else e }
    icon a i
  | none =>
    match entryOf doc limits (refNum fs) none (res doc limits fs) with
    | none => { a with warnings := a.warnings + 1 }
    | some e =>
      match a.add { e with page := some pg } with
      | (a, some i) => icon a i
      | (a, none) => a

/-- **The attachments of a document** (rules A1–A5). -/
def list (doc : Doc) (limits : Limits) : Listing :=
  let (tes, tw) := treeList doc limits
  let a0 : Acc := { entries := (tes.take maxAttachments).toArray, icons := [], warnings := tw,
                    truncated := decide (maxAttachments < tes.length) }
  let a := (List.range doc.pages.size).foldl (fun a i =>
    match doc.pages[i]? with
    | some p => (pageAttachments doc limits p).foldl (addAnnot doc limits i) a
    | none => a) a0
  { entries := a.entries.toList.take maxAttachments, icons := a.icons.reverse,
    warnings := a.warnings, truncated := a.truncated }

/-! ## Decoding (rule A6) -/

/-- **The decoded bytes of an attachment** (rule A6): its stream through the filter chain under
`limits` and a fresh budget. A missing stream is `malformed` with the problem's text. -/
def decode (doc : Doc) (limits : Limits) (e : Attachment) : Except Error ByteArray :=
  match e.stream with
  | none => .error (.malformed 0 ((e.problem.getD .notEmbedded).message))
  | some (n, g) =>
    match (doc.decodeStreamOf limits (Filter.Budget.init limits) n g).1 with
    | .error err => .error err
    | .ok (.data b) => .ok b
    | .ok (.image _ _ _) => .error (.unsupported "an image filter on an embedded file")

/-- The size shown for an entry (rule A6): `/Params /Size`, else the decoded length when it
decodes. -/
def shownSize (e : Attachment) (decoded : Except Error ByteArray) : Option Nat :=
  match e.size with
  | some s => some s
  | none =>
    match decoded with
    | .ok b => some b.size
    | .error _ => none

/-- A size as text: bytes, KB, MB (decimal units, one decimal below 10). -/
def sizeText (n : Nat) : String :=
  let unit (v : Nat) (u : String) : String :=
    if v < 10000 then s!"{v / 1000}.{(v % 1000) / 100} {u}" else s!"{(v + 500) / 1000} {u}"
  if n < 1000 then s!"{n} B"
  else if n < 1000000 then unit n "KB"
  else if n < 1000000000 then unit (n / 1000) "MB"
  else unit (n / 1000000) "GB"

/-! ## Theorems -/

/-- At most `maxAttachments` entries are listed. -/
theorem list_entries_le (doc : Doc) (limits : Limits) :
    (list doc limits).entries.length ≤ maxAttachments := by
  simp only [list]
  exact List.length_take_le _ _

/-- `cut` keeps at most `m` characters, for `m ≥ 1`. -/
theorem cut_length_le (m : Nat) (hm : 1 ≤ m) (cs : List Char) : (cut m cs).length ≤ m := by
  unfold cut
  split
  · assumption
  · simp only [List.length_append, List.length_take, List.length_singleton]
    omega

/-- A sanitized string has at most `m` characters (`m ≥ 1`). -/
theorem clean_length_le (m : Nat) (hm : 1 ≤ m) (cs : List Char) : (clean m cs).length ≤ m :=
  cut_length_le m hm _

/-- `scrub` leaves no hidden character. -/
theorem scrub_safe (cs : List Char) : ∀ c ∈ scrub cs, hidden c = false := by
  intro c hc
  simp only [scrub, List.mem_filterMap] at hc
  obtain ⟨a, _, h⟩ := hc
  split at h
  · cases h; decide
  · split at h
    · cases h
    · rename_i hh; cases h; simpa using hh

/-- An element after `dropWhile` was in the list. -/
theorem mem_dropWhile_sub {p : Char → Bool} {c : Char} :
    (cs : List Char) → c ∈ cs.dropWhile p → c ∈ cs
  | [], h => by simp at h
  | x :: xs, h => by
    simp only [List.dropWhile] at h
    split at h
    · exact List.mem_cons_of_mem _ (mem_dropWhile_sub xs h)
    · exact h

/-- Dropping from both ends keeps a sublist. -/
theorem trimSpaces_sub (cs : List Char) : ∀ c ∈ trimSpaces cs, c ∈ cs := by
  intro c hc
  simp only [trimSpaces, List.mem_reverse] at hc
  exact mem_dropWhile_sub _ (List.mem_reverse.mp (mem_dropWhile_sub _ hc))

/-- A sanitized string has no hidden character (rule A3). -/
theorem clean_safe (m : Nat) (cs : List Char) : ∀ c ∈ clean m cs, hidden c = false := by
  intro c hc
  simp only [clean, cut] at hc
  split at hc
  · exact scrub_safe cs c (trimSpaces_sub _ c hc)
  · rcases List.mem_append.mp hc with h | h
    · exact scrub_safe cs c (trimSpaces_sub _ c (List.mem_of_mem_take h))
    · simp only [List.mem_singleton] at h
      subst h
      decide

/-- `takeBytes` keeps a prefix. -/
theorem takeBytes_sub (b : Nat) (cs : List Char) : ∀ c ∈ takeBytes b cs, c ∈ cs := by
  induction cs generalizing b with
  | nil => intro c h; simp [takeBytes] at h
  | cons x xs ih =>
    intro c h
    simp only [takeBytes] at h
    split at h
    · rcases List.mem_cons.mp h with h | h
      · exact h ▸ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih _ c h)
    · simp at h

/-- A default file name has no `/` (rule A4). -/
theorem fileNameChars_noSlash (cs : List Char) : '/' ∉ fileNameChars cs := by
  intro h
  simp only [fileNameChars] at h
  split at h
  · revert h; decide
  · have h1 := takeBytes_sub _ _ _ h
    simp only [List.mem_reverse] at h1
    have h2 := mem_dropWhile_sub _ (List.mem_reverse.mp (mem_dropWhile_sub _ h1))
    simp only [List.mem_map] at h2
    obtain ⟨c, _, hc⟩ := h2
    split at hc
    · cases hc
    · rename_i hb
      subst hc
      exact hb (by decide)

/-- A default file name has no `/` (rule A4). -/
theorem fileNameOf_noSlash (name : String) : '/' ∉ (fileNameOf name).toList := by
  simp only [fileNameOf, String.toList_ofList]
  exact fileNameChars_noSlash _

/-- Decoded attachment bytes are at most `limits.maxDecodedStreamBytes` (rule A6). -/
theorem decode_size_le (doc : Doc) (limits : Limits) (e : Attachment) (b : ByteArray)
    (h : decode doc limits e = .ok b) : b.size ≤ limits.maxDecodedStreamBytes := by
  unfold decode at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i r hr
      cases h
      exact Doc.decodeStreamOf_size_le (r := .data b) hr
    · cases h

/-! ## Checks -/

#guard String.ofList (clean 10 "  a\tb\u202Ec\x00d  ".toList) == "a bcd"
#guard String.ofList (clean 5 "abcdefgh".toList) == "abcd…"
#guard fileNameOf "../../etc/passwd" == "passwd"
#guard fileNameOf "C:\\x\\..\\evil.exe" == "evil.exe"
#guard fileNameOf ".." == "attachment" && fileNameOf "" == "attachment"
#guard fileNameOf ".hidden. " == "hidden"
#guard fileNameOf "a:b*c?.txt" == "a_b_c_.txt"
#guard (fileNameOf (String.ofList (List.replicate 300 'é'))).utf8ByteSize == 200
#guard dateText "D:20240131120530+01'00'".toUTF8.toList == "2024-01-31 12:05"
#guard dateText "D:2024".toUTF8.toList == "2024"
#guard dateText "yesterday".toUTF8.toList == "yesterday"
#guard displayText 10 [0xFE, 0xFF, 0x00, 0x41, 0x20, 0x2E, 0x00, 0x42] == "AB"
#guard sizeText 999 == "999 B" && sizeText 1234 == "1.2 KB" && sizeText 123456 == "123 KB" &&
  sizeText 5500000 == "5.5 MB"

end SafePdf.Core.Doc.Attachments
