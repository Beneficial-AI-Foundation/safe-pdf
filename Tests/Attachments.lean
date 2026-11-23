import SafePdf
import SafePdf.Core.Doc.Attachments

/-!
# Attachments (task 9.r10)

Plan.md §6 Phase 9 (the attachments panel), ISO 32000-2 §7.11 (file specifications), §7.11.4
(embedded file streams), §7.7.4 (`/EmbeddedFiles`), §12.5.6.15 (file attachment annotations).
Small PDFs built here exercise every rule of `Core.Doc.Attachments`:

* a two-level `/EmbeddedFiles` name tree (`/Kids`, `/Limits`) with a UTF-16 `/UF`, `/Desc`,
  `/Params` (size, dates), a `/Subtype` MIME type, an `[/ASCIIHexDecode /FlateDecode]` chain
  without `/Params /Size`, an external file specification (no `/EF`), an entry named only by
  its key;
* file attachment annotations: one sharing a tree entry's file specification (no second
  entry; the icon points at it, its page is set), one with a hostile name (path, BEL, RLO);
* `/EF` problems (`badEF`, `notAStream`), a plain-string `/FS`, an image filter;
* a decompression bomb (limit error, per entry), a `/Kids` cycle in the name tree, more than
  `maxAttachments` entries, a document without attachments.
-/

namespace SafePdf.Tests.Attachments

open SafePdf.Core.Doc
open SafePdf.Core.Doc.Attachments

/-- Reports a failed check; 1 on failure. -/
def check (what : String) (ok : Bool) : IO Nat := do
  if ok then return 0
  IO.println s!"  FAIL attachments: {what}"
  return 1

/-- A PDF whose objects `1 …` are the given bodies (raw bytes), with a correct xref table. -/
def mkPdf (objs : List ByteArray) : ByteArray := Id.run do
  let mut body : ByteArray := "%PDF-1.7\n".toUTF8
  let mut offs : List Nat := []
  let mut i := 1
  for o in objs do
    offs := offs ++ [body.size]
    body := body ++ s!"{i} 0 obj\n".toUTF8 ++ o ++ "\nendobj\n".toUTF8
    i := i + 1
  let row (o : Nat) : String :=
    let s := toString o
    String.ofList (List.replicate (10 - s.length) '0') ++ s ++ " 00000 n \n"
  let x := body.size
  let rows := String.join (offs.map row)
  body ++ (s!"xref\n0 {objs.length + 1}\n0000000000 65535 f \n" ++ rows ++
    s!"trailer\n<< /Size {objs.length + 1} /Root 1 0 R >>\nstartxref\n{x}\n%%EOF\n").toUTF8

/-- A text object body. -/
def T (s : String) : ByteArray := s.toUTF8

/-- A stream object with dictionary entries `dict` and raw data `data`. -/
def S (dict : String) (data : ByteArray) : ByteArray :=
  s!"<< {dict} /Length {data.size} >>\nstream\n".toUTF8 ++ data ++ "\nendstream".toUTF8

/-- Upper-case hex of bytes. -/
def hex (b : ByteArray) : String :=
  String.ofList (b.data.toList.flatMap fun x =>
    let d (n : Nat) : Char := "0123456789ABCDEF".toList.getD n '0'
    [d (x.toNat / 16), d (x.toNat % 16)])

/-- The payload of the filter-chain attachment. -/
def payload : ByteArray := (String.join (List.replicate 40 "binary\x00data ")).toUTF8

/-- Catalog with `cat`, one 200×200 page with `/Annots annots`; extra objects from 4. -/
def doc1 (cat annots : String) (extra : List ByteArray) : ByteArray :=
  mkPdf ([T s!"<< /Type /Catalog /Pages 2 0 R {cat} >>",
    T "<< /Type /Pages /Kids [3 0 R] /Count 1 /MediaBox [0 0 200 200] >>",
    T s!"<< /Type /Page /Parent 2 0 R {annots} >>"] ++ extra)

/-- The main fixture: tree with kids, annotations, chain, external file, hostile name. -/
def treePdf : ByteArray := doc1 "/Names << /EmbeddedFiles 4 0 R >>" "/Annots [12 0 R 13 0 R]" [
  T "<< /Kids [5 0 R 6 0 R] >>",                                                         -- 4
  T "<< /Limits [(a.txt) (b.bin)] /Names [(a.txt) 7 0 R (b.bin) 8 0 R] >>",              -- 5
  T "<< /Limits [(c) (d)] /Names [(c-ext) 9 0 R (d-noname) 10 0 R] >>",                  -- 6
  T ("<< /Type /Filespec /F (old.txt) /UF <FEFF00E4002E007400780074> /Desc (First\\nfile) " ++
     "/EF << /F 11 0 R >> >>"),                                                          -- 7
  T "<< /Type /Filespec /F (b.bin) /EF << /F 14 0 R >> >>",                              -- 8
  T "<< /Type /Filespec /F (external.pdf) >>",                                           -- 9
  T "<< /Type /Filespec /EF << /F 11 0 R >> >>",                                         -- 10
  S ("/Type /EmbeddedFile /Subtype /text#2Fplain /Params << /Size 5 " ++
     "/CreationDate (D:20240131120530Z) /ModDate (D:2024) >>") "hello".toUTF8,           -- 11
  T "<< /Type /Annot /Subtype /FileAttachment /Rect [10 40 30 10] /FS 7 0 R >>",         -- 12
  T "<< /Type /Annot /Subtype /FileAttachment /Rect [50 50 70 70] /FS 15 0 R >>",        -- 13
  S "/Type /EmbeddedFile /Filter [/ASCIIHexDecode /FlateDecode]"
    (hex (SafePdf.Core.Filter.Deflate.zlibFixed payload) ++ ">").toUTF8,                 -- 14
  T ("<< /Type /Filespec /UF <FEFF002E002E005C006500760069006C0007002E006500780065202E> " ++
     "/EF << /F 16 0 R >> >>"),                                                          -- 15
  S "" "abc".toUTF8]                                                                     -- 16

/-- `/EF` problems, a string `/FS`, an image filter, a bomb, a non-file-spec tree value. -/
def oddPdf : ByteArray := doc1 "/Names << /EmbeddedFiles << /Names [(1) 4 0 R (2) 5 0 R (3) 6 0 R (4) 7 0 R (5) 42] >> >>"
    "/Annots [8 0 R 9 0 R]" [
  T "<< /F (bad-ef) /EF << /F (x) >> >>",                                               -- 4
  T "<< /F (not-stream) /EF << /F 3 0 R >> >>",                                          -- 5
  T "<< /F (image) /EF << /F 10 0 R >> >>",                                              -- 6
  T "<< /F (bomb) /EF << /F 11 0 R >> >>",                                               -- 7
  T "<< /Subtype /FileAttachment /Rect [0 0 1 1] /FS (plain.txt) >>",                    -- 8
  T "<< /Subtype /Link /Rect [0 0 1 1] >>",                                              -- 9
  S "/Filter /DCTDecode /DL 7" "xyz".toUTF8,                                                   -- 10
  S "/Filter /FlateDecode /Params << /Size 50000 >>"
    (SafePdf.Core.Filter.Deflate.zlibFixed (String.join (List.replicate 50000 "a")).toUTF8)]  -- 11

/-- A name tree whose `/Kids` form a cycle (4 → 5 → 4). -/
def cyclePdf : ByteArray := doc1 "/Names << /EmbeddedFiles 4 0 R >>" "" [
  T "<< /Kids [5 0 R] >>",
  T "<< /Kids [4 0 R 5 0 R] /Names [(x.txt) 6 0 R] >>",
  T "<< /F (x.txt) /EF << /F 7 0 R >> >>",
  S "" "x".toUTF8]

/-- More than `maxAttachments` entries (direct file specifications in one leaf). -/
def manyPdf : ByteArray :=
  let names := String.join ((List.range 1100).map fun i =>
    s!"(k{1000 + i}) << /F (f{i}) /EF << /F 4 0 R >> >> ")
  doc1 s!"/Names << /EmbeddedFiles << /Names [{names}] >> >>" "" [S "" "z".toUTF8]

/-- No attachments at all. -/
def plainPdf : ByteArray := doc1 "" "" []

/-- Opens a fixture. -/
def withDoc (what : String) (b : ByteArray) (k : Doc → IO Nat) : IO Nat := do
  match openDoc SafePdf.Limits.default b with
  | .ok d => k d
  | .error e => check s!"{what}: opens ({repr e})" false

/-- Decoded bytes, if they decode. -/
def bytesOf (d : Doc) (l : SafePdf.Limits) (e : Attachment) : Option (List UInt8) :=
  match decode d l e with
  | .ok b => some b.data.toList
  | .error _ => none

/-- Runs the suite; the number of failures. -/
def run : IO Nat := do
  let L := SafePdf.Limits.default
  let mut f := 0
  f := f + (← withDoc "tree" treePdf fun d => do
    let l := list d L
    let es := l.entries
    let mut f := 0
    f := f + (← check "tree: five entries" (es.length == 5))
    f := f + (← check "tree: names" (es.map (·.name) ==
      ["ä.txt", "b.bin", "external.pdf", "d-noname", "..\\evil.exe"]))
    f := f + (← check "tree: file names" (es.map (·.fileName) ==
      ["ä.txt", "b.bin", "external.pdf", "d-noname", "evil.exe"]))
    f := f + (← check "tree: in tree" (es.map (·.inTree) == [true, true, true, true, false]))
    f := f + (← check "tree: pages" (es.map (·.page) == [some 0, none, none, none, some 0]))
    let some a := es[0]? | check "tree: first" false
    f := f + (← check "tree: desc" (a.desc == some "First file"))
    f := f + (← check "tree: size/mime/dates" (a.size == some 5 && a.mime == some "text/plain" &&
      a.created == some "2024-01-31 12:05" && a.modified == some "2024"))
    f := f + (← check "tree: decode" (bytesOf d L a == some "hello".toUTF8.toList))
    let some b := es[1]? | check "tree: second" false
    f := f + (← check "tree: chain decodes" (bytesOf d L b == some payload.data.toList))
    f := f + (← check "tree: size from decoded" (b.size.isNone &&
      shownSize b (decode d L b) == some payload.size))
    let some c := es[2]? | check "tree: third" false
    f := f + (← check "tree: external" (c.problem == some .notEmbedded && c.stream.isNone &&
      (decode d L c matches .error _)))
    let some k := es[3]? | check "tree: fourth" false
    f := f + (← check "tree: key name, shared stream" (bytesOf d L k == some "hello".toUTF8.toList))
    let some w := es[4]? | check "tree: fifth" false
    f := f + (← check "tree: hostile name is clean" (w.name.toList.all (!hidden ·)))
    f := f + (← check "tree: hostile decode" (bytesOf d L w == some "abc".toUTF8.toList))
    f := f + (← check "tree: icons" (l.icons.map (fun i => (i.page, i.entry)) == [(0, 0), (0, 4)]))
    f := f + (← check "tree: icon rect normalized" (l.icons.head?.map (fun i =>
      (i.rect.llx.mantissa, i.rect.lly.mantissa, i.rect.urx.mantissa, i.rect.ury.mantissa)) ==
      some (10, 10, 30, 40)))
    f := f + (← check "tree: no warnings" (l.warnings == 0 && !l.truncated))
    f := f + (← check "tree: listed sizes without decoding" (es.map listedSize ==
      [some 5, none, none, some 5, some 3] && es.map (·.filtered) ==
      [false, true, false, false, false]))
    return f)
  f := f + (← withDoc "odd" oddPdf fun d => do
    let l := list d L
    let es := l.entries
    let mut f := 0
    f := f + (← check "odd: entries" (es.map (·.name) ==
      ["bad-ef", "not-stream", "image", "bomb", "plain.txt"]))
    f := f + (← check "odd: problems" (es.map (·.problem) ==
      [some .badEF, some .notAStream, none, none, some .notEmbedded]))
    f := f + (← check "odd: non-filespec counted" (l.warnings == 1))
    let some img := es[2]? | check "odd: image" false
    f := f + (← check "odd: /DL listed" (listedSize img == some 7 && img.stored == some 3))
    f := f + (← check "odd: image filter refused" (decode d L img matches .error (.unsupported _)))
    let some bomb := es[3]? | check "odd: bomb" false
    f := f + (← check "odd: bomb decodes under default limits"
      ((bytesOf d L bomb).map List.length == some 50000))
    let small : SafePdf.Limits := { maxDecodedStreamBytes := 1000 }
    f := f + (← check "odd: bomb is a limit error"
      (decode d small bomb matches .error (.limitExceeded .decodedStreamBytes)))
    f := f + (← check "odd: declared size kept" (shownSize bomb (decode d small bomb) == some 50000))
    f := f + (← check "odd: /DL-less bomb listed by /Params" (listedSize bomb == some 50000))
    f := f + (← check "odd: string /FS icon" (l.icons.map (·.entry) == [4]))
    return f)
  f := f + (← withDoc "cycle" cyclePdf fun d => do
    let l := list d L
    let mut f := 0
    f := f + (← check "cycle: one entry" (l.entries.map (·.name) == ["x.txt"]))
    f := f + (← check "cycle: warned" (l.warnings ≥ 1))
    return f)
  f := f + (← withDoc "many" manyPdf fun d => do
    let l := list d L
    let mut f := 0
    f := f + (← check "many: capped" (l.entries.length == maxAttachments && l.truncated))
    f := f + (← check "many: first" (l.entries.head?.map (·.name) == some "f0"))
    return f)
  f := f + (← withDoc "plain" plainPdf fun d => do
    let l := list d L
    check "plain: none" (l.entries.isEmpty && l.icons.isEmpty && l.warnings == 0))
  -- Names: sanitized and bounded.
  f := f + (← check "long name bounded"
    ((displayText maxNameChars (List.replicate 5000 65)).length == maxNameChars))
  f := f + (← check "size text" (sizeText 0 == "0 B" && sizeText 2048 == "2.0 KB"))
  return f

end SafePdf.Tests.Attachments
