import SafePdf.Core.Crypt.Sha2
import SafePdf.Shell.App.BibLean.Annots

/-!
# `viewer --biblean --self-test`: the reader contract's sequence without a window (task 10.4; Plan.md §6 Phase 10 "Conformance")

A headless run of what bib-lean's reader contract (`bib-lean/docs/READER-CONTRACT.md` §2–§5)
asks of a viewer, so the contract can be checked with `biblean open KEY --reader 'exec
viewer --biblean --self-test'` (`scripts/biblean-contract.sh`) and with our stub server,
without a display. Unverified shell code; it reuses the launch (`Launch.openFromBibLean`),
the annotation conversion (`Annots`), the detection (`Text`) and the Phase 9 writer
(`Save.build`) exactly as the window does.

**The sequence** (`run`):

1. **Launch** (`Launch.openFromBibLean`): the token from file descriptor 3, `BIBLEAN_SERVER`,
   `BIBLEAN_ATTACHMENT`, `BIBLEAN_PAGE` / `--page N`; `GET /api/attachments/{key}/file` into
   `Api.openBytes`, `GET /api/items/{key}` (stored annotations, parent, title).
2. **Two deterministic marks on page 1** (`addSelfTestMarks`): a yellow highlight over the first
   word of page 1 (`Select.wordAt` on the page's glyph cells; on a page without text, the
   fixed box `fallbackQuad` near the CropBox's upper-left corner) and a yellow note with the
   text `noteText` at 20 pt right of and below the CropBox's upper-left corner. The store they
   are added to is the file's own marks merged with the stored set (`Sync.load`, as the window
   does at open). A self-test mark that is **already there** (same page, kind, colour, quads or
   icon box within `Save.tol`, same text) is not added again, so a second run on the file
   the first run stored (bib-lean serves the `PUT` file from then on) creates nothing, posts
   the same ids and keeps bib-lean's item keys (contract §4.2; the contract script's S12).
3. **`POST /api/attachments/{key}/annotations`** with the whole set (`Annots.bodyOf`: our marks
   with `id` = `/NM`, then the elements of other viewers verbatim); the answer must be `200`
   with one key per element.
4. **`POST /api/attachments/{key}/detected`** with the first DOI and arXiv id of pages 1–2
   (`Text.detect`, `Text.detectedBody`), regardless of a parent item (the stock viewer's
   self-test does the same); the answer must be `202`. A PDF without identifiers skips this
   step (`detected: none found`), which is not a failure. Then the full text to `/fulltext`
   (`200` expected).
5. **`PUT /api/attachments/{key}/file`** with the re-saved file: `Save.build` (the incremental
   update of Plan S8/C7, checked by reopening it strictly and reading the marks back) of the
   store's unsaved marks; the answer must be `200`. When every mark is already in the file the
   step is skipped (`put: skipped …`): bib-lean would only store an identical revision.

**Output** (stdout; one `name: value` line per step, then the verdict line
`viewer self-test: ok` or `viewer self-test: FAILED (reason)`): `key`, `pages`, `bytes` and
`sha256` of the served file (so a harness can compare it with the attachment without the
viewer writing the PDF anywhere, contract §2), `page-env` (the parsed `BIBLEAN_PAGE`, or
`unset`), `page-arg` (`--page`, or `none`), `page` (the page the window would open at, or
`none`), `marks`, `annotations` (status, element count, the answered item keys), `detected`,
`fulltext`, `put`. Never the token; library data only as item keys and identifiers.

**Exit codes** (contract §5, as the stock viewer): `0` every step passed, `1` a step failed
(the server refused, an answer was not the expected one, the file did not open or could not be
re-saved), `2` usage error (`Main.lean`; also a bad `BIBLEAN_SERVER`/`BIBLEAN_ATTACHMENT`),
`3` no valid token on file descriptor 3.
-/

namespace SafePdf.Shell.App.BibLean.SelfTest

open SafePdf.Core.Raster.Geom (Pt Box)
open SafePdf.Shell.App.Marks (Mark Color Store Anchor)
open SafePdf.Shell.App.BibLean.Http (JVal)

/-! ## Pure parts -/

/-- The text of the self-test's note. -/
def noteText : String := "safe-pdf self-test note"

/-- The highlight's box on a page without text: 72 pt right of the CropBox's left edge, 72 to
84 pt below its top, 144 pt wide. -/
def fallbackQuad (pb : Box) : Box := ⟨pb.llx + 72, pb.ury - 84, pb.llx + 216, pb.ury - 72⟩

/-- Where the note is anchored: 20 pt right of and below the CropBox's upper-left corner. -/
def noteAnchor (pb : Box) : Pt := ⟨pb.llx + 20, pb.ury - 20⟩

/-- The highlight's quads: the first word of the page (`cells`), else `fallbackQuad`. -/
def highlightQuads (pi : Annots.PageInfo) : List Box :=
  let qs := if pi.cells.isEmpty then []
    else let (a, b) := Select.wordAt pi.cells 0; Select.rangeBoxes pi.cells a b
  if qs.isEmpty then [fallbackQuad pi.box] else qs

/-- Whether `m` is the self-test mark `want` (ids aside): page, kind, colour, text, quads and
note icon box within `Save.tol`. -/
def sameShape (pb : Box) (want m : Mark) : Bool :=
  Save.sameMark pb { want with id := m.id } m

/-- **The two self-test marks** on page 0 (see the module doc), each added to `s` unless the
store already holds it. Returns the store and the number of marks added. -/
def addSelfTestMarks (pi : Annots.PageInfo) (s : Store) : Store × Nat := Id.run do
  let hl : Mark := ⟨0, 0, .yellow, .highlight (highlightQuads pi)⟩
  let note : Mark := ⟨0, 0, .yellow, .note noteText (.point (noteAnchor pi.box))⟩
  let mut s := s
  let mut added := 0
  for want in [hl, note] do
    if s.marks.any (sameShape pi.box want) then continue
    s := (s.add want.page want.color want.kind).1
    added := added + 1
  return (s, added)

private def pb0 : Box := ⟨0, 0, 612, 792⟩
private def cells0 : Array Select.Cell :=
  #[⟨"H", "", ⟨100, 698, 106, 708⟩, 0⟩, ⟨"i", "", ⟨106, 698, 109, 708⟩, 0⟩,
    ⟨"y", " ", ⟨112, 698, 118, 708⟩, 0⟩]

#guard (addSelfTestMarks ⟨pb0, cells0⟩ {}).2 == 2
#guard let (s, _) := addSelfTestMarks ⟨pb0, cells0⟩ {}
  (s.marks.map (·.id)).toList == [1, 2] && (s.marks.map Mark.isNote).toList == [false, true]
-- Idempotent: a second pass (also on the marks read back as saved) adds nothing.
#guard let (s, _) := addSelfTestMarks ⟨pb0, cells0⟩ {}
  (addSelfTestMarks ⟨pb0, cells0⟩ s).2 == 0 &&
    (addSelfTestMarks ⟨pb0, cells0⟩ (Store.load s.marks.toList)).2 == 0
-- Other marks of the store are kept and the new ids come after them.
#guard let s0 := (Store.load [⟨7, 0, .green, .note "mine" (.point ⟨300, 300⟩)⟩])
  let (s, n) := addSelfTestMarks ⟨pb0, cells0⟩ s0
  n == 2 && (s.marks.map (·.id)).toList == [7, 8, 9]
-- No text: the fallback box.
#guard highlightQuads ⟨pb0, #[]⟩ == [⟨72, 708, 216, 720⟩]

/-- Lowercase hex of `b`. -/
def hexOf (b : ByteArray) : String :=
  String.join (b.toList.map fun x =>
    let d (n : Nat) : Char := "0123456789abcdef".toList.getD n '0'
    String.ofList [d (x.toNat / 16), d (x.toNat % 16)])

#guard hexOf (SafePdf.Core.Crypt.Sha2.sha256 "abc".toUTF8) ==
  "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"

/-- The item keys of a `POST …/annotations` answer (`{"version", "keys": [...]}`); `none` when
the answer has no such list of strings. -/
def keysOf? (body : ByteArray) : Option (Array String) := do
  match ← (← Launch.parseJson? body).get? "keys" with
  | .arr xs => xs.mapM JVal.str?
  | _ => none

#guard keysOf? "{\"version\":4,\"keys\":[\"AB2345CD\",\"EF6789GH\"]}".toUTF8 ==
  some #["AB2345CD", "EF6789GH"]
#guard keysOf? "{\"keys\":[1]}".toUTF8 == none

/-- Number of elements of a JSON array text (`0` for anything else). -/
def arrayLength (s : String) : Nat :=
  match Http.parseJson s.toUTF8 with
  | .ok (.arr xs) => xs.size
  | _ => 0

/-- The `identifiers` object of a `POST …/detected` answer, as compact JSON (`?` if absent). -/
def identifiersOf (body : ByteArray) : String :=
  ((Launch.parseJson? body).bind (·.get? "identifiers")).map Annots.jtext |>.getD "?"

#guard identifiersOf "{\"pending\":true,\"identifiers\":{\"doi\":\"10.1/x\"}}".toUTF8 ==
  "{\"doi\":\"10.1/x\"}"

/-! ## The run (IO) -/

/-- One request on the session's server; `(status, body)` or the exchange's error (method,
path and port only). -/
def request (s : Launch.Session) (method route : String) (body : Option (ByteArray × String))
    (lim : Http.Limits) : IO (Except String (Nat × ByteArray)) := do
  try
    let r ← Http.exchange s.origin s.token method s!"/api/attachments/{s.key}/{route}" body lim
    return .ok (r.status, r.body)
  catch e => return .error s!"{e}"

/-- `HTTP n` with the error body's code, if any. -/
def statusText (status : Nat) (body : ByteArray) : String :=
  s!"HTTP {status}" ++ ((Launch.errorCode? body).map (s!" ({·})") |>.getD "")

/-- **`viewer --biblean --self-test`** (see the module documentation): prints the step lines
and the verdict; returns the exit code. `argPage` is a `--page` argument. -/
def run (argPage : Option Nat) : IO UInt32 := do
  let o ← match ← Launch.openFromBibLean (argPage := argPage) with
    | .error f =>
      IO.eprintln s!"viewer --biblean: {f.message}"
      IO.println s!"viewer self-test: FAILED ({f.message})"
      return f.exitCode
    | .ok o => pure o
  let fmt (x : Option Nat) : String := (x.map toString).getD "none"
  let envPage ← IO.getEnv "BIBLEAN_PAGE"
  IO.println s!"key: {o.session.key}\npages: {o.document.pageCount}\nbytes: {o.bytes.size}\n\
    sha256: {hexOf (SafePdf.Core.Crypt.Sha2.sha256 o.bytes)}\n\
    page-env: {if envPage.isNone then "unset" else fmt (Launch.pageOf? envPage)}\n\
    page-arg: {fmt argPage}\npage: {fmt o.page}"
  let failures ← IO.mkRef (#[] : Array String)
  let failed (step msg : String) : IO Unit := do
    IO.println s!"{step}: {msg}"
    failures.modify (·.push step)
  let d := o.document
  if d.pageCount == 0 then
    IO.println "viewer self-test: FAILED (the document has no pages)"
    return 1
  -- 2. The marks.
  let y ← Annots.Sync.create o
  let s0 ← y.load (Store.load (Save.readMarks d.doc d.limits))
  let pi ← y.pageInfo 0
  let (s, added) := addSelfTestMarks pi s0
  IO.println s!"marks: {added} added, {s.marks.size} in all, {s.unsaved.length} not yet in the file"
  -- 3. The annotation set.
  let mut infos : Array Annots.PageInfo := #[]
  for i in [0:d.pageCount] do
    let pi ← if s.marks.any (·.page == i) then y.pageInfo i else pure default
    infos := infos.push pi
  let body := Annots.bodyOf (fun i => infos.getD i default) s (← y.state.get).passthrough
  let n := arrayLength body
  match ← request o.session "POST" "annotations" (some (body.toUTF8, "application/json"))
      Launch.jsonLimits with
  | .error e => failed "annotations" e
  | .ok (st, ans) =>
    match keysOf? ans with
    | some ks =>
      if st == 200 && ks.size == n then
        IO.println s!"annotations: HTTP 200, {n} elements, keys {",".intercalate ks.toList}"
      else failed "annotations" s!"{statusText st ans}, {n} elements, {ks.size} keys"
    | none => failed "annotations" s!"{statusText st ans}, no keys in the answer"
  -- 4. Detection (pages 1–2) and the full text.
  let mut pages : Array String := #[]
  for i in [0:min d.pageCount BibLean.Text.maxFulltextPages] do
    pages := pages.push (BibLean.Text.pageTextOf d i)
  match BibLean.Text.detectedBody (BibLean.Text.detect pages.toList) with
  | none => IO.println "detected: none found"
  | some db =>
    match ← request o.session "POST" "detected" (some (db.toUTF8, "application/json"))
        Launch.postLimits with
    | .error e => failed "detected" e
    | .ok (st, ans) =>
      if st == 202 then IO.println s!"detected: HTTP 202 {db} -> {identifiersOf ans}"
      else failed "detected" (statusText st ans)
  let (ft, np) := BibLean.Text.fulltextBody pages
  match ← request o.session "POST" "fulltext" (some (ft, "text/plain; charset=utf-8"))
      Launch.postLimits with
  | .error e => failed "fulltext" e
  | .ok (st, ans) =>
    if st == 200 then IO.println s!"fulltext: HTTP 200 ({np} pages, {ft.size} bytes)"
    else failed "fulltext" (statusText st ans)
  -- 5. The re-saved file.
  if s.unsaved.isEmpty then
    IO.println "put: skipped (every mark is already in the file)"
  else
    match Save.build d.limits d.doc s (← Save.nowDate) with
    | .error e => failed "put" s!"cannot re-save: {e}"
    | .ok (bytes, got) =>
      if bytes.size > Annots.maxPutBytes then
        failed "put" s!"{bytes.size} bytes is more than 64 MiB"
      else
        match ← request o.session "PUT" "file" (some (bytes, "application/pdf")) Annots.putLimits with
        | .error e => failed "put" e
        | .ok (st, ans) =>
          if st == 200 then
            IO.println s!"put: HTTP 200 ({bytes.size} bytes, {bytes.size - o.bytes.size} appended, \
              {got.length} marks in the file)"
          else failed "put" (statusText st ans)
  let fs ← failures.get
  if fs.isEmpty then
    IO.println "viewer self-test: ok"
    return 0
  IO.println s!"viewer self-test: FAILED ({", ".intercalate fs.toList})"
  return 1

end SafePdf.Shell.App.BibLean.SelfTest
