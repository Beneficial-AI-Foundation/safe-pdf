import SafePdf.Api
import SafePdf.Shell.Worker.Client
import SafePdf.Shell.Worker.Serve
import Tests.OptionalContent

/-!
# Document worker, end to end (tasks 12.2a, 12.2d)

Plan.md §6 Phase 12, "Restricted, stoppable document worker". Spawns the real `worker`
executable (`.lake/build/bin/worker`, a default build target) through
`SafePdf.Shell.Worker.Client` and checks:

* **End to end**: open `Tests/golden/text/latin.pdf` from its bytes; page count; page info;
  render page 1 and compare with the in-process render (`Core.Raster.Glyph.renderDocPage`
  with the same substitute fonts, `Worker.workerFonts`) **byte for byte**; the text of page 1
  equals the in-process `Core.Text.extractDocPage` (and the glyph count, and
  `Api.pageText` with annotations); outline and links of `Tests/golden/pages/outline.pdf`
  equal `Api.outline`; strict mode refuses a file that needs repair; requests before any
  open get `noDocument`; a bad page index and a bad rotation get `pageFailed`.
* **Malformed frames** (tag 0, unknown tag, truncated field, trailing byte, zero
  denominator): each gets an `error .malformed` response and the worker keeps serving.
* **Oversized message**: a header above `requestCap` gets `error .tooLong` before any payload
  byte is sent, and the worker exits; a request above the cap is refused by the client
  without sending (`notEncodable`).
* **Kill mid-render**: a render at zoom 8 with a 20 ms timeout is killed (`timeout`), the
  process is gone, and a fresh worker opens and renders the next file.
* **Overhead**: page 1 at zoom 1 rendered 5 times in-process and through the worker (the
  worker's time includes the frame copy and pipe transfer); printed, not asserted.
* **Task 12.2d, the viewer's text and links**: for every page (at most 6) of eight golden files
  and of the optional-content fixture under three layers states, the worker's `pageIndex`
  answer equals the viewer's in-process index (`Select.PageIndex.ofText` of
  `Annot.extractDocPageAnnots`) cell for cell — text, separator, box, line, line directions,
  hidden flags — and the index the viewer rebuilds from it has the same text (byte for byte)
  and search text; `viewLinks` equals `Links.pageLinks`. Layered renders equal the in-process
  render under the same state, and differ between states; hidden text follows the state.
* **Startup flags**: `--no-subst` renders as in process without substitute fonts; a font search
  naming missing directories renders as the default; `--limits` reaches the worker; an unknown
  flag ends the worker with status 5.
* **Task 12.3, resource fences** (`--mem-limit-mib=`, `--cpu-limit-s=`, `Sandbox.fence`): a
  worker with a 64 MiB ceiling asked for a ~124 MB render is ended (the watchdog: status 6;
  on Linux possibly an allocation failure under the rlimit backstop) instead of answering, while one with the
  viewer's ceiling renders the same page; a worker with a 1 s CPU fence that busy-loops 4 s
  before a render (`--test-spin-ms`) is ended by `SIGXCPU` before the loop ends, while four
  requests of 0.6 s each (2.4 s in all) are answered: the fence is per request. Task 12.c1:
  the 64 MiB case, and every fence check that fails, is run once more with the worker's
  stderr piped (`diagnose`) and its lines printed (`worker stderr: …`): the fences installed
  and the step that ended it.
-/

namespace SafePdf.Tests.Worker

open SafePdf SafePdf.Core
open SafePdf.Shell.Worker
open SafePdf.Shell.Worker.Protocol (Request Response ErrorKind)

/-- Reports a failed check; 1 on failure. -/
def check (what : String) (ok : Bool) : IO Nat := do
  if ok then return 0
  IO.println s!"  FAIL worker: {what}"
  return 1

/-- The worker executable (absolute: the worker runs with `/` as working directory). -/
def workerExe : IO (Option System.FilePath) := do
  let p : System.FilePath := ".lake/build/bin/worker"
  if ← p.pathExists then return some (← IO.FS.realPath p) else return none

/-- A short description of a response, for failure messages. -/
def describe : Except ClientError Response → String
  | .error e => s!"client error {e}"
  | .ok (.error k m) => s!"error {reprStr k}: {m}"
  | .ok (.docInfo n r e) => s!"docInfo {n} {r} {e}"
  | .ok (.image w h d) => s!"image {w}x{h} ({d.size} bytes)"
  | .ok (.text s gs) => s!"text {s.length} chars, {gs.length} glyphs"
  | .ok _ => "other response"

/-- `true` iff the response is an error of kind `k`. -/
def isErr (k : ErrorKind) : Except ClientError Response → Bool
  | .ok (.error k' _) => k' == k
  | _ => false

/-- `true` iff the response is `docInfo` with `n` pages. -/
def isDoc (n : Nat) : Except ClientError Response → Bool
  | .ok (.docInfo n' _ _) => n' == n
  | _ => false

/-- Milliseconds since an arbitrary origin. -/
def nowMs : IO Nat := IO.monoMsNow

/-- A PDF that opens only through the repair path (no xref table). -/
def needsRepair : ByteArray :=
  ("%PDF-1.4\n1 0 obj\n<< /Type /Catalog /Pages 2 0 R >>\nendobj\n" ++
    "2 0 obj\n<< /Type /Pages /Kids [] /Count 0 >>\nendobj\ntrailer\n<< /Root 1 0 R >>\n%%EOF\n").toUTF8

/-- End-to-end checks against the in-process API. -/
def endToEnd (exe : System.FilePath) : IO Nat := do
  let mut f := 0
  let bytes ← IO.FS.readBinFile "Tests/golden/text/latin.pdf"
  let limits := Limits.default
  let c ← spawn exe
  -- Before any open.
  f := f + (← check "info before open is noDocument" (isErr .noDocument (← c.request .info)))
  -- Open from bytes.
  let some d := (Api.openBytes bytes).toOption | check "latin.pdf opens in process" false
  let r ← c.request (.openDoc bytes true)
  f := f + (← check s!"openDoc → docInfo {d.pageCount} ({describe r})" (isDoc d.pageCount r))
  f := f + (← check "info → docInfo" (isDoc d.pageCount (← c.request .info)))
  -- Page info.
  match ← c.request (.pageInfo 0), Api.pageInfo d 0 with
  | .ok (.pageInfo lbl w h rot), .ok pi =>
    f := f + (← check "pageInfo matches Api.pageInfo"
      (lbl == pi.label && w == pi.size.1 && h == pi.size.2 && rot == rotationToNat pi.rotation))
  | r, _ => f := f + (← check s!"pageInfo ({describe r})" false)
  -- Render page 1, byte for byte against the in-process render.
  let subst ← workerFonts limits
  let some page := d.doc.pages[0]? | check "page 0 exists" false
  let local_ := (Raster.Glyph.renderDocPage limits d.doc page (3 / 2) .r0
    (Filter.Budget.init limits) (subst := subst)).1
  match ← c.request (.render 0 (3 / 2) 0 none), local_ with
  | .ok (.image w h data), .ok img =>
    f := f + (← check s!"render size {w}x{h} vs {img.w}x{img.h}" (w == img.w && h == img.h))
    f := f + (← check "render bytes equal the in-process render" (data == img.data))
    -- Without substitute fonts (e.g. CI without fonts-urw-base35 in the worker's font
    -- directories) the page's non-embedded text paints nothing on both paths.
    if subst.faces.isEmpty then
      IO.println "  worker: no substitute fonts found; ink check skipped (renders still byte-equal)"
    else
      f := f + (← check "render has ink" (data.toList.any (· < 128)))
  | r, _ => f := f + (← check s!"render ({describe r})" false)
  -- Rotated render too.
  let localR := (Raster.Glyph.renderDocPage limits d.doc page 1 .r90
    (Filter.Budget.init limits) (subst := subst)).1
  match ← c.request (.render 0 1 1 none), localR with
  | .ok (.image w h data), .ok img =>
    f := f + (← check "rotated render equals the in-process render"
      (w == img.w && h == img.h && data == img.data))
  | r, _ => f := f + (← check s!"rotated render ({describe r})" false)
  -- Text of page 1 against Core.Text.extractDocPage.
  let localT := (Text.extractDocPage limits d.doc page (Filter.Budget.init limits)).1
  match ← c.request (.text 0 false), localT with
  | .ok (.text s gs), .ok pt =>
    f := f + (← check s!"text equals extractDocPage ({s.length} chars)" (s == pt.text && !s.isEmpty))
    f := f + (← check "glyph count equals extractDocPage" (gs.length == pt.glyphs.length))
    let firstOk := match gs.head?, (Api.pageText d 0 { withAnnots := false }).toOption with
      | some g, some t => t.glyphs[0]?.map (fun a => a.origin == g.origin && a.box == g.box &&
          a.text == g.text) == some true
      | _, _ => false
    f := f + (← check "first glyph equals Api.pageText's" firstOk)
  | r, _ => f := f + (← check s!"text ({describe r})" false)
  match ← c.request (.text 0 true), Api.pageText d 0 with
  | .ok (.text s _), .ok t => f := f + (← check "text with annotations equals Api.pageText" (s == t.text))
  | r, _ => f := f + (← check s!"text with annotations ({describe r})" false)
  -- Bad page, bad rotation, bad zoom.
  f := f + (← check "page out of range is pageFailed" (isErr .pageFailed (← c.request (.render 99 1 0 none))))
  f := f + (← check "rotation 4 is pageFailed" (isErr .pageFailed (← c.request (.render 0 1 4 none))))
  f := f + (← check "zoom 0 is pageFailed" (isErr .pageFailed (← c.request (.render 0 0 0 none))))
  f := f + (← check "zoom -1 is pageFailed" (isErr .pageFailed (← c.request (.render 0 (-1) 0 none))))
  -- Outline and links of another document, in the same worker.
  let ob ← IO.FS.readBinFile "Tests/golden/pages/outline.pdf"
  let some od := (Api.openBytes ob).toOption | check "outline.pdf opens in process" false
  f := f + (← check "second openDoc replaces the document" (isDoc od.pageCount (← c.request (.openDoc ob true))))
  match ← c.request .outline with
  | .ok (.outline items) =>
    let expect := Api.outline od
    f := f + (← check s!"outline has {expect.length} items" (items.length == expect.length && !items.isEmpty))
    f := f + (← check "outline titles and depths equal Api.outline"
      (items.map (fun i => (i.title, i.depth)) == expect.map (fun i => (i.title, i.depth))))
    f := f + (← check "outline targets equal Api.outline"
      (items.map (·.target) == expect.map (fun i => Serve.target i.target)))
  | r => f := f + (← check s!"outline ({describe r})" false)
  match ← c.request (.links 0), Api.pageLinks od 0 with
  | .ok (.links ls), .ok expect =>
    f := f + (← check "links equal Api.pageLinks"
      (ls == expect.map fun l => { rect := l.rect, target := Serve.target l.target }))
  | r, _ => f := f + (← check s!"links ({describe r})" false)
  -- Strict mode.
  f := f + (← check "strict open of a damaged file is openFailed"
    (isErr .openFailed (← c.request (.openDoc needsRepair false))))
  f := f + (← check "after a failed open there is no document" (isErr .noDocument (← c.request .info)))
  match ← c.request (.openDoc needsRepair true) with
  | .ok (.docInfo 0 true _) => pure ()
  | r => f := f + (← check s!"lenient open of a damaged file is repaired ({describe r})" false)
  -- Quit.
  match ← c.request .quit (some 5000) with
  | .ok .bye => pure ()
  | r => f := f + (← check s!"quit → bye ({describe r})" false)
  let code ← c.waitExit
  f := f + (← check s!"worker exits 0 after quit (got {code})" (code == some 0))
  return f

/-- Malformed and oversized frames. -/
def malformed (exe : System.FilePath) : IO Nat := do
  let mut f := 0
  let c ← spawn exe
  let payloads : List (String × ByteArray) :=
    [("tag 0", ⟨#[0]⟩), ("unknown tag", ⟨#[200]⟩), ("truncated field", ⟨#[3]⟩),
     ("trailing byte", ⟨#[2, 0]⟩), ("zero denominator", ⟨#[4, 0, 2, 0]⟩),
     ("empty payload", .empty), ("over-long number", ⟨#[3] ++ (List.replicate 30 (0x80 : UInt8)).toArray⟩)]
  for (what, p) in payloads do
    discard <| c.sendRaw (Protocol.header p.size ++ p)
    let r ← c.awaitResponse (some 5000)
    f := f + (← check s!"{what} → malformed ({describe r})" (isErr .malformed r))
  -- Still serving.
  f := f + (← check "still serving after malformed frames" (isErr .noDocument (← c.request .info (some 5000))))
  -- A request above the cap is refused by the client, nothing sent.
  let tiny : Limits := { maxInputBytes := 10 }
  let c' : Client := { c with limits := tiny }
  match ← c'.request (.openDoc (ByteArray.mk (Array.replicate 100 0)) true) with
  | .error .notEncodable => pure ()
  | r => f := f + (← check s!"client refuses a request above requestCap ({describe r})" false)
  f := f + (← check "still serving after a refused request" (isErr .noDocument (← c.request .info (some 5000))))
  -- An oversized header: tooLong, then the worker exits (status 2).
  discard <| c.sendRaw (Protocol.header (2 ^ 32 - 1))
  let r ← c.awaitResponse (some 5000)
  f := f + (← check s!"oversized header → tooLong ({describe r})" (isErr .tooLong r))
  let code ← c.waitExit
  f := f + (← check s!"worker exits 2 after an oversized header (got {code})" (code == some 2))
  -- The protocol's own cap check, without a process.
  f := f + (← check "requestCap fits a 4-byte header" (Protocol.requestCap {} < 2 ^ 32))
  return f

/-- Kill mid-render, then a fresh worker works. -/
def killAndRestart (exe : System.FilePath) : IO Nat := do
  let mut f := 0
  let bytes ← IO.FS.readBinFile "Tests/golden/text/latin.pdf"
  let c ← spawn exe
  f := f + (← check "open before kill" (isDoc 1 (← c.request (.openDoc bytes true) (some 10000))))
  let t0 ← nowMs
  let r ← c.request (.render 0 8 0 none) (some 20)
  let t1 ← nowMs
  f := f + (← check s!"render at zoom 8 times out after 20 ms ({describe r})"
    (match r with | .error .timeout => true | _ => false))
  f := f + (← check s!"timeout returns promptly ({t1 - t0} ms)" (t1 - t0 < 2000))
  let st ← c.exited?
  f := f + (← check s!"killed worker is gone ({st})" st.isSome)
  -- The next file, in a fresh worker.
  let ob ← IO.FS.readBinFile "Tests/golden/pages/outline.pdf"
  let c2 ← spawn exe
  match ← c2.request (.openDoc ob true) (some 10000) with
  | .ok (.docInfo n _ _) =>
    f := f + (← check "a fresh worker opens the next file" (n > 0))
    match ← c2.request (.render 0 1 0 none) (some 10000) with
    | .ok (.image w h d) => f := f + (← check "a fresh worker renders" (d.size == 4 * w * h && w > 0))
    | r => f := f + (← check s!"fresh render ({describe r})" false)
  | r => f := f + (← check s!"fresh open ({describe r})" false)
  c2.close
  return f

/-- Rendering overhead of the worker against in-process rendering (printed). -/
def overhead (exe : System.FilePath) : IO Nat := do
  let bytes ← IO.FS.readBinFile "Tests/golden/text/latin.pdf"
  let limits := Limits.default
  let some d := (Api.openBytes bytes).toOption | check "overhead: open" false
  let some page := d.doc.pages[0]? | check "overhead: page" false
  let subst ← workerFonts limits
  let n := 5
  let t0 ← IO.monoNanosNow
  let mut sz := 0
  for _ in [0:n] do
    match (Raster.Glyph.renderDocPage limits d.doc page 1 .r0 (Filter.Budget.init limits)
        (subst := subst)).1 with
    | .ok img => sz := sz + img.data.size
    | .error _ => pure ()
  let t1 ← IO.monoNanosNow
  let s0 ← IO.monoNanosNow
  let c ← spawn exe
  discard <| c.request (.openDoc bytes true)
  let s1 ← IO.monoNanosNow
  let mut wsz := 0
  for _ in [0:n] do
    match ← c.request (.render 0 1 0 none) with
    | .ok (.image _ _ data) => wsz := wsz + data.size
    | _ => pure ()
  let t2 ← IO.monoNanosNow
  c.close
  let ms (a b : Nat) : String := s!"{(b - a) / 100000 / 10}.{(b - a) / 100000 % 10}"
  IO.println s!"  worker overhead: {n} renders of page 1 at zoom 1 ({sz / n} bytes each): \
    in-process {ms t0 t1} ms, worker {ms s1 t2} ms; spawn + open {ms s0 s1} ms"
  check "overhead: same image sizes" (sz == wsz)

/-! ## Task 12.2d: the viewer's text index, links, layered renders, startup flags -/

/-- The viewer's in-process text index of a page (`App.Viewer.pageIndex` without a worker):
`Select.PageIndex.ofText` of `Annot.extractDocPageAnnots` under `oc`. -/
def localIndex (limits : Limits) (d : Api.Document) (page : Doc.Page)
    (oc : Option Doc.OptionalContent.State) : Except String Shell.App.Select.PageIndex :=
  match (Annot.extractDocPageAnnots limits d.doc page (Filter.Budget.init limits) (oc := oc)).1 with
  | .ok pt => .ok (Shell.App.Select.PageIndex.ofText pt)
  | .error e => .error (Shell.renderError e)

/-- Whether the worker's `pageIndex` answer is the in-process index, field for field, and the
index rebuilt from it (as the viewer does) has the same text and normalised search text. -/
def sameIndex (ix : Shell.App.Select.PageIndex) (cs : List Protocol.Cell) (ds : List Nat)
    (hs : List Bool) : Bool :=
  let cells := (cs.map fun c =>
    ({ text := c.text, sep := c.sep, box := c.box, line := c.line } : Shell.App.Select.Cell)).toArray
  ix.cells.toList.map (fun c => (c.text, c.sep, c.box, c.line)) ==
      cs.map (fun c => (c.text, c.sep, c.box, c.line)) &&
    ix.lineDirs.toList == ds && ix.hidden.toList == hs &&
    (Shell.App.Select.fullText cells).toUTF8 == (Shell.App.Select.fullText ix.cells).toUTF8 &&
    Shell.App.Select.normChars cells == ix.hay

/-- The text index and the links of every page (at most 6) of `bytes` through the worker `c`
against the in-process ones, under `oc`. Returns failures and the number of non-empty
indexes. -/
def compareDoc (c : Client) (name : String) (bytes : ByteArray)
    (oc : Option Doc.OptionalContent.State := none) : IO (Nat × Nat) := do
  let limits := Limits.default
  let some d := (Api.openBytes bytes).toOption
    | return (← check s!"{name} opens in process" false, 0)
  let mut f := 0
  let mut nonEmpty := 0
  f := f + (← check s!"{name}: openDoc" (isDoc d.pageCount (← c.request (.openDoc bytes true))))
  for i in [0:min d.pageCount 6] do
    let some page := d.doc.pages[i]? | continue
    match ← c.request (.pageIndex i oc), localIndex limits d page oc with
    | .ok (.pageIndex cs ds hs), .ok ix =>
      if !cs.isEmpty then nonEmpty := nonEmpty + 1
      f := f + (← check s!"{name} p{i + 1}: text index equals the in-process index \
        ({cs.length} cells)" (sameIndex ix cs ds hs))
    | .ok (.error _ m), .error m' =>
      f := f + (← check s!"{name} p{i + 1}: same text error ({m} / {m'})" (m == m'))
    | r, _ => f := f + (← check s!"{name} p{i + 1}: pageIndex ({describe r})" false)
    let expect := (Shell.App.Links.pageLinks d.doc limits i).toList.map fun l =>
      ({ box := l.box, action := Serve.action l.action } : Protocol.ViewLink)
    match ← c.request (.viewLinks i) with
    | .ok (.viewLinks ls) =>
      f := f + (← check s!"{name} p{i + 1}: links equal Links.pageLinks ({ls.length})" (ls == expect))
    | r => f := f + (← check s!"{name} p{i + 1}: viewLinks ({describe r})" false)
  return (f, nonEmpty)

/-- Text index and links on golden files, a layered page (render and text under three layers
states), and the timings of a text request. -/
def textLinksLayers (exe : System.FilePath) : IO Nat := do
  let mut f := 0
  let limits := Limits.default
  let c ← spawn exe
  let files := ["Tests/golden/text/latin.pdf", "Tests/golden/text/offpage.pdf",
    "Tests/golden/text/lineseps.pdf", "Tests/golden/text/actualtext.pdf",
    "Tests/golden/text/unicode.pdf", "Tests/golden/pages/outline.pdf",
    "Tests/golden/pages/tree.pdf", "Tests/golden/svg/shapes.pdf"]
  let mut nonEmpty := 0
  let mut links := 0
  for file in files do
    let bytes ← IO.FS.readBinFile file
    let (g, n) ← compareDoc c file bytes
    f := f + g
    nonEmpty := nonEmpty + n
    if let some d := (Api.openBytes bytes).toOption then
      links := links + (List.range (min d.pageCount 6)).foldl
        (fun a i => a + (Shell.App.Links.pageLinks d.doc limits i).size) 0
  f := f + (← check s!"some golden pages have text ({nonEmpty})" (nonEmpty ≥ 5))
  f := f + (← check s!"some golden pages have links ({links})" (links ≥ 1))
  -- The layers fixture of the optional-content suite, under the document's default (group 6
  -- OFF), every group ON and group 5 OFF.
  let ocBytes := OptionalContent.fixture
    "<< /OCGs [5 0 R 6 0 R] /D << /Name (Default) /OFF [6 0 R] >> >>"
  let allOn : Doc.OptionalContent.State := { known := [(5, 0), (6, 0)], off := [] }
  let fiveOff : Doc.OptionalContent.State := { known := [(5, 0), (6, 0)], off := [(5, 0)] }
  let states : List (Option Doc.OptionalContent.State) := [none, some allOn, some fiveOff]
  for oc in states do
    let (g, _) ← compareDoc c s!"layers {reprStr oc}" ocBytes oc
    f := f + g
  let some od := (Api.openBytes ocBytes).toOption
    | return f + (← check "layers fixture opens" false)
  let some page := od.doc.pages[0]? | return f + (← check "layers page" false)
  discard <| c.request (.openDoc ocBytes true)
  let subst ← workerFonts limits
  let mut imgs : List ByteArray := []
  for oc in states do
    let here := (Raster.Glyph.renderDocPage limits od.doc page 1 .r0 (Filter.Budget.init limits)
      (subst := subst) (oc := oc)).1
    match ← c.request (.render 0 1 0 oc), here with
    | .ok (.image w h data), .ok img =>
      f := f + (← check s!"layered render {reprStr oc} equals the in-process render"
        (w == img.w && h == img.h && data == img.data))
      imgs := imgs ++ [data]
    | r, _ => f := f + (← check s!"layered render {reprStr oc} ({describe r})" false)
  f := f + (← check "the layers states render differently"
    (match imgs with | [a, b, c'] => a != b && b != c' | _ => false))
  -- Hidden text follows the layers state.
  let has (cs : List Protocol.Cell) : Bool :=
    ((String.join (cs.map (·.text))).splitOn "HIDDENTEXT").length > 1
  match ← c.request (.pageIndex 0 none), ← c.request (.pageIndex 0 (some allOn)) with
  | .ok (.pageIndex a _ _), .ok (.pageIndex b _ _) =>
    f := f + (← check "text hidden by the default layers state is not in the index, \
      and is with every group ON" (!has a && has b))
  | _, _ => f := f + (← check "layers text requests" false)
  -- A page out of range.
  f := f + (← check "pageIndex of a page out of range is pageFailed"
    (isErr .pageFailed (← c.request (.pageIndex 99 none))))
  f := f + (← check "viewLinks of a page out of range is pageFailed"
    (isErr .pageFailed (← c.request (.viewLinks 99))))
  -- Timing: the text index of latin.pdf page 1, in process and through the worker.
  let bytes ← IO.FS.readBinFile "Tests/golden/text/latin.pdf"
  let some d := (Api.openBytes bytes).toOption | return f
  let some p0 := d.doc.pages[0]? | return f
  discard <| c.request (.openDoc bytes true)
  let n := 5
  let t0 ← IO.monoNanosNow
  let mut k := 0
  for _ in [0:n] do
    match localIndex limits d p0 none with
    | .ok ix => k := k + ix.cells.size
    | .error _ => pure ()
  let t1 ← IO.monoNanosNow
  for _ in [0:n] do
    match ← c.request (.pageIndex 0 none) with
    | .ok (.pageIndex cs _ _) => k := k + cs.length
    | _ => pure ()
  let t2 ← IO.monoNanosNow
  let ms (a b : Nat) : String := s!"{(b - a) / 100000 / 10}.{(b - a) / 100000 % 10}"
  IO.println s!"  worker text index: {n} × latin.pdf page 1 ({k / (2 * n)} cells): \
    in-process {ms t0 t1} ms, worker {ms t1 t2} ms"
  c.close
  return f

/-- Startup flags: `--no-subst` renders as in process without substitute fonts; a font search
naming missing directories renders as the default; `--limits` reaches the worker; an unknown
flag ends the worker (status 5) before it reads anything. -/
def startupFlags (exe : System.FilePath) : IO Nat := do
  let mut f := 0
  let limits := Limits.default
  let bytes ← IO.FS.readBinFile "Tests/golden/text/latin.pdf"
  let some d := (Api.openBytes bytes).toOption | return (← check "latin opens" false)
  let some page := d.doc.pages[0]? | return (← check "latin page" false)
  let renderWith (subst : Raster.Subst.SubstFonts) :=
    (Raster.Glyph.renderDocPage limits d.doc page 1 .r0 (Filter.Budget.init limits)
      (subst := subst)).1
  let subst ← workerFonts limits
  let noFaces ← workerFaces { noSubst := true }
  f := f + (← check "workerFaces with noSubst is empty" noFaces.isEmpty)
  let cases : List (String × Protocol.StartConfig × Raster.Subst.SubstFonts) :=
    [("--no-subst", { noSubst := true }, {}),
     ("--home/--font-dir of missing directories",
       { home := some "/nonexistent-safepdf-home", fontDirs := ["/nonexistent-safepdf-fonts"] },
       subst)]
  for (what, start, sf) in cases do
    let c ← spawn exe limits #[] start
    discard <| c.request (.openDoc bytes true) (some 10000)
    match ← c.request (.render 0 1 0 none) (some 20000), renderWith sf with
    | .ok (.image w h data), .ok img =>
      f := f + (← check s!"worker started with {what} renders as in process"
        (w == img.w && h == img.h && data == img.data))
      if what == "--no-subst" && !subst.faces.isEmpty then
        match renderWith subst with
        | .ok img2 => f := f + (← check "--no-subst changes the render (substitutes found here)"
            (img2.data != data))
        | .error _ => pure ()
    | r, _ => f := f + (← check s!"render with {what} ({describe r})" false)
    c.close
  -- A changed limit reaches the worker: a page side cap of 10 pixels bounds a zoom-1 render
  -- of the 612 × 792 page.
  let c ← spawn exe { maxPageSide := 10 }
  discard <| c.request (.openDoc bytes true) (some 10000)
  let r ← c.request (.render 0 1 0 none) (some 20000)
  f := f + (← check s!"--limits reaches the worker ({describe r})"
    (match r with | .ok (.image w h _) => w ≤ 10 && h ≤ 10 | .ok (.error ..) => true | _ => false))
  c.close
  -- An unknown flag.
  let child ← IO.Process.spawn
    { toStdioConfig := workerStdio, cmd := exe.toString, args := #["--bogus"], cwd := some "/",
      env := #[], inheritEnv := false }
  let cb : Client := { child, limits, status := ← IO.mkRef none }
  let code ← cb.waitExit
  f := f + (← check s!"an unknown flag ends the worker with status 5 (got {code})" (code == some 5))
  return f

/-- Read a stream to its end, discarding the bytes (a render's pixels are not UTF-8). -/
def drain (s : IO.FS.Handle) : IO Unit := do
  repeat
    if (← s.read 65536).isEmpty then break

/-- Task 12.c1 diagnostics for a failed fence check: run the worker again with `start`, send
`reqs` and close its stdin, with **stderr piped** (the client discards it), wait up to
`timeoutMs` (then kill), and print its exit status and every stderr line: its confinement and
fences, or the one line of the step that failed (startup, watchdog, `SIGXCPU`, `SIGABRT`). -/
def diagnose (exe : System.FilePath) (start : Protocol.StartConfig) (reqs : List Request)
    (timeoutMs : Nat := 30000) : IO Unit := do
  let child ← IO.Process.spawn
    { stdin := .piped, stdout := .piped, stderr := .piped, cmd := exe.toString,
      args := start.toArgs, cwd := some "/", env := #[], inheritEnv := false }
  let err ← IO.asTask child.stderr.readToEnd .dedicated
  let out ← IO.asTask (drain child.stdout) .dedicated
  let (stdin, child) ← child.takeStdin
  for r in reqs do
    if let some f := Protocol.frameRequest {} r then
      try stdin.write f; stdin.flush catch _ => pure ()
  let deadline := (← nowMs) + timeoutMs
  let mut code := none
  repeat
    if let some s ← (try child.tryWait catch _ => pure none) then
      code := some s
      break
    if (← nowMs) ≥ deadline then
      try child.kill catch _ => pure ()
      code := ← (try some <$> child.wait catch _ => pure none)
      break
    IO.sleep 5
  discard <| IO.wait out
  let err := match ← IO.wait err with | .ok s => s | .error e => s!"(stderr: {e})"
  IO.println s!"    diagnose {start.toArgs.toList.drop 1}: exit {code}"
  for l in err.splitOn "\n" do
    if !l.isEmpty then IO.println s!"    worker stderr: {l}"

/-- Task 12.3: the worker's memory and CPU fences (see the module doc). -/
def fences (exe : System.FilePath) : IO Nat := do
  let mut f := 0
  let bytes ← IO.FS.readBinFile "Tests/golden/text/latin.pdf"
  -- Memory: page 1 (612 × 792) at zoom 8 is 4896 × 6336 pixels, 124 MB of RGBA.
  let small : Protocol.StartConfig := { noSubst := true, memLimitMiB := 64 }
  let c ← spawn exe (start := small)
  let r0 ← c.request (.openDoc bytes true) (some 10000)
  f := f + (← check s!"a 64 MiB worker opens latin.pdf ({describe r0})" (isDoc 1 r0))
  let r ← c.request (.render 0 8 0 none) (some 20000)
  let code ← c.waitExit 5000
  IO.println s!"  worker fences: 64 MiB worker asked for a 124 MB render: {describe r}, exit {code}"
  -- Task 12.c1: always shown (fast: the worker ends at once) — its stderr names the fences
  -- installed and the mechanism that ended it.
  diagnose exe small [.openDoc bytes true, .render 0 8 0 none]
  f := f + (← check s!"the memory ceiling ends the worker instead of answering ({describe r})"
    (match r with | .error (.exited _) => true | _ => false))
  f := f + (← check s!"the ended worker exited with a failure status ({code})"
    (match code with | some k => k != 0 | none => false))
  let big : Protocol.StartConfig := { noSubst := true, memLimitMiB := 2048 }
  let c ← spawn exe (start := big)
  discard <| c.request (.openDoc bytes true) (some 10000)
  let r ← c.request (.render 0 8 0 none) (some 60000)
  let k ← check s!"a 2048 MiB worker renders the same page ({describe r})"
    (match r with | .ok (.image w h _) => w == 4896 && h == 6336 | _ => false)
  c.close
  if k > 0 then diagnose exe big [.openDoc bytes true, .render 0 8 0 none, .quit] 60000
  f := f + k
  -- CPU: one request spinning 4 s under a 1 s fence.
  let spin4 : Protocol.StartConfig := { noSubst := true, cpuLimitS := 1, spinMs := 4000 }
  let c ← spawn exe (start := spin4)
  discard <| c.request (.openDoc bytes true) (some 10000)
  let t0 ← nowMs
  let r ← c.request (.render 0 1 0 none) (some 20000)
  let t1 ← nowMs
  let code ← c.waitExit 5000
  IO.println s!"  worker fences: 1 s CPU fence, 4 s spin: {describe r} after {t1 - t0} ms, exit {code}"
  let k ← check s!"the CPU fence ends a 4 s request ({describe r}, {t1 - t0} ms)"
    (match r with | .error (.exited _) => t1 - t0 < 3900 | _ => false)
  let k := k + (← check s!"ended by SIGXCPU or with a failure status ({code})"
    (match code with | some k => k != 0 | none => false))
  if k > 0 then diagnose exe spin4 [.openDoc bytes true, .render 0 1 0 none, .quit] 20000
  f := f + k
  -- Per request: four 0.6 s requests under the same 1 s fence are all answered.
  let spin06 : Protocol.StartConfig := { noSubst := true, cpuLimitS := 1, spinMs := 600 }
  let c ← spawn exe (start := spin06)
  discard <| c.request (.openDoc bytes true) (some 10000)
  let mut answered := 0
  for _ in [0:4] do
    match ← c.request (.render 0 1 0 none) (some 20000) with
    | .ok (.image ..) => answered := answered + 1
    | _ => pure ()
  let k ← check s!"the CPU fence is re-armed per request ({answered}/4 answered)" (answered == 4)
  c.close
  if k > 0 then
    diagnose exe spin06 ([.openDoc bytes true] ++ List.replicate 4 (.render 0 1 0 none) ++ [.quit])
  f := f + k
  return f

/-- Run the suite. -/
def run : IO Nat := do
  let some exe ← workerExe
    | check "worker executable at .lake/build/bin/worker (run `lake build worker`)" false
  let mut f := 0
  f := f + (← endToEnd exe)
  f := f + (← malformed exe)
  f := f + (← killAndRestart exe)
  f := f + (← overhead exe)
  f := f + (← textLinksLayers exe)
  f := f + (← startupFlags exe)
  f := f + (← fences exe)
  return f

end SafePdf.Tests.Worker
