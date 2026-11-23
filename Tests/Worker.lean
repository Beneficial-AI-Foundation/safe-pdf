import SafePdf.Api
import SafePdf.Shell.Worker.Client
import SafePdf.Shell.Worker.Serve

/-!
# Document worker, end to end (task 12.2a)

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
  match ← c.request (.render 0 (3 / 2) 0), local_ with
  | .ok (.image w h data), .ok img =>
    f := f + (← check s!"render size {w}x{h} vs {img.w}x{img.h}" (w == img.w && h == img.h))
    f := f + (← check "render bytes equal the in-process render" (data == img.data))
    f := f + (← check "render has ink" (data.toList.any (· < 128)))
  | r, _ => f := f + (← check s!"render ({describe r})" false)
  -- Rotated render too.
  let localR := (Raster.Glyph.renderDocPage limits d.doc page 1 .r90
    (Filter.Budget.init limits) (subst := subst)).1
  match ← c.request (.render 0 1 1), localR with
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
  f := f + (← check "page out of range is pageFailed" (isErr .pageFailed (← c.request (.render 99 1 0))))
  f := f + (← check "rotation 4 is pageFailed" (isErr .pageFailed (← c.request (.render 0 1 4))))
  f := f + (← check "zoom 0 is pageFailed" (isErr .pageFailed (← c.request (.render 0 0 0))))
  f := f + (← check "zoom -1 is pageFailed" (isErr .pageFailed (← c.request (.render 0 (-1) 0))))
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
  let r ← c.request (.render 0 8 0) (some 20)
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
    match ← c2.request (.render 0 1 0) (some 10000) with
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
    match ← c.request (.render 0 1 0) with
    | .ok (.image _ _ data) => wsz := wsz + data.size
    | _ => pure ()
  let t2 ← IO.monoNanosNow
  c.close
  let ms (a b : Nat) : String := s!"{(b - a) / 100000 / 10}.{(b - a) / 100000 % 10}"
  IO.println s!"  worker overhead: {n} renders of page 1 at zoom 1 ({sz / n} bytes each): \
    in-process {ms t0 t1} ms, worker {ms s1 t2} ms; spawn + open {ms s0 s1} ms"
  check "overhead: same image sizes" (sz == wsz)

/-- Run the suite. -/
def run : IO Nat := do
  let some exe ← workerExe
    | check "worker executable at .lake/build/bin/worker (run `lake build worker`)" false
  let mut f := 0
  f := f + (← endToEnd exe)
  f := f + (← malformed exe)
  f := f + (← killAndRestart exe)
  f := f + (← overhead exe)
  return f

end SafePdf.Tests.Worker
