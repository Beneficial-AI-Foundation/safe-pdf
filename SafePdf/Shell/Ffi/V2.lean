import SafePdf.Api
import SafePdf.Shell.Read
import SafePdf.Shell.Fonts
import SafePdf.Shell.Worker.Client
import SafePdf.Shell.Ffi.Flat
import SafePdf.Shell.Views.Common

/-!
# C API v2, document layer over the worker (task 11.3a1)

Plan.md §6 Phase 11; `docs/macos-design.md` §3 decisions 2 and 4: the native shell reads the
file through the capped read (task 12.1), keeps the parse it needs for layout (page count and
sizes), and hands the bytes to a **confined document worker** (`Worker.Session`, tasks
12.2a–d) that renders pages and answers the text index, link and outline requests with
priorities, cancellation, a deadline kill and respawn. Completion is reported to C through one
`@[extern]` callback (`deliver`); `macos/safepdf_core.c` copies the result into flat C structs
and enqueues the caller's callback on its dispatch queue.

Unverified shell code (`IO`). The exports here are **not** the public C API: they take and
return Lean objects and are wrapped by `macos/safepdf_core.c` (`macos/safepdf_core.h`). Every
object parameter is owned (Lean v4.36 rejects `@&` on `@[export]`), so the C side `lean_inc`s
the handle before each call.

* **Where each request runs.** Renders, the selection/search index (`pageIndex`), links
  (`viewLinks`) and the outline go to the worker, as in the Tk viewer (12.2c/d). The protocol
  has no request for page labels, attachments or the layers configuration; like the Tk viewer
  (`docs/viewer.md`: "the parse the GUI keeps for layout, page labels, open settings,
  attachments, the layers panel and Save"), they are computed from the in-process parse on a
  dedicated Lean task and delivered the same way. Their priority is ignored.
* **Delivery.** Every accepted request is delivered **exactly once** (`deliver`): OK with its
  blob, an error with its text, or cancelled. Worker requests are delivered from a task mapped
  over the session's reply (`IO.mapTask`); in-process ones from their own task. The tasks are
  kept in `Doc.tasks` until they finish so that none is dropped unreferenced.
* **Close.** `shutdown` closes the session (queued requests are dropped as cancelled, a request
  in flight is killed) and marks in-process requests that have not started as cancelled; the C
  side then waits until every outstanding request has been delivered.
* **Worker crash or deadline.** A request without an answer within the deadline kills the
  worker (`failed .timeout`), a crashed worker gives `failed (.exited …)`; both are delivered as
  errors with the Tk viewer's text, and the next request spawns a fresh worker and sends the
  bytes again (`Session.ensureClient`).
-/

namespace SafePdf.Shell.Ffi.V2

open SafePdf SafePdf.Core
open SafePdf.Shell.Worker (Session Reply ClientError)

/-- The limits of every document the C API opens (the Tk viewer's `Viewer.limits`). -/
def limits : Limits := Limits.default

/-- The deadline of a worker request when the caller gives none (the Tk viewer's
`workerDeadlineMs`). -/
def defaultDeadlineMs : Nat := 20000

/-- A request in flight: its C id, its worker request id (`none`: answered in this process)
and whether the C side cancelled it. -/
structure Pending where
  /-- The C request id. -/
  cid : UInt64
  /-- The session's request id, for worker requests. -/
  sid : Option Nat
  /-- Cancelled by the C side (in-process requests check it before they start). -/
  cancelled : Bool := false

/-- An open document as the C side sees it: an opaque `lean_object *`. -/
structure Handle where
  /-- The in-process parse (page count, sizes, labels, attachments, layers). -/
  api : Api.Document
  /-- The worker session of this document (one worker process per document). -/
  session : Session
  /-- The deadline the session runs with (for the error text). -/
  deadlineMs : Nat
  /-- The page labels (computed on first use). -/
  labels : Thunk (Array String)
  /-- The attachments (computed on first use). -/
  listing : Thunk Core.Doc.Attachments.Listing
  /-- The optional content configuration (computed on first use). -/
  ocCfg : Thunk (Option Core.Doc.OptionalContent.Config)
  /-- Requests not delivered yet. -/
  pending : IO.Ref (List Pending)
  /-- Delivery tasks not finished yet (kept referenced). -/
  tasks : IO.Ref (Array (Task (Except IO.Error Unit)))
  /-- `shutdown` was called. -/
  closed : IO.Ref Bool

/-- The session's document id (one document per session). -/
def docId : Nat := 1

/-- **The C callback** (`macos/safepdf_core.c`): delivers the outcome of the request whose C
record is `token` — `status` 0 OK (`blob`, and `w`·`h` for an image), 1 error (`msg`),
2 cancelled. It copies what it needs before it returns and never calls back into Lean. -/
@[extern "safepdf_c_deliver"]
opaque deliver (token : USize) (status : UInt8) (msg : @& String) (blob : @& ByteArray)
  (w h : USize) : IO Unit

/-- The kinds of request (`safepdf_core.c` passes the number). -/
inductive Kind where
  | render | pageIndex | links | outline | labels | attachments | attachmentBytes | layers
  deriving DecidableEq, Repr

/-- The kind of a C kind number. -/
def Kind.ofNat? : Nat → Option Kind
  | 0 => some .render | 1 => some .pageIndex | 2 => some .links | 3 => some .outline
  | 4 => some .labels | 5 => some .attachments | 6 => some .attachmentBytes | 7 => some .layers
  | _ => none

#guard (List.range 9).map (fun n => (Kind.ofNat? n).isSome) ==
  [true, true, true, true, true, true, true, true, false]

/-- What is delivered: status (0 OK, 1 error, 2 cancelled), message, blob, image size. -/
structure Out where
  /-- 0 OK, 1 error, 2 cancelled. -/
  status : UInt8
  /-- The error text (status 1). -/
  msg : String := ""
  /-- The result: the flat tables (`Flat`), the RGBA bytes or the attachment's bytes. -/
  blob : ByteArray := .empty
  /-- Image width (renders). -/
  w : Nat := 0
  /-- Image height (renders). -/
  h : Nat := 0

/-- An error outcome. -/
def Out.err (m : String) : Out := { status := 1, msg := m }

/-- A cancelled outcome. -/
def Out.cancelled : Out := { status := 2 }

/-- An OK outcome. -/
def Out.ok (b : ByteArray) : Out := { status := 0, blob := b }

/-- What went wrong with a worker request (the Tk viewer's `failText`). -/
def failText : ClientError → String
  | .notEncodable => "the request does not fit the protocol"
  | .timeout => "no answer in time"
  | .exited d => d
  | .tooLong n => s!"its answer of {n} bytes is above the cap"
  | .badFrame _ => "its answer does not decode"

/-- The error text of a request that hit the deadline (the Tk viewer's `timeoutText`). -/
def timeoutText (deadlineMs : Nat) : String :=
  let t := if deadlineMs % 1000 == 0 then s!"{deadlineMs / 1000} s" else s!"{deadlineMs} ms"
  s!"the document took too long (no answer within {t}; its worker was stopped)"

/-- **The outcome of a worker reply** for a request of kind `k` (pure). An image is checked
against its size before C copies it. -/
def outOfReply (k : Kind) (deadlineMs : Nat) : Reply → Out
  | .cancelled => .cancelled
  | .failed .timeout => .err (timeoutText deadlineMs)
  | .failed e => .err s!"the document worker stopped: {failText e}"
  | .response (.error _ msg) _ => .err msg
  | .response r _ =>
    match k, r with
    | .render, .image w h data =>
      if data.size == 4 * w * h then { status := 0, blob := data, w, h }
      else .err s!"the document worker sent a malformed image ({w}x{h}, {data.size} bytes)"
    | .pageIndex, .pageIndex cs ds hs => .ok (Flat.pageIndex cs ds hs)
    | .links, .viewLinks ls => .ok (Flat.links ls)
    | .outline, .outline items => .ok (Flat.outline items)
    | _, _ => .err "the document worker answered with another message"

#guard (outOfReply .render 20000 .cancelled).status == 2
#guard (outOfReply .render 20000 (.failed .timeout)).msg ==
  "the document took too long (no answer within 20 s; its worker was stopped)"
#guard (outOfReply .render 500 (.response (.image 1 1 (ByteArray.mk #[1, 2, 3, 4])) 0)).status == 0
#guard (outOfReply .render 500 (.response (.image 2 1 (ByteArray.mk #[1, 2, 3, 4])) 0)).status == 1
#guard (outOfReply .links 500 (.response (.outline []) 0)).msg ==
  "the document worker answered with another message"

/-- **The answer of an in-process request** (labels, attachments, an attachment's bytes, the
layers panel) on the document `d` (pure; the thunks are forced here). -/
def answerHere (d : Handle) (k : Kind) (index : Nat) : Out :=
  match k with
  | .labels => .ok (Flat.labels d.labels.get)
  | .attachments => .ok (Flat.attachments d.listing.get)
  | .attachmentBytes =>
    match d.listing.get.entries[index]? with
    | none => .err s!"no attachment {index} (the document lists {d.listing.get.entries.length})"
    | some a =>
      match Core.Doc.Attachments.decode d.api.doc limits a with
      | .ok b => .ok b
      | .error e => .err (Shell.renderError e)
  | .layers => .ok (Flat.layers d.ocCfg.get)
  | _ => .err "not an in-process request"

/-- Calls the C callback with `o`; never throws (a failure of the call itself is ignored: the
C side has nothing else to deliver). -/
def deliverOut (token : USize) (o : Out) : IO Unit :=
  try deliver token o.status o.msg o.blob o.w.toUSize o.h.toUSize catch _ => pure ()

/-- Forgets request `cid` (delivered). -/
def Handle.forget (d : Handle) (cid : UInt64) : IO Unit :=
  d.pending.modify (·.filter (·.cid != cid))

/-- Keeps the delivery task `t`, dropping the finished ones. -/
def Handle.keep (d : Handle) (t : Task (Except IO.Error Unit)) : IO Unit := do
  let ts ← d.tasks.get
  let mut live := #[t]
  for x in ts do
    if !(← IO.hasFinished x) then live := live.push x
  d.tasks.set live

/-- The worker request of kind `k` (`none`: answered in this process, or a bad argument with
its message). -/
def workerRequest (k : Kind) (page num den rot : Nat) (layers : ByteArray) :
    Except String (Option Worker.Protocol.Request) := do
  let oc ← if layers.isEmpty then pure none else
    match Flat.decodeState layers with
    | some st => pure (some st)
    | none => throw "malformed layers state"
  match k with
  | .render =>
    if num == 0 || den == 0 then throw "zoom must be positive"
    if rot > 3 then throw s!"rotation must be 0–3 quarter turns (got {rot})"
    return some (.render page ((num : Rat) / (den : Rat)) rot oc)
  | .pageIndex => return some (.pageIndex page oc)
  | .links => return some (.viewLinks page)
  | .outline => return some .outline
  | _ => return none

/-- **Submits a request** of kind number `kind` for document `d`, delivered to the C record
`token` (C id `cid`). `page` is the page (or the attachment index), `num/den` the zoom and
`rot` the extra rotation of a render, `layers` an encoded layers state (`Flat.encodeState`;
empty: the document's default), `prio` the worker priority (0 most urgent). Never throws: every
call delivers exactly once (a bad argument is delivered as an error). -/
@[export safepdf_lean_doc_submit]
def submit (d : Handle) (token : USize) (cid : UInt64) (kind : UInt8) (page : USize)
    (num den : USize) (rot : UInt8) (layers : ByteArray) (prio : UInt8) : IO Unit := do
  let some k := Kind.ofNat? kind.toNat
    | deliverOut token (.err s!"unknown request kind {kind}")
  if ← d.closed.get then
    deliverOut token .cancelled
    return
  match workerRequest k page.toNat num.toNat den.toNat rot.toNat layers with
  | .error m => deliverOut token (.err m)
  | .ok (some req) =>
    try
      let (sid, t) ← d.session.submit docId req prio.toNat
      d.pending.modify (⟨cid, some sid, false⟩ :: ·)
      let dl := d.deadlineMs
      let t2 ← IO.mapTask (fun r => do
        d.forget cid
        deliverOut token (outOfReply k dl r)) t
      d.keep t2
    catch e => deliverOut token (.err s!"cannot submit the request: {e}")
  | .ok none =>
    d.pending.modify (⟨cid, none, false⟩ :: ·)
    try
      let t ← IO.asTask (prio := .dedicated) do
        let cancelled := ((← d.pending.get).find? (·.cid == cid)).any (·.cancelled)
        let out ← if cancelled || (← d.closed.get) then pure Out.cancelled
          else IO.lazyPure fun _ => answerHere d k page.toNat
        d.forget cid
        deliverOut token out
      d.keep t
    catch e =>
      d.forget cid
      deliverOut token (.err s!"cannot start the request: {e}")

/-- **Cancels** request `cid`: a worker request is dropped while queued and its worker killed
after `SessionConfig.preemptMs` when in flight; an in-process request that has not started is
delivered as cancelled. A delivered (or unknown) id changes nothing. -/
@[export safepdf_lean_doc_cancel]
def cancel (d : Handle) (cid : UInt64) : IO Unit := do
  let ps ← d.pending.modifyGet fun ps =>
    (ps, ps.map fun p => if p.cid == cid then { p with cancelled := true } else p)
  if let some p := ps.find? (·.cid == cid) then
    if let some sid := p.sid then d.session.cancel sid

/-- **Raises** queued worker request `cid` to priority `prio` when that is more urgent
(`Session.raise`). -/
@[export safepdf_lean_doc_raise]
def raise (d : Handle) (cid : UInt64) (prio : UInt8) : IO Unit := do
  if let some p := (← d.pending.get).find? (·.cid == cid) then
    if let some sid := p.sid then d.session.raise sid prio.toNat

/-- **Closes** the document's session: queued requests are delivered as cancelled, a request in
flight is killed, the worker stops; in-process requests not started yet are delivered as
cancelled. The C side waits for every delivery afterwards. -/
@[export safepdf_lean_doc_shutdown]
def shutdown (d : Handle) : IO Unit := do
  d.closed.set true
  d.session.shutdown

/-- The worker's font search and resource ceilings, as the Tk viewer starts it
(`Viewer.workerStart`): `SAFEPDF_SUBST_FONTS=0`, `$HOME`, `$SAFEPDF_FONT_DIR`, the viewer's
memory and CPU ceilings. -/
def workerStart : IO Worker.Protocol.StartConfig := do
  let noSubst := (← IO.getEnv "SAFEPDF_SUBST_FONTS") == some "0"
  let home := (← IO.getEnv "HOME").filter (!·.isEmpty)
  return { limits, noSubst, home, fontDirs := ← Fonts.userDirs,
           memLimitMiB := App.Budget.ceilings.workerMemMiB,
           cpuLimitS := App.Budget.ceilings.workerCpuS }

/-- **Opens a document from its bytes** (the GUI's capped read or the caller's buffer): parses
it in this process (`Api.openBytes`, the viewer's limits; `strict`: no repair path) and starts
its worker session with the bytes. `worker` is the worker executable (`""`: `worker` next to
this process's executable), `deadlineMs` the request deadline (0: `defaultDeadlineMs`),
`stallMs` a test hook (the worker sleeps before each render). A relative `worker` is resolved
against the current directory. Throws an `IO.userError` with the
English error text when the bytes do not open or there is no worker executable. -/
@[export safepdf_lean_doc_open_bytes]
def openBytes (bytes : ByteArray) (worker : String) (deadlineMs : USize) (strict : UInt8)
    (stallMs : USize) : IO Handle := do
  let allowRepair := strict == 0
  let api ← match Api.openBytes bytes { limits, allowRepair } with
    | .ok d => pure d
    | .error e => throw (IO.userError e.message)
  let exe : System.FilePath ← if worker.isEmpty then pure ((← IO.appDir) / "worker")
    else pure worker
  -- The session starts the worker with `/` as working directory: a relative path would name
  -- another file there (and exec would fail), so it is made absolute here.
  let exe ← if exe.isAbsolute then pure exe else pure ((← IO.currentDir) / exe)
  if !(← exe.pathExists) then throw (IO.userError s!"no document worker at {exe}")
  let deadlineMs := if deadlineMs == 0 then defaultDeadlineMs else deadlineMs.toNat
  let session ← Session.start { exe, limits, deadlineMs, start := ← workerStart }
  if stallMs != 0 then session.setEnv #[("SAFEPDF_WORKER_TEST_STALL_MS", some (toString stallMs))]
  session.setDoc (some (docId, bytes, allowRepair))
  let doc := api.doc
  return { api, session, deadlineMs,
           labels := Thunk.mk fun _ => App.Links.labels doc limits
           listing := Thunk.mk fun _ => Core.Doc.Attachments.list doc limits
           ocCfg := Thunk.mk fun _ =>
             (Core.Doc.OptionalContent.read (Core.Content.Run.resolve (Core.Text.docSource limits doc))
               limits (Core.Filter.Budget.init limits) doc.catalog).1
           pending := ← IO.mkRef [], tasks := ← IO.mkRef #[], closed := ← IO.mkRef false }

/-- **Opens the file `path`** through the capped read (`Shell.Read.readFile`, task 12.1: at
most `maxInputBytes + 1` bytes through a handle), then `openBytes`. -/
@[export safepdf_lean_doc_open_file]
def openFile (path : String) (worker : String) (deadlineMs : USize) (strict : UInt8)
    (stallMs : USize) : IO Handle := do
  let bytes ← match ← Read.readFile path limits.maxInputBytes .inputBytes with
    | .ok b => pure b
    | .error e => throw (IO.userError (Api.Error.pdf e).message)
  openBytes bytes worker deadlineMs strict stallMs

/-- Number of pages. -/
@[export safepdf_lean_doc_page_count]
def pageCount (d : Handle) : USize := d.api.pageCount.toUSize

/-- Displayed width and height in points of page `i` (CropBox, `/Rotate` applied), as a
two-element `FloatArray`; empty when `i` is out of range. -/
@[export safepdf_lean_doc_page_size]
def pageSize (d : Handle) (i : USize) : FloatArray :=
  match Api.pageInfo d.api i.toNat with
  | .ok info => ⟨#[Flat.ratToFloat info.size.1, Flat.ratToFloat info.size.2]⟩
  | .error _ => FloatArray.empty

/-- Bit 0: the file was opened by the repair path; bit 1: it is encrypted. -/
@[export safepdf_lean_doc_flags]
def flags (d : Handle) : UInt8 :=
  (if d.api.repaired then 1 else 0) + (if d.api.encrypted then 2 else 0)

/-- **Toggles layer row `row`** of the layers panel in state `state` (encoded,
`Flat.encodeState`; empty: the document's default) with `Sidebar.layerToggle` (radio-button
groups, locked groups unchanged; a heading changes nothing). Returns the new state as a blob
(`Flat.state`); throws for a malformed state. Runs on the calling thread (it reads the
document's optional content the first time). -/
@[export safepdf_lean_doc_layers_toggle]
def layersToggle (d : Handle) (state : ByteArray) (row : USize) : IO ByteArray := do
  match d.ocCfg.get with
  | none => return Flat.state {}
  | some c =>
    let st ← if state.isEmpty then pure c.initial else
      match Flat.decodeState state with
      | some s => pure s
      | none => throw (IO.userError "malformed layers state")
    return Flat.state (App.Sidebar.layerToggle c st (App.Sidebar.layerRows c) row.toNat)

/-! ## Page geometry (task 11.3c1) -/

/-- Whether `v` fits a 64-bit signed integer. -/
def fitsI64 (v : Int) : Bool := decide (-(2 ^ 63) ≤ v) && decide (v < 2 ^ 63)

/-- Appends `v` as eight little-endian bytes in two's complement (callers check `fitsI64`). -/
def putI64 (b : ByteArray) (v : Int) : ByteArray := Flat.putU64 b (v % 2 ^ 64).toNat

/-- Degrees of a rotation (0, 90, 180, 270). -/
def rotDeg : Doc.Rotation → Nat
  | .r0 => 0 | .r90 => 90 | .r180 => 180 | .r270 => 270

/-- The integers of a page's geometry, as `safepdf_page_geom` (`macos/safepdf_view.h`) holds
it: the CropBox's `llx lly urx ury`, each as numerator and (positive) denominator of the exact
rational, then `/Rotate` in degrees — what `FfiView.layoutW` reads per page. -/
def geomInts (b : Raster.Geom.Box) (r : Doc.Rotation) : List Int :=
  [b.llx.num, b.llx.den, b.lly.num, b.lly.den, b.urx.num, b.urx.den, b.ury.num, b.ury.den,
    rotDeg r]

#guard geomInts ⟨0, 0, 601 / 2, 400⟩ .r180 == [0, 1, 0, 1, 601, 2, 400, 1, 180]
#guard geomInts ⟨-10, 0, 148819 / 250, 84189 / 100⟩ .r270 ==
  [-10, 1, 0, 1, 148819, 250, 84189, 100, 270]
#guard (geomInts ⟨(2 : Rat) ^ 64, 0, 1, 1⟩ .r0).all fitsI64 == false

/-- **The geometry of page `i`** for layout (`safepdf_doc_page_geom`): its effective CropBox
(`Box.ofRect` of the page's crop rectangle, exactly the box `Api.pageInfo`, the renderer and the
Tk viewer's layout use) and its effective `/Rotate`, as `geomInts` in the wire format (nine
64-bit little-endian integers). Empty when `i` is out of range or a coordinate does not fit
64 bits. -/
@[export safepdf_lean_doc_page_geom]
def pageGeom (d : Handle) (i : USize) : ByteArray :=
  match d.api.page i.toNat with
  | .error _ => .empty
  | .ok p =>
    let xs := geomInts (Raster.Geom.Box.ofRect p.cropBox) p.rotate
    if xs.all fitsI64 then xs.foldl putI64 .empty else .empty

/-- The rotation of `q` quarter turns clockwise (`none` above 3). -/
def rotOfQuarters : Nat → Option Doc.Rotation
  | 0 => some .r0 | 1 => some .r90 | 2 => some .r180 | 3 => some .r270 | _ => none

/-- **TESTS ONLY** (`safepdf_test_render_sync`, `macos/tests/core_test.c`): renders page `i` in
this process, on the calling thread, with the call the worker answers a render with
(`Raster.Glyph.renderDocPage` at `num / den` with `rot` extra quarter turns, a fresh decode
budget, the substitute fonts found on this system, the default layers state). Returns the
width and height (eight bytes each, `Flat.putU64`) followed by the RGBA bytes; throws an
`IO.userError` for a bad page, zoom or rotation, or a core error. The C test compares it with
the worker's answer to `safepdf_doc_render` byte for byte. -/
@[export safepdf_lean_doc_test_render]
def testRender (d : Handle) (i : USize) (num den : USize) (rot : UInt8) : IO ByteArray := do
  if num == 0 || den == 0 then throw (IO.userError "zoom must be positive")
  let some r := rotOfQuarters rot.toNat
    | throw (IO.userError s!"rotation must be 0–3 quarter turns (got {rot})")
  let zoom : Rat := (num.toNat : Rat) / (den.toNat : Rat)
  match d.api.page i.toNat with
  | .error e => throw (IO.userError e.message)
  | .ok p =>
    let a := d.api
    let subst ← Fonts.loadSubstFonts a.limits
    let res ← IO.lazyPure fun _ =>
      (Raster.Glyph.renderDocPage a.limits a.doc p zoom r (Filter.Budget.init a.limits)
        (subst := subst)).1
    match res with
    | .ok img => return Flat.putU64 (Flat.putU64 .empty img.w) img.h ++ img.data
    | .error e => throw (IO.userError (Api.Error.pdf e).message)

end SafePdf.Shell.Ffi.V2
