import SafePdf.Shell.Worker.Wire

/-!
# Document worker client (task 12.2a)

Plan.md §6 Phase 12, "Restricted, stoppable document worker". Unverified shell code (`IO`):
start the `worker` executable (`SafePdf.Shell.Worker.Main`), exchange frames with it
(`SafePdf.Shell.Worker.Protocol`), and stop it.

* **Spawn** (`spawn`): `IO.Process.spawn` with piped stdin/stdout, stderr discarded, an
  **empty environment** (`inheritEnv := false`) and `/` as working directory, so the worker
  sees neither the user's environment (12.2b adds the sandbox) nor a meaningful relative path.
* **Request** (`request`): frame the request (`Protocol.frameRequest`: valid and within
  `Protocol.requestCap`, else `notEncodable` without sending), write it, then read one
  response frame (cap `Protocol.responseCap`: a longer header is refused before its payload
  is read) on a dedicated task. With a timeout, the caller polls the task every millisecond;
  when the deadline passes the worker is **killed** (which closes its stdout, so the reading
  task ends) and `timeout` is returned. A killed or crashed worker gives `exited`; the client
  must spawn a new one.
* **Kill** (`kill`): `SIGTERM` and reap. Waiting on the reading task after a kill keeps the
  rule that no dedicated task outlives the call (the Lean runtime joins them at exit).
-/

namespace SafePdf.Shell.Worker

open SafePdf

/-- The stdio configuration of a worker process. -/
abbrev workerStdio : IO.Process.StdioConfig :=
  { stdin := .piped, stdout := .piped, stderr := .null }

/-- A running worker. -/
structure Client where
  /-- The process. -/
  child : IO.Process.Child workerStdio
  /-- The limits that set the frame caps (the worker uses `Limits.default`). -/
  limits : Limits
  /-- The exit status once the process has been reaped (a reaped child must not be waited on
  or signalled again: `waitpid` fails with `ECHILD`, and its process id may be reused). -/
  status : IO.Ref (Option UInt32)

/-- Why a request got no response. -/
inductive ClientError where
  /-- The request is not encodable (a number out of range) or above `requestCap`. -/
  | notEncodable
  /-- No response within the timeout: the worker was killed. -/
  | timeout
  /-- The worker is gone (its stdout ended, or writing to it failed). -/
  | exited (detail : String)
  /-- The response frame is above `responseCap` (its payload was not read). -/
  | tooLong (len : Nat)
  /-- The response frame does not decode. -/
  | badFrame (e : Protocol.DecodeError)
  deriving Repr

instance : ToString ClientError := ⟨fun e => reprStr e⟩

/-- **Start a worker** from the executable `exe` (an absolute path), always with an empty
environment (the worker refuses anything else, task 12.2b). Its configuration goes on the
command line (task 12.2d, `Protocol.StartConfig.toArgs`): `limits` and the font search of
`start` (its own `limits` field is replaced by `limits`). `env` carries test settings only:
`SAFEPDF_WORKER_TEST_STALL_MS=N` becomes the worker's `--test-stall-ms=N` flag
(`SafePdf.Shell.Worker.TestHooks`); other entries are ignored. -/
def spawn (exe : System.FilePath) (limits : Limits := {})
    (env : Array (String × Option String) := #[]) (start : Protocol.StartConfig := {}) :
    IO Client := do
  let stall := (env.findSome? fun (k, v) =>
    if k == "SAFEPDF_WORKER_TEST_STALL_MS" then v.bind String.toNat? else none).getD 0
  let args := { start with limits, stallMs := stall }.toArgs
  let child ← IO.Process.spawn
    { toStdioConfig := workerStdio, cmd := exe.toString, args, cwd := some "/", env := #[],
      inheritEnv := false }
  return { child, limits, status := ← IO.mkRef none }

/-- **Whether the worker has exited** (its status, if so; reaps it). Never throws. -/
def Client.exited? (c : Client) : IO (Option UInt32) := do
  if let some s ← c.status.get then return some s
  match ← (try c.child.tryWait catch _ => pure none) with
  | some s => c.status.set (some s); return some s
  | none => return none

/-- **Kill** the worker (`SIGTERM`) and reap it, unless it has already exited (then it is
only reaped, so a reused process id is never signalled). Returns the exit status (`none` if
it could not be reaped). Never throws. -/
def Client.kill (c : Client) : IO (Option UInt32) := do
  if let some s ← c.exited? then return some s
  try c.child.kill catch _ => pure ()
  match ← (try some <$> c.child.wait catch _ => pure none) with
  | some s => c.status.set (some s); return some s
  | none => return none

/-- **Wait for the worker to exit** for at most `timeoutMs` milliseconds, then kill it.
Returns the exit status. -/
def Client.waitExit (c : Client) (timeoutMs : Nat := 5000) : IO (Option UInt32) := do
  let deadline := (← IO.monoMsNow) + timeoutMs
  repeat
    if let some s ← c.exited? then return some s
    if (← IO.monoMsNow) ≥ deadline then break
    IO.sleep 1
  c.kill

/-- Read one response frame. -/
def Client.readResponse (c : Client) : IO (Except ClientError Protocol.Response) := do
  let s := IO.FS.Stream.ofHandle c.child.stdout
  match ← readFrame s (Protocol.responseCap c.limits) with
  | .eof => return .error (.exited "end of output")
  | .truncated n => return .error (.exited s!"end of output inside a frame ({n} bytes)")
  | .tooLong len => return .error (.tooLong len)
  | .frame payload =>
    match Protocol.decodeBody Protocol.response payload with
    | .ok r => return .ok r
    | .error e => return .error (.badFrame e)

/-- Send raw bytes (tests: malformed and oversized frames). -/
def Client.sendRaw (c : Client) (bytes : ByteArray) : IO (Except ClientError Unit) := do
  try
    c.child.stdin.write bytes
    c.child.stdin.flush
    return .ok ()
  catch e => return .error (.exited (toString e))

/-- Wait for a response, killing the worker after `timeoutMs` milliseconds (`none`: wait). -/
def Client.awaitResponse (c : Client) (timeoutMs : Option Nat) :
    IO (Except ClientError Protocol.Response) := do
  match timeoutMs with
  | none => c.readResponse
  | some ms =>
    let task ← IO.asTask c.readResponse .dedicated
    let deadline := (← IO.monoMsNow) + ms
    repeat
      if ← IO.hasFinished task then break
      if (← IO.monoMsNow) ≥ deadline then
        discard c.kill
        discard <| IO.wait task
        return .error .timeout
      IO.sleep 1
    match ← IO.wait task with
    | .ok r => return r
    | .error e => return .error (.exited (toString e))

/-- **Send a request and read its response**, with an optional timeout in milliseconds after
which the worker is killed. -/
def Client.request (c : Client) (req : Protocol.Request) (timeoutMs : Option Nat := none) :
    IO (Except ClientError Protocol.Response) := do
  match Protocol.frameRequest c.limits req with
  | none => return .error .notEncodable
  | some f =>
    match ← c.sendRaw f with
    | .error e => return .error e
    | .ok () => c.awaitResponse timeoutMs

/-- Ask the worker to quit and reap it (killing it if it does not answer within
`timeoutMs`). -/
def Client.close (c : Client) (timeoutMs : Nat := 5000) : IO Unit := do
  match ← c.request .quit (some timeoutMs) with
  | .ok _ => discard (c.waitExit timeoutMs)
  | .error _ => discard c.kill

/-! ## Sessions: one worker per open document, requests queued (task 12.2c)

A `Session` serves the GUI's requests for the open document through one worker process at a
time. The GUI thread only queues requests (`submit`), cancels them (`cancel`) and changes the
document (`setDoc`); every request is answered by a promise, so the GUI polls tasks as it did
for the render threads of task 8.8 and never waits on the worker's pipes. A **dispatcher**
(one dedicated task per session, `run`) owns the `Client`:

* **Queue.** It answers one request at a time, the lowest `prio` first (the viewer: 0 the
  current page or spread and the outline, 1 other pages in view and the prefetch, 2
  thumbnails), oldest first among equals. Requests cancelled by the GUI or made for another
  document are dropped unanswered (`Reply.cancelled`) when they come up.
* **One process per document.** The worker is spawned for the document of the request
  (`setDoc` id), with the document's bytes in an `openDoc` request; a worker of another
  document is killed first. After a kill or a crash the next request spawns a fresh one and
  sends the bytes again.
* **Deadline.** A request (or the `openDoc` of a spawn) not answered within
  `SessionConfig.deadlineMs` kills the worker and gets `failed .timeout`.
* **Cancellation and preemption by kill.** The renderer is pure and cannot be interrupted, but
  the worker can be killed: a request in flight whose document changed (or the session closed)
  is killed at once; after `preemptMs`, one the GUI cancelled is killed (`cancelled`), and so is
  one that blocks a more urgent request — a lower `prio`, or a newer `prio` 0 one submitted at
  least `newerMs` later (the user moved on) — which then goes back into the queue with `prio`
  at least 1 (answered later, from scratch).
* **Idle.** With nothing queued it waits on a promise that `submit`, `setDoc` and `shutdown`
  resolve; a worker whose document is no longer open is killed then.

The state shared by both threads is one `IO.Ref` changed only by atomic `modifyGet`/`modify`.
-/

/-- What a request submitted to a `Session` gets back. -/
inductive Reply where
  /-- The worker's response and the time from sending the request to reading it (ns). -/
  | response (r : Protocol.Response) (ns : Nat)
  /-- No response: `timeout` (the worker was killed after the deadline), the worker exited,
  sent a bad frame or could not open the document. -/
  | failed (e : ClientError)
  /-- Cancelled or superseded before it was answered (the GUI shows nothing for it). -/
  | cancelled

instance : Nonempty Reply := ⟨.cancelled⟩

/-- A request waiting in a session's queue (or being answered). -/
structure Queued where
  /-- Session-wide request number (`Session.cancel`). -/
  id : Nat
  /-- The document it is for (`Session.setDoc` id). -/
  doc : Nat
  /-- The request. -/
  req : Protocol.Request
  /-- Priority, 0 most urgent. -/
  prio : Nat
  /-- When it was submitted (`IO.monoMsNow`). -/
  submitted : Nat
  /-- Resolved with the reply. -/
  promise : IO.Promise Reply

/-- The state a session's GUI side and dispatcher share. -/
structure SessionState where
  /-- The open document: id, bytes and whether the repair path is allowed (`none`: none). -/
  doc : Option (Nat × ByteArray × Bool) := none
  /-- Requests not answered yet, besides the one in flight. -/
  queue : Array Queued := #[]
  /-- Ids the GUI cancelled (cleared when the dispatcher takes the next request). -/
  cancelled : List Nat := []
  /-- The next request id. -/
  nextId : Nat := 0
  /-- Resolved to wake the idle dispatcher. -/
  wake : Option (IO.Promise Unit) := none
  /-- `shutdown` was called. -/
  closed : Bool := false
  /-- Workers spawned so far. -/
  spawns : Nat := 0
  /-- Requests that hit the deadline. -/
  timeouts : Nat := 0
  /-- Requests stopped by a kill (cancelled or preempted). -/
  kills : Nat := 0

/-- How a session runs its workers. -/
structure SessionConfig where
  /-- The worker executable (absolute path). -/
  exe : System.FilePath
  /-- Frame caps, and the limits the worker parses and renders with (`--limits=`). -/
  limits : Limits := {}
  /-- The worker's font search (task 12.2d; its `limits` field is ignored). -/
  start : Protocol.StartConfig := {}
  /-- A request (or the open of a spawned worker) not answered within this many ms kills the
  worker. -/
  deadlineMs : Nat := 20000
  /-- A request in flight is killed for a cancellation or a more urgent request only after it
  ran this many ms (a respawn costs about as much as a short render). -/
  preemptMs : Nat := 250
  /-- A `prio` 0 request preempts a `prio` 0 request in flight only when submitted this many ms
  after it (pages of one spread are submitted together). -/
  newerMs : Nat := 100

/-- A worker session (see the section doc). -/
structure Session where
  /-- Configuration. -/
  cfg : SessionConfig
  /-- Shared state. -/
  state : IO.Ref SessionState
  /-- The running worker and its document id (dispatcher only). -/
  client : IO.Ref (Option (Client × Nat))
  /-- Environment of the workers spawned next (test hooks only; empty otherwise). -/
  env : IO.Ref (Array (String × Option String))
  /-- The dispatcher task. -/
  task : IO.Ref (Option (Task (Except IO.Error Unit)))

/-- Index of the request to answer next: lowest `prio`, then lowest id. -/
def bestIndex (qs : Array Queued) : Option Nat := Id.run do
  let mut best : Option (Nat × Nat × Nat) := none
  let mut i := 0
  for q in qs do
    match best with
    | some (p, d, _) => if q.prio < p || (q.prio == p && q.id < d) then best := some (q.prio, q.id, i)
    | none => best := some (q.prio, q.id, i)
    i := i + 1
  return best.map (·.2.2)

/-- Takes the next request off the queue (and the document), dropping cancelled ones and those
for another document; with none left, records `w` as the wake-up promise. -/
def Session.next (s : Session) (w : IO.Promise Unit) :
    IO (Option (Queued × (Nat × ByteArray × Bool))) := do
  let (dropped, pick) ← s.state.modifyGet fun st =>
    let cur := st.doc.map (·.1)
    let (dead, live) := st.queue.partition fun q =>
      st.closed || st.cancelled.contains q.id || cur != some q.doc
    match (bestIndex live).bind (fun i => (live[i]?).map (i, ·)), st.doc with
    | some (i, q), some d =>
      ((dead, some (q, d)), { st with queue := live.eraseIdxIfInBounds i, cancelled := [] })
    | _, _ => ((dead, none), { st with queue := live, cancelled := [], wake := some w })
  for q in dropped do q.promise.resolve .cancelled
  return pick

/-- Why a request in flight is stopped. -/
inductive Abort where
  /-- Its document is no longer open, or the session closed. -/
  | stop
  /-- The GUI cancelled it. -/
  | cancel
  /-- A more urgent request waits. -/
  | preempt

/-- Whether the request `q`, in flight for `elapsed` ms, must be stopped. -/
def Session.abortCheck (s : Session) (q : Queued) (elapsed : Nat) : IO (Option Abort) := do
  let st ← s.state.get
  let cur := st.doc.map (·.1)
  if st.closed || cur != some q.doc then return some .stop
  if elapsed < s.cfg.preemptMs then return none
  if st.cancelled.contains q.id then return some .cancel
  let urgent (o : Queued) : Bool :=
    !st.cancelled.contains o.id && cur == some o.doc &&
      (o.prio < q.prio || (o.prio == 0 && q.prio == 0 && o.submitted ≥ q.submitted + s.cfg.newerMs))
  if st.queue.any urgent then return some .preempt
  return none

/-- Drops the running worker (killed and reaped). -/
def Session.dropClient (s : Session) : IO Unit := do
  if let some (c, _) ← s.client.get then discard c.kill
  s.client.set none

/-- The worker for document `d`: the running one when it serves `d` and is alive, else a new
one (spawned with `env`, opened with `d`'s bytes within the deadline). -/
def Session.ensureClient (s : Session) (d : Nat × ByteArray × Bool) :
    IO (Except ClientError Client) := do
  if let some (c, id) ← s.client.get then
    if id == d.1 && (← c.exited?).isNone then return .ok c
    s.dropClient
  let env ← s.env.get
  let r ← try
      let c ← spawn s.cfg.exe s.cfg.limits env s.cfg.start
      pure (Except.ok c)
    catch e => pure (Except.error s!"cannot start the document worker: {e}")
  match r with
  | .error m => return .error (.exited m)
  | .ok c =>
    s.state.modify fun st => { st with spawns := st.spawns + 1 }
    match ← c.request (.openDoc d.2.1 d.2.2) (some s.cfg.deadlineMs) with
    | .ok (.docInfo ..) =>
      s.client.set (some (c, d.1))
      return .ok c
    | .ok (.error _ msg) =>
      discard c.kill
      return .error (.exited s!"the document worker could not open the document: {msg}")
    | .ok _ =>
      discard c.kill
      return .error (.exited "the document worker answered the open with another message")
    | .error e =>
      discard c.kill
      if let .timeout := e then s.state.modify fun st => { st with timeouts := st.timeouts + 1 }
      return .error e

/-- Answers `q` for document `d` (see the section doc: deadline, cancellation, preemption). -/
def Session.serve (s : Session) (q : Queued) (d : Nat × ByteArray × Bool) : IO Unit := do
  match ← s.ensureClient d with
  | .error e => q.promise.resolve (.failed e)
  | .ok c =>
    match Protocol.frameRequest c.limits q.req with
    | none => q.promise.resolve (.failed .notEncodable)
    | some f =>
      let t0 ← IO.monoNanosNow
      match ← c.sendRaw f with
      | .error e =>
        s.dropClient
        q.promise.resolve (.failed e)
      | .ok () =>
        let task ← IO.asTask c.readResponse .dedicated
        let start ← IO.monoMsNow
        let mut abort : Option Abort := none
        let mut timedOut := false
        repeat
          if ← IO.hasFinished task then break
          let el := (← IO.monoMsNow) - start
          if el ≥ s.cfg.deadlineMs then
            timedOut := true
            break
          if let some a ← s.abortCheck q el then
            abort := some a
            break
          IO.sleep 1
        if timedOut || abort.isSome then
          s.dropClient
          discard <| IO.wait task
          if timedOut then
            s.state.modify fun st => { st with timeouts := st.timeouts + 1 }
            q.promise.resolve (.failed .timeout)
          else
            s.state.modify fun st => { st with kills := st.kills + 1 }
            match abort with
            | some .preempt =>
              s.state.modify fun st => { st with queue := st.queue.push { q with prio := max 1 q.prio } }
            | _ => q.promise.resolve .cancelled
        else
          let ns := (← IO.monoNanosNow) - t0
          match ← IO.wait task with
          | .ok (.ok r) => q.promise.resolve (.response r ns)
          | .ok (.error e) =>
            s.dropClient
            q.promise.resolve (.failed e)
          | .error e =>
            s.dropClient
            q.promise.resolve (.failed (.exited (toString e)))

/-- The dispatcher loop (a dedicated task per session, started by `Session.start`). -/
def Session.run (s : Session) : IO Unit := do
  repeat
    let w ← IO.Promise.new
    match ← s.next w with
    | some (q, d) =>
      try s.serve q d
      catch e =>
        s.dropClient
        q.promise.resolve (.failed (.exited s!"client error: {e}"))
    | none =>
      let st ← s.state.get
      if let some (_, id) ← s.client.get then
        if st.closed || st.doc.map (·.1) != some id then s.dropClient
      if st.closed then return
      discard <| IO.wait w.result?

/-- **Starts a session** (no worker yet: the first request spawns it). -/
def Session.start (cfg : SessionConfig) : IO Session := do
  let s : Session := { cfg, state := ← IO.mkRef {}, client := ← IO.mkRef none,
                       env := ← IO.mkRef #[], task := ← IO.mkRef none }
  let t ← IO.asTask s.run .dedicated
  s.task.set (some t)
  return s

/-- Wakes the dispatcher if it is idle. -/
def Session.wakeUp (w : Option (IO.Promise Unit)) : IO Unit := do
  if let some p := w then p.resolve ()

/-- **Queues** `req` for document `doc` with priority `prio`; returns its id and the task of
its reply (never blocks; `cancelled` at once after `shutdown`). -/
def Session.submit (s : Session) (doc : Nat) (req : Protocol.Request) (prio : Nat) :
    IO (Nat × Task Reply) := do
  let p ← IO.Promise.new
  let now ← IO.monoMsNow
  let (id, closed, wake) ← s.state.modifyGet fun st =>
    let q : Queued := { id := st.nextId, doc, req, prio, submitted := now, promise := p }
    if st.closed then ((st.nextId, true, none), { st with nextId := st.nextId + 1 })
    else ((st.nextId, false, st.wake),
      { st with queue := st.queue.push q, nextId := st.nextId + 1, wake := none })
  if closed then p.resolve .cancelled
  Session.wakeUp wake
  return (id, p.resultD .cancelled)

/-- **Cancels** request `id`: dropped if still queued, killed after `preemptMs` if in flight. -/
def Session.cancel (s : Session) (id : Nat) : IO Unit :=
  s.state.modify fun st =>
    if st.cancelled.contains id then st else { st with cancelled := id :: st.cancelled }

/-- **Raises** queued request `id` to priority `prio` when that is more urgent, as if submitted
now (a page asked for as a neighbour becomes the current page: it may then preempt). -/
def Session.raise (s : Session) (id prio : Nat) : IO Unit := do
  let now ← IO.monoMsNow
  s.state.modify fun st =>
    { st with queue := st.queue.map fun q =>
        if q.id == id && prio < q.prio then { q with prio, submitted := now } else q }

/-- **Sets the open document** (`none`: no document): its id, bytes and whether the repair path
is allowed. Requests for the previous one are dropped; its worker is killed. -/
def Session.setDoc (s : Session) (doc : Option (Nat × ByteArray × Bool)) : IO Unit := do
  let wake ← s.state.modifyGet fun st => (st.wake, { st with doc, wake := none })
  Session.wakeUp wake

/-- Sets the environment of the workers spawned from now on (test hooks). -/
def Session.setEnv (s : Session) (env : Array (String × Option String)) : IO Unit :=
  s.env.set env

/-- **Closes** the session: every request is dropped, the worker killed, and the dispatcher
ends (waited for at most `waitMs`). -/
def Session.shutdown (s : Session) (waitMs : Nat := 2000) : IO Unit := do
  let wake ← s.state.modifyGet fun st => (st.wake, { st with closed := true, wake := none })
  Session.wakeUp wake
  if let some t ← s.task.get then
    let deadline := (← IO.monoMsNow) + waitMs
    while !(← IO.hasFinished t) && (← IO.monoMsNow) < deadline do IO.sleep 2

end SafePdf.Shell.Worker
