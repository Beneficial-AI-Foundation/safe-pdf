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

/-- **Start a worker** from the executable `exe` (an absolute path). -/
def spawn (exe : System.FilePath) (limits : Limits := {}) : IO Client := do
  let child ← IO.Process.spawn
    { toStdioConfig := workerStdio, cmd := exe.toString, args := #[], cwd := some "/"
      env := #[], inheritEnv := false }
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

end SafePdf.Shell.Worker
