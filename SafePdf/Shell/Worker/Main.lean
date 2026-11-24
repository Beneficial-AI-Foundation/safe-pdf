import SafePdf.Shell.Worker.Serve
import SafePdf.Shell.Worker.TestHooks
import SafePdf.Shell.Worker.Sandbox

/-!
# The document worker executable (tasks 12.2a, 12.2b)

Plan.md §6 Phase 12, "Restricted, stoppable document worker". The `worker` executable's
entry point: startup and confinement (`SafePdf.Shell.Worker.Sandbox.prepare`: empty
environment required, substitute fonts read, sandbox installed) **before** the first request
is read, then the request loop (`SafePdf.Shell.Worker.Serve`). A worker that cannot confine
itself exits (status 3: non-empty environment, 4: no sandbox) without reading a request.

Task 12.2d: the startup configuration (limits, font search, test stall) comes as flags
(`Protocol.StartConfig.ofArgs`), parsed **before** startup, since the fonts are read before
confinement and the environment must stay empty. An argument the worker does not understand
ends it with status 5 before it reads anything.
-/

/-- The worker: confine, then serve requests on stdin/stdout until end of input, `quit` or an
oversized frame. Exits through `IO.Process.exit` (no dedicated tasks to join). -/
def main (args : List String) : IO UInt32 := do
  match SafePdf.Shell.Worker.Protocol.StartConfig.ofArgs args with
  | .error m =>
    IO.eprintln s!"safe-pdf worker: {m}"
    IO.Process.exit 5
  | .ok start =>
  match ← SafePdf.Shell.Worker.Sandbox.prepare start with
  | .error f =>
    IO.eprintln f.message
    IO.Process.exit f.exitCode
  | .ok p =>
    let code ← SafePdf.Shell.Worker.Serve.loop start.limits p.subst
      (min start.stallMs SafePdf.Shell.Worker.TestHooks.maxStallMs)
    IO.Process.exit code.toUInt8
