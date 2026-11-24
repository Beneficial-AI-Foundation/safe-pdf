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
-/

/-- The worker: confine, then serve requests on stdin/stdout until end of input, `quit` or an
oversized frame. Exits through `IO.Process.exit` (no dedicated tasks to join). -/
def main (args : List String) : IO UInt32 := do
  let limits := SafePdf.Limits.default
  match ← SafePdf.Shell.Worker.Sandbox.prepare limits with
  | .error f =>
    IO.eprintln f.message
    IO.Process.exit f.exitCode
  | .ok p =>
    let code ← SafePdf.Shell.Worker.Serve.loop limits p.subst
      (SafePdf.Shell.Worker.TestHooks.stallOfArgs args)
    IO.Process.exit code.toUInt8
