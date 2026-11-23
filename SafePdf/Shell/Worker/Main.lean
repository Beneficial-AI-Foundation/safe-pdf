import SafePdf.Shell.Worker.Serve

/-!
# The document worker executable (task 12.2a)

Plan.md §6 Phase 12, "Restricted, stoppable document worker". The `worker` executable's
entry point; the request loop and its design are in `SafePdf.Shell.Worker.Serve`.
-/

/-- The worker: serve requests on stdin/stdout until end of input, `quit` or an oversized
frame. Exits through `IO.Process.exit` (no dedicated tasks to join). -/
def main : IO UInt32 := do
  let code ← SafePdf.Shell.Worker.Serve.loop SafePdf.Limits.default
  IO.Process.exit code.toUInt8
