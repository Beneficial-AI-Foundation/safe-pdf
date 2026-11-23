import SafePdf.Shell.Worker.Protocol

/-!
# Document worker: test hooks (task 12.2c)

Plan.md §6 Phase 12, "Restricted, stoppable document worker". Test-only behaviour of the
`worker` executable, called by `SafePdf.Shell.Worker.Serve.loop` before it answers a request.

* **Stall** (`SAFEPDF_WORKER_TEST_STALL_MS=N`): before answering a `render` request the worker
  sleeps `N` ms (at most ten minutes), so the viewer's smoke test (`scripts/viewer-smoke.sh`,
  case 12.2c) can check that the GUI keeps handling events while a render runs and that a
  render past the deadline kills the worker. The client starts workers with an empty
  environment (`Worker.spawn`); only the viewer's smoke mode puts this variable into it. This
  is the only environment variable the worker reads.
-/

namespace SafePdf.Shell.Worker.TestHooks

/-- The longest stall the hook makes (ms). -/
def maxStallMs : Nat := 600000

/-- **Before answering `req`**: the stall hook (see the module doc); nothing otherwise. -/
def beforeRequest (req : Protocol.Request) : IO Unit := do
  match req with
  | .render .. =>
    if let some v ← IO.getEnv "SAFEPDF_WORKER_TEST_STALL_MS" then
      if let some ms := v.toNat? then
        IO.sleep (min ms maxStallMs).toUInt32
  | _ => pure ()

end SafePdf.Shell.Worker.TestHooks
