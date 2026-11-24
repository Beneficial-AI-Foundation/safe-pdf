import SafePdf.Shell.Worker.Protocol

/-!
# Document worker: test hooks (task 12.2c)

Plan.md §6 Phase 12, "Restricted, stoppable document worker". Test-only behaviour of the
`worker` executable, called by `SafePdf.Shell.Worker.Serve.loop` before it answers a request.

* **Stall** (command-line flag `--test-stall-ms=N`): before answering a `render` request the
  worker sleeps `N` ms (at most ten minutes), so the viewer's smoke test
  (`scripts/viewer-smoke.sh`, case 12.2c) can check that the GUI keeps handling events while a
  render runs and that a render past the deadline kills the worker. A flag, not an environment
  variable: the worker refuses a non-empty environment (task 12.2b). The flag can only slow the
  worker down; it changes nothing about its confinement or its answers.
-/

namespace SafePdf.Shell.Worker.TestHooks

/-- The longest stall the hook makes (ms). -/
def maxStallMs : Nat := 600000

/-- The stall requested on the command line (`--test-stall-ms=N`, capped at `maxStallMs`); 0
without the flag. -/
def stallOfArgs (args : List String) : Nat :=
  match args.findSome? (fun a => (a.dropPrefix? "--test-stall-ms=").bind (·.toString.toNat?)) with
  | some ms => min ms maxStallMs
  | none => 0

#guard stallOfArgs [] == 0
#guard stallOfArgs ["--test-stall-ms=1500"] == 1500
#guard stallOfArgs ["--test-stall-ms=99999999"] == maxStallMs

/-- **Before answering `req`**: sleep `stallMs` ms before a `render` (the stall hook, see the
module doc); nothing otherwise. -/
def beforeRequest (stallMs : Nat) (req : Protocol.Request) : IO Unit := do
  match req with
  | .render .. => if stallMs > 0 then IO.sleep stallMs.toUInt32
  | _ => pure ()

end SafePdf.Shell.Worker.TestHooks
