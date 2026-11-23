/-!
# Worker confinement suite (task 12.2b)

Plan.md §6 Phase 12, "Restricted, stoppable document worker"; milestone M12 "a platform
test shows the worker cannot open unrelated files, reach the network or see the token".
Drives the built executables (default targets `worker` and `worker-probe`):

* the production `worker` started with a **non-empty environment** refuses to serve: exit
  status 3, nothing on stdout;
* `worker-probe --parent` (see `SafePdf.Shell.Worker.Probe`), run with
  `SAFEPDF_PROBE_TOKEN` in its environment: the child started exactly like the client starts
  the worker is confined (file reads, a file re-read after startup, file creation, directory
  listing, a TCP connect to 127.0.0.1, the token variable and process spawning all denied;
  a thread and a render still work), and the unconfined control child is allowed all of
  them. `scripts/worker-confinement-test.sh` runs the same probe and prints every line.

Rendering through the confined worker is also covered by the `worker` suite (renders
byte-equal to in-process rendering), since every `worker` now confines itself.
-/

namespace SafePdf.Tests.WorkerConfinement

/-- Report a failed check. -/
def check (what : String) (ok : Bool) : IO Nat := do
  if ok then return 0
  IO.println s!"  FAIL worker-confinement: {what}"
  return 1

/-- A built executable (absolute path), if present. -/
def exe (name : String) : IO (Option System.FilePath) := do
  let p : System.FilePath := ".lake/build/bin" / name
  if ← p.pathExists then return some (← IO.FS.realPath p) else return none

/-- The production worker refuses a non-empty environment (the test runner's own, plus a
token). Not `inheritEnv := false` with a non-empty `env`: in Lean 4.36 that spawn crashes
the child (SIGSEGV even for `/usr/bin/env`, task 12.2b). -/
def refusesEnvironment (w : System.FilePath) : IO Nat := do
  let out ← IO.Process.output
    { cmd := w.toString, cwd := some "/", env := #[("SAFEPDF_PROBE_TOKEN", some "secret")],
      stdin := .null }
  let mut f := 0
  f := f + (← check s!"worker with an environment exits 3 (got {out.exitCode})" (out.exitCode == 3))
  f := f + (← check "worker with an environment writes nothing to stdout" out.stdout.isEmpty)
  return f

/-- The probe: every confined attempt denied, every control attempt allowed. -/
def probe (p : System.FilePath) : IO Nat := do
  let pdf ← IO.FS.realPath "Tests/golden/text/latin.pdf"
  let out ← IO.Process.output
    { cmd := p.toString, args := #["--parent", pdf.toString], stdin := .null
      env := #[("SAFEPDF_PROBE_TOKEN", some "probe-token-value")] }
  let lines := out.stdout.splitOn "\n"
  -- Split at the control child's header: the confined part comes first.
  let (conf, ctl) := lines.span (!·.startsWith "--- unconfined")
  let probes (ls : List String) := ls.filter (·.startsWith "probe ")
  let denied (ls : List String) := (probes ls).filter (·.contains ": denied (")
  let mut f := 0
  f := f + (← check s!"probe exits 0 (got {out.exitCode}):\n{out.stdout}{out.stderr}"
    (out.exitCode == 0))
  f := f + (← check "probe reports PASS" (lines.contains "probe result: PASS"))
  -- Seven attempts must be denied in the confined child (six if no substitute font exists).
  f := f + (← check s!"confined child: ≥ 6 denied probes (got {(denied conf).length})"
    ((denied conf).length ≥ 6))
  f := f + (← check "control child: no denied probe" ((denied ctl).isEmpty))
  f := f + (← check "confined child: render still works"
    (conf.any (·.startsWith "probe render page 1: ALLOWED")))
  return f

/-- Run the suite. -/
def run : IO Nat := do
  let some w ← exe "worker"
    | check "worker executable at .lake/build/bin/worker (run `lake build worker`)" false
  let some p ← exe "worker-probe"
    | check "probe executable at .lake/build/bin/worker-probe (run `lake build worker-probe`)"
        false
  return (← refusesEnvironment w) + (← probe p)

end SafePdf.Tests.WorkerConfinement
