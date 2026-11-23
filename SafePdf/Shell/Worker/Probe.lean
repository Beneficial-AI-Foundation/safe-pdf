import SafePdf.Shell.Worker.Client
import SafePdf.Shell.Worker.Serve
import SafePdf.Shell.Worker.Sandbox

/-!
# Worker confinement probe (task 12.2b; test-only executable `worker-probe`)

Plan.md §6 Phase 12, "Restricted, stoppable document worker"; milestone M12: "a platform
test shows the worker cannot open unrelated files, reach the network or see the token". The
probe runs the worker's own startup (`Sandbox.prepare`: environment check, fonts,
confinement) and then tries what a compromised worker would try. It is a separate
executable so that the production `worker` has no request that opens a path, connects or
spawns; it is linked with the same confinement object, compiled with the TCP probe added.

**Parent mode** `worker-probe --parent PDF` (run by `scripts/worker-confinement-test.sh` and
the `worker-confinement` suite, with `SAFEPDF_PROBE_TOKEN` set in its environment):
opens a listening TCP socket on 127.0.0.1, then starts itself twice and reports both:

* the **confined** child through `Worker.spawn` — exactly the client's spawn (empty
  environment, cwd `/`) — every probe must be **denied** and the render must work;
* an **unconfined control** child with the parent's environment inherited, which skips the
  environment check and the sandbox: every probe must be **allowed** (shows the probes can
  detect access at all).

**Child mode** (no arguments): reads one line `MODE PORT TOKENVAR PDF` from stdin, reads the
PDF bytes (before confinement, as the GUI would send them), runs `prepare`, then probes:
read `/etc/hosts`; re-read a font file the startup itself read; create a file in `/tmp`;
list `/`; connect to the parent's port; read the token variable; spawn `/bin/echo` — and,
expected to work in both modes, run a dedicated thread and render page 1 of the PDF through
`Serve.answer`. One line per probe, then `verdict: ok` or
`verdict: FAIL`; exit 0 iff every probe met the mode's expectation.
-/

namespace SafePdf.Shell.Worker.Probe

open SafePdf SafePdf.Shell.Worker

/-- Raw binding (probe object only): connect to 127.0.0.1:`port`; `"ok: connected"` or the
failing call and error. -/
@[extern "safepdf_probe_tcp"]
opaque probeTcp (port : UInt32) : IO String

/-- Raw binding (probe object only): listen on an ephemeral 127.0.0.1 port (close-on-exec);
the port, or 0. -/
@[extern "safepdf_probe_listen"]
opaque listen : IO UInt32

/-- The environment variable the parent holds and the confined child must not see. -/
def tokenVar : String := "SAFEPDF_PROBE_TOKEN"

/-- Run an action; `ok detail` if it succeeded, the error text otherwise. -/
def attempt (act : IO String) : IO (Bool × String) := do
  try return (true, ← act) catch e => return (false, toString e)

/-- One probe line; returns whether the outcome met the expectation (`expectAllowed`). -/
def report (name : String) (expectAllowed : Bool) (r : Bool × String) : IO Bool := do
  let (allowed, detail) := r
  let detail := (detail.replace "\n" " ").take 160
  IO.println s!"probe {name}: {if allowed then "ALLOWED" else "denied"} ({detail})"
  return allowed == expectAllowed

/-- Child mode: see the module doc. -/
def child : IO UInt32 := do
  let stdin ← IO.getStdin
  let line := (← stdin.getLine).trimAscii.toString
  let mode :: portStr :: tok :: rest := line.splitOn " "
    | IO.println s!"bad config line: {line}"; return 2
  let some port := portStr.toNat? | IO.println s!"bad port: {portStr}"; return 2
  let pdf := " ".intercalate rest
  let confined := mode == "confined"
  let pdfBytes ← IO.FS.readBinFile pdf
  let limits := Limits.default
  let p ← match ← Sandbox.prepare limits confined with
    | .ok p => pure p
    | .error f =>
      IO.println s!"startup: FAILED ({f.message})"
      IO.println "verdict: FAIL"
      return f.exitCode.toUInt32
  IO.println s!"mode: {mode}; confinement: {p.mechanism.getD "none (control)"}; \
    {p.faces.length} substitute faces read before confinement"
  let want := !confined
  let mut ok := true
  ok := (← report "read /etc/hosts" want (← attempt do
    let b ← IO.FS.readBinFile "/etc/hosts"; return s!"{b.size} bytes")) && ok
  match p.faces.head? with
  | some f =>
    ok := (← report s!"re-read font {f.path}" want (← attempt do
      let b ← IO.FS.readBinFile f.path; return s!"{b.size} bytes")) && ok
  | none => IO.println "probe re-read font: skipped (no substitute font found)"
  let tmp : System.FilePath := s!"/tmp/safepdf-worker-probe-{← IO.Process.getPID}"
  ok := (← report s!"create {tmp}" want (← attempt do
    IO.FS.writeFile tmp "probe"; IO.FS.removeFile tmp; return "created and removed")) && ok
  ok := (← report "list /" want (← attempt do
    let es ← System.FilePath.readDir "/"; return s!"{es.size} entries")) && ok
  ok := (← report s!"connect 127.0.0.1:{port}" want (← do
    let r ← probeTcp port.toUInt32
    pure (r.startsWith "ok", r))) && ok
  ok := (← report s!"read ${tok}" want (← do
    match ← IO.getEnv tok with
    | some v => pure (true, s!"visible, {v.length} chars")
    | none => pure (false, s!"unset; environment has {← Sandbox.envCount} entries"))) && ok
  ok := (← report "spawn /bin/echo" want (← attempt do
    let o ← IO.Process.output { cmd := "/bin/echo", args := #["probe"] }
    return s!"exit {o.exitCode}, stdout {o.stdout.trimAscii}")) && ok
  -- What the worker needs must still work after confinement: a thread (Lean's dedicated
  -- task; the client-side 12.2c design may use them) and a render.
  ok := (← report "run a dedicated thread" true (← attempt do
    let t ← IO.asTask (pure (21 * 2 : Nat)) .dedicated
    match ← IO.wait t with
    | .ok v => return s!"returned {v}"
    | .error e => throw e)) && ok
  let st : Serve.State := { subst := p.subst }
  let (st, r1) := Serve.answer st (.openDoc pdfBytes true)
  let (_, r2) := Serve.answer st (.render 0 1 0)
  let rendered := match r1, r2 with
    | .docInfo n _ _, .image w h data => some s!"{n} pages; page 1 {w}x{h}, {data.size} bytes"
    | _, _ => none
  ok := (← report "render page 1" true (rendered.isSome, rendered.getD "render failed")) && ok
  IO.println s!"verdict: {if ok then "ok" else "FAIL"}"
  return if ok then 0 else 1

/-- Run one child: write its config line, collect its stdout, reap it. -/
def runChild (c : IO.Process.Child Worker.workerStdio) (config : String) :
    IO (String × Option UInt32) := do
  c.stdin.putStr (config ++ "\n")
  c.stdin.flush
  let out ← c.stdout.readToEnd
  let code ← try some <$> c.wait catch _ => pure none
  return (out, code)

/-- Parent mode: see the module doc. Returns the exit status. -/
def parent (pdf : String) : IO UInt32 := do
  let some tokenVal ← IO.getEnv tokenVar
    | IO.println s!"parent: set {tokenVar} in the environment first"; return 2
  let pdf ← IO.FS.realPath pdf
  let self ← IO.appPath
  let port ← listen
  if port == 0 then IO.println "parent: could not listen on 127.0.0.1"; return 2
  IO.println s!"parent: {tokenVar} is set ({tokenVal.length} chars); listening on \
    127.0.0.1:{port}"
  -- Confined: exactly the client's spawn (empty environment, cwd `/`).
  let c ← Worker.spawn self
  let (out1, code1) ← runChild c.child s!"confined {port} {tokenVar} {pdf}"
  IO.println s!"--- confined child (Worker.spawn: empty environment, cwd /), exit {code1}"
  IO.print out1
  -- Control: environment inherited, no sandbox.
  let ctl ← IO.Process.spawn
    { toStdioConfig := Worker.workerStdio, cmd := self.toString, args := #[], cwd := some "/" }
  let (out2, code2) ← runChild ctl s!"unconfined {port} {tokenVar} {pdf}"
  IO.println s!"--- unconfined control child (environment inherited, no sandbox), exit {code2}"
  IO.print out2
  let ok := code1 == some 0 && code2 == some 0
  IO.println s!"probe result: {if ok then "PASS" else "FAIL"}"
  return if ok then 0 else 1

end SafePdf.Shell.Worker.Probe

/-- `worker-probe` (child mode) or `worker-probe --parent PDF`. -/
def main (args : List String) : IO UInt32 := do
  let code ← match args with
    | [] => SafePdf.Shell.Worker.Probe.child
    | ["--parent", pdf] => SafePdf.Shell.Worker.Probe.parent pdf
    | _ => do
      IO.eprintln "usage: worker-probe --parent PDF   (no arguments: child mode, config on stdin)"
      pure 2
  IO.Process.exit code.toUInt8
