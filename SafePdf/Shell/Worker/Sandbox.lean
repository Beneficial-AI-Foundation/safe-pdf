import SafePdf.Shell.Worker.Wire

/-!
# Document worker confinement (task 12.2b)

Plan.md §6 Phase 12, "Restricted, stoppable document worker". Lean side of
`c/worker_sandbox.c` (trusted, unverified shell). `prepare` is the worker's whole startup,
in this order:

1. **Environment check**: the worker refuses to serve when its environment is not empty
   (the client spawns it with `env := #[]`, `inheritEnv := false`). A worker started by
   hand from a shell therefore exits with status 3 instead of carrying `$HOME`, tokens or
   credentials into the process that parses untrusted bytes.
2. **Fonts**: the substitute fonts are read from the fixed system font directories
   (`Worker.workerFaces`), every file in full.
3. **Confinement** (`confine`): macOS seatbelt (`(deny default)`), Linux seccomp-bpf
   allowlist with `no_new_privs`; any failure (including an unsupported platform) is an
   error and the worker exits with status 4 — it never serves unconfined. There is no
   debug escape in the `worker` executable (no flag, no environment variable); the
   test-only `worker-probe` executable has an unconfined control mode.

Only after `prepare` succeeds does the worker read its first request. The externs exist only
in the executables that link the shim object (`worker`, `worker-probe`; see `lakefile.lean`),
so this module must not be imported by `SafePdf.lean`, the inspector or the tests.
-/

namespace SafePdf.Shell.Worker.Sandbox

open SafePdf SafePdf.Core

/-- Raw binding: the number of entries in the process environment (`environ`). -/
@[extern "safepdf_worker_env_count"]
opaque envCount : IO UInt32

/-- Raw binding: **confine the process for good** (macOS `sandbox_init`, Linux seccomp with
`PR_SET_NO_NEW_PRIVS`). Returns a one-line description of the mechanism; throws when the
sandbox cannot be installed or the platform has none. Irreversible. -/
@[extern "safepdf_worker_confine"]
opaque confine : IO String

/-- What the worker holds after startup. -/
structure Prepared where
  /-- The substitute faces, read before confinement. -/
  faces : List Fonts.Found
  /-- The substitute-font table of `faces`. -/
  subst : Raster.Subst.SubstFonts
  /-- How the process is confined (`none`: not confined; only the probe's control mode). -/
  mechanism : Option String

/-- Why startup failed, with the worker's exit status. -/
inductive Failure where
  /-- The environment has `n` entries (exit 3). -/
  | environment (n : Nat)
  /-- Confinement could not be installed (exit 4). -/
  | confinement (msg : String)

/-- The exit status of a startup failure. -/
def Failure.exitCode : Failure → UInt8
  | .environment _ => 3
  | .confinement _ => 4

/-- A one-line message for stderr. -/
def Failure.message : Failure → String
  | .environment n => s!"safe-pdf worker: refusing to serve: the environment has {n} \
      entries (start the worker with an empty environment)"
  | .confinement m => s!"safe-pdf worker: refusing to serve unconfined: {m}"

/-- **The worker's startup**: check that the environment is empty, read the substitute
fonts, then confine the process. `confined := false` (the probe's control mode only) skips
the environment check and the confinement. -/
def prepare (limits : Limits) (confined : Bool := true) : IO (Except Failure Prepared) := do
  if confined then
    let n ← envCount
    if n != 0 then return .error (.environment n.toNat)
  let faces ← workerFaces
  let subst := Fonts.tableOf limits faces
  if !confined then return .ok { faces, subst, mechanism := none }
  try
    let m ← confine
    return .ok { faces, subst, mechanism := some m }
  catch e => return .error (.confinement (toString e))

end SafePdf.Shell.Worker.Sandbox
