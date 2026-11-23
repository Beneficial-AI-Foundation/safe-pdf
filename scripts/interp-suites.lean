import Tests.Main

/-!
# Interpreted test runner (task 12.6, Plan.md §6 Phase 12 "Independent verification")

Run by `scripts/compiled-vs-interpreted.sh` as `lake env lean scripts/interp-suites.lean`.
The `#eval` below runs the registered test suites (`SafePdf.Tests.suites`, `Tests/Main.lean`)
in Lean's **IR interpreter**: the imported project code is loaded from the `.olean` files and
interpreted, not executed from the natively compiled `tests` binary. Comparing the two
outputs probes the unverified Lean → C code generator (`docs/safety.md` §5, item 6).

Environment (read at elaboration time):
* `SAFEPDF_INTERP_OUT` (required): file that receives the suites' standard output, in the
  same format as `lake exe tests` (each suite's lines followed by its `[PASS]`/`[FAIL]` line).
  `#eval` captures standard output into an info message, so the output goes to a file.
* `SAFEPDF_SUITES` (optional): comma-separated suite names (no spaces); empty or unset runs every suite.
  Unknown names are reported as `[MISSING] name` so a typo cannot pass silently.

This file is outside the library and is never imported.
-/

open SafePdf.Tests in
#eval show IO Unit from do
  let some outPath ← IO.getEnv "SAFEPDF_INTERP_OUT"
    | throw (IO.userError "SAFEPDF_INTERP_OUT is not set")
  let sel := ((← IO.getEnv "SAFEPDF_SUITES").getD "").splitOn ","
    |>.filter (!·.isEmpty)
  let chosen := if sel.isEmpty then suites else suites.filter (sel.contains ·.name)
  IO.FS.withFile outPath .write fun h => do
    let out := IO.FS.Stream.ofHandle h
    let old ← IO.setStdout out
    try
      for s in chosen do
        let f ← s.run
        IO.println s!"[{if f == 0 then "PASS" else "FAIL"}] {s.name} ({f} failures)"
      for n in sel do
        unless suites.any (·.name == n) do
          IO.println s!"[MISSING] {n}"
    finally
      out.flush
      discard <| IO.setStdout old
