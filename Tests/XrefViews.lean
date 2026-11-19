import SafePdf
import SafePdf.Shell.Views.Xref
import Tests.Golden

/-!
# Golden tests of the `xref`, `revisions` and `repair` inspector views (task 2.8)

Each input under `Tests/golden/xref/` is rendered with the deterministic text forms of the
three views of `SafePdf.Shell.Views.Xref` (no timings) under `Limits.default`, separated by
`--- <view>` lines, and compared with `<input>.expected` by `Tests.Golden.runCase`
(Plan.md §6 Phase 2, milestone M2 inspector views). `SAFEPDF_GOLDEN_UPDATE=1` regenerates.
-/

namespace SafePdf.Tests.XrefViews

open SafePdf.Shell.Views.Xref

/-- Directory of the inputs. -/
def dir : System.FilePath := Tests.Golden.goldenRoot / "xref"

/-- Render the three views for one input (the path is shown as `input`). -/
def render (bytes : ByteArray) : String :=
  let l := Limits.default
  let rep := xrefReport l bytes
  let lines :=
    ["--- xref"] ++ xrefText "input" rep ++
    ["--- revisions"] ++ revisionsText "input" rep.trace rep ++
    ["--- repair"] ++ repairText "input" l (repairReport l bytes)
  "\n".intercalate lines ++ "\n"

/-- Run the suite; returns the number of failures. -/
def run : IO Nat := do
  let update := (← IO.getEnv Tests.Golden.updateEnvVar) == some "1"
  if !(← dir.isDir) then
    IO.println s!"  FAIL xref views: directory {dir} not found (run from the repo root)"
    return 1
  let inputs := ((← dir.readDir).map (·.path)).toList.filter Tests.Golden.isInput
  let inputs := inputs.toArray.qsort (fun a b => a.toString < b.toString)
  if inputs.isEmpty then
    IO.println s!"  FAIL xref views: no input files in {dir}"
    return 1
  let mut c : Tests.Golden.Counts := {}
  for input in inputs do
    c ← Tests.Golden.runCase update render input c
  if update then IO.println s!"  xref views: wrote {c.written} .expected file(s)"
  else IO.println s!"  xref views: {c.cases} case(s), {c.failures} failure(s)"
  return c.failures

end SafePdf.Tests.XrefViews
