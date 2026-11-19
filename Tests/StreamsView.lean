import SafePdf
import SafePdf.Shell.Views.Streams
import Tests.Golden

/-!
# Golden tests of the `streams` inspector view (task 3.7)

Each input under `Tests/golden/streams/` (tiny generated PDFs: Flate, ASCIIHex→Flate, a DCT
placeholder, indirect `/Filter` and `/DecodeParms`, a bad zlib stream, an unknown filter) is
rendered with the deterministic text form of `SafePdf.Shell.Views.Streams` (no timings),
twice: under `Limits.default` and under a 50-byte `maxDecodedTotalBytes` budget (exercising
the "budget exhausted" path), separated by `--- <limits>` lines, and compared with
`<input>.expected` by `Tests.Golden.runCase` (Plan.md §6 Phase 3, M3 decoded-stream viewer).
`SAFEPDF_GOLDEN_UPDATE=1` regenerates.
-/

namespace SafePdf.Tests.StreamsView

open SafePdf.Shell.Views.Streams

/-- Directory of the inputs. -/
def dir : System.FilePath := Tests.Golden.goldenRoot / "streams"

/-- The view's text form under `limits` (the path is shown as `input`). -/
def renderWith (limits : Limits) (bytes : ByteArray) : List String :=
  let result := SafePdf.parseWith limits bytes
  let (recs, sc) := match result with
    | .ok d => decodeAll limits d.doc
    | .error _ => (#[], {})
  text "input" result recs sc #[]

/-- Render one input under the default limits and under a 50-byte total budget. -/
def render (bytes : ByteArray) : String :=
  let small := { Limits.default with maxDecodedTotalBytes := 50 }
  let lines :=
    ["--- default limits"] ++ renderWith Limits.default bytes ++
    ["--- maxDecodedTotalBytes 50"] ++ renderWith small bytes
  "\n".intercalate lines ++ "\n"

/-- Run the suite; returns the number of failures. -/
def run : IO Nat := do
  let update := (← IO.getEnv Tests.Golden.updateEnvVar) == some "1"
  if !(← dir.isDir) then
    IO.println s!"  FAIL streams view: directory {dir} not found (run from the repo root)"
    return 1
  let inputs := ((← dir.readDir).map (·.path)).toList.filter Tests.Golden.isInput
  let inputs := inputs.toArray.qsort (fun a b => a.toString < b.toString)
  if inputs.isEmpty then
    IO.println s!"  FAIL streams view: no input files in {dir}"
    return 1
  let mut c : Tests.Golden.Counts := {}
  for input in inputs do
    c ← Tests.Golden.runCase update render input c
  if update then IO.println s!"  streams view: wrote {c.written} .expected file(s)"
  else IO.println s!"  streams view: {c.cases} case(s), {c.failures} failure(s)"
  return c.failures

end SafePdf.Tests.StreamsView
