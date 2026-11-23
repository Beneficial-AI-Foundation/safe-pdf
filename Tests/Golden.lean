import SafePdf
import Tests.ObjRender

/-!
# Golden-file test harness (Plan.md §6 Phase 0, §7 item 1)

For every suite registered in `renderers`, each input file under `Tests/golden/<suite>/` is
fed to the suite's pure renderer `ByteArray → String`, and the result is compared with the
file `<input>.expected` next to it. Files ending in `.expected` or `.md`, and hidden files,
are not inputs.

* A mismatch reports the first differing line (expected vs actual).
* A missing `.expected` file is a failure, with a hint to regenerate.
* With `SAFEPDF_GOLDEN_UPDATE=1` in the environment the runner writes (or overwrites) every
  `.expected` file instead of comparing, and reports how many it wrote.

Paths are resolved relative to the current directory: run `lake exe tests` from the repo root.
-/

namespace SafePdf.Tests.Golden

/-- Directory holding one subdirectory per golden suite. -/
def goldenRoot : System.FilePath := "Tests" / "golden"

/-- Environment variable that switches the runner to regeneration mode. -/
def updateEnvVar : String := "SAFEPDF_GOLDEN_UPDATE"

/-- Suffix of expected-output files. -/
def expectedSuffix : String := ".expected"

/-- Render a `Document` as stable, line-oriented text. -/
def formatDocument (d : Document) : String :=
  let v := match d.version with
    | some (major, minor) => s!"{major}.{minor}"
    | none => "none"
  s!"ok\nheaderOffset: {d.headerOffset}\nversion: {v}\nbyteLength: {d.byteLength}\n" ++
    s!"open: {if d.repaired then "repaired" else "strict"}\nrevisions: {d.revisions}\n" ++
    s!"objects: {d.objectCount}\nroot: {d.root.1} {d.root.2}\n"

/-- Render a parse `Error` as stable, line-oriented text. -/
def formatError (e : Error) : String :=
  let body := match e with
    | .malformed off msg => s!"malformed at {off}: {msg}"
    | .limitExceeded k => s!"limitExceeded: {reprStr k}"
    | .unsupported what => s!"unsupported: {what}"
    | .cycle off what => s!"cycle at {off}: {what}"
  s!"error\n{body}\n"

/-- Renderer for the `header` suite: the result of `SafePdf.parse` (header check, then
`Core.Open.openFile`). -/
def renderHeader (bytes : ByteArray) : String :=
  match SafePdf.parse bytes with
  | .ok d => formatDocument d
  | .error e => formatError e

/-- Renderer for the `objects` suite: one direct object from offset 0 under `Limits.default`
(`SafePdf.parseObjectAt`), then the end position. -/
def renderObjects (bytes : ByteArray) : String :=
  match SafePdf.parseObjectAt Limits.default bytes 0 with
  | .ok (o, r) => "ok\n" ++ ObjRender.unlines (ObjRender.renderObj 0 "" o) ++ s!"end: {r}\n"
  | .error e => formatError e

/-- Renderer for the `indirect` suite: one indirect object or stream from offset 0 under
`Limits.default` (`SafePdf.parseIndirectAt`), then the end position. -/
def renderIndirect (bytes : ByteArray) : String :=
  match SafePdf.parseIndirectAt Limits.default bytes 0 with
  | .ok (io, r) => "ok\n" ++ ObjRender.unlines (ObjRender.renderIndirect io) ++ s!"end: {r}\n"
  | .error e => formatError e

/-- Registry of golden suites: suite name (= directory under `Tests/golden/`) and renderer. -/
def renderers : List (String × (ByteArray → String)) :=
  [ ("header", renderHeader),
    ("objects", renderObjects),
    ("indirect", renderIndirect) ]

/-- Whether `path` is a golden input (not an expected file, a note, or a hidden file). -/
def isInput (path : System.FilePath) : Bool :=
  let name := path.fileName.getD ""
  !(name.endsWith expectedSuffix || name.endsWith ".md" || name.startsWith ".")

/-- First line at which `expected` and `actual` differ, as `(lineNo, expected, actual)`
(1-based; a missing line is shown as `<end of file>`). -/
def firstDiff (expected actual : String) : Option (Nat × String × String) :=
  let e := expected.splitOn "\n"
  let a := actual.splitOn "\n"
  let n := max e.length a.length
  let line (xs : List String) (i : Nat) : String := (xs[i]?).getD "<end of file>"
  (List.range n).find? (fun i => line e i != line a i) |>.map
    (fun i => (i + 1, line e i, line a i))

/-- Outcome counters of one run. -/
structure Counts where
  /-- Inputs checked or regenerated. -/
  cases : Nat := 0
  /-- Failing inputs. -/
  failures : Nat := 0
  /-- `.expected` files written in update mode. -/
  written : Nat := 0

/-- Check (or, when `update`, regenerate) one input file. -/
def runCase (update : Bool) (render : ByteArray → String) (input : System.FilePath)
    (c : Counts) : IO Counts := do
  let c := { c with cases := c.cases + 1 }
  let expPath : System.FilePath := input.toString ++ expectedSuffix
  let actual ← try
      pure (Except.ok (render (← IO.FS.readBinFile input)))
    catch err => pure (Except.error (toString err))
  match actual with
  | .error msg =>
    IO.println s!"  FAIL {input}: cannot read input: {msg}"
    return { c with failures := c.failures + 1 }
  | .ok actual =>
  if update then
    IO.FS.writeFile expPath actual
    return { c with written := c.written + 1 }
  if !(← expPath.pathExists) then
    IO.println s!"  FAIL {input}: missing {expPath}"
    IO.println s!"       hint: run `{updateEnvVar}=1 lake exe tests` to create it, then review the diff"
    return { c with failures := c.failures + 1 }
  let expected ← IO.FS.readFile expPath
  match firstDiff expected actual with
  | none => return c
  | some (ln, e, a) =>
    IO.println s!"  FAIL {input}: output differs from {expPath} at line {ln}"
    IO.println s!"       expected: {repr e}"
    IO.println s!"       actual:   {repr a}"
    return { c with failures := c.failures + 1 }

/-- Run every registered golden suite; returns the number of failures. -/
def run : IO Nat := do
  let update := (← IO.getEnv updateEnvVar) == some "1"
  let mut c : Counts := {}
  for (suite, render) in renderers do
    let dir := goldenRoot / suite
    if !(← dir.isDir) then
      IO.println s!"  FAIL golden suite '{suite}': directory {dir} not found (run from the repo root)"
      c := { c with failures := c.failures + 1 }
      continue
    let entries ← dir.readDir
    let inputs := (entries.map (·.path)).toList.filter isInput
    let inputs := inputs.toArray.qsort (fun a b => a.toString < b.toString)
    if inputs.isEmpty then
      IO.println s!"  FAIL golden suite '{suite}': no input files in {dir}"
      c := { c with failures := c.failures + 1 }
    for input in inputs do
      c ← runCase update render input c
  if update then
    IO.println s!"  golden: wrote {c.written} .expected file(s) ({updateEnvVar}=1)"
  else
    IO.println s!"  golden: {c.cases} case(s), {c.failures} failure(s)"
  return c.failures

end SafePdf.Tests.Golden
