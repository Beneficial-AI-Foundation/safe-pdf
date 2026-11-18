import SafePdf

/-!
# Inspector (unverified shell, Plan.md §6 MVP / visibility track)

Stub created by task 0.1; the skeleton lands in task 0.10.
-/

namespace SafePdf.Shell.Inspect

/-- Run the inspector CLI. -/
def run (args : List String) : IO UInt32 := do
  match args with
  | [] =>
    IO.eprintln "usage: inspect <file.pdf> [view]"
    return 2
  | path :: _ =>
    let bytes ← IO.FS.readBinFile path
    IO.println s!"{path}: {bytes.size} bytes"
    return 0

end SafePdf.Shell.Inspect
