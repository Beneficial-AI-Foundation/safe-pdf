import SafePdf.Shell.App.Viewer

/-!
# Entry point of the `viewer` executable (task 8.2a; Plan.md §8, §10)

The native viewer shell (unverified). See `SafePdf.Shell.App.Viewer` and `docs/viewer.md`.
-/

/-- Entry point of the `viewer` executable. -/
def main (args : List String) : IO UInt32 :=
  SafePdf.Shell.App.Viewer.main args
