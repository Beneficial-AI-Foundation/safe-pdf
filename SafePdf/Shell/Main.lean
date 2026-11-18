import SafePdf.Shell.Inspect

/-- Entry point of the `inspect` executable (unverified shell). -/
def main (args : List String) : IO UInt32 :=
  SafePdf.Shell.Inspect.run args
