import SafePdf
import Tests.Golden
import Tests.Adversarial
import Tests.XrefViews

/-!
# Test runner

Shared registry: test suites are registered in `suites` (the orchestrator adds lines).
-/

namespace SafePdf.Tests

/-- A named test suite returning the number of failures. -/
structure Suite where
  name : String
  run : IO Nat

/-- Registered test suites. -/
def suites : List Suite :=
  [ { name := "smoke", run := do
        let l := SafePdf.Limits.default
        return if l.maxXObjectDepth == 32 then 0 else 1 },
    { name := "golden", run := SafePdf.Tests.Golden.run },
    { name := "adversarial", run := SafePdf.Tests.Adversarial.run },
    { name := "xref-views", run := SafePdf.Tests.XrefViews.run } ]

end SafePdf.Tests

def main : IO UInt32 := do
  let mut failures := 0
  for s in SafePdf.Tests.suites do
    let f ← s.run
    IO.println s!"[{if f == 0 then "PASS" else "FAIL"}] {s.name} ({f} failures)"
    failures := failures + f
  return if failures == 0 then 0 else 1
