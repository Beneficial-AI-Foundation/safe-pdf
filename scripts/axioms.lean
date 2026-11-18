/-
Axiom audit, run by `scripts/check-hygiene.sh` via `lake env lean scripts/axioms.lean`.

Every top-level theorem of the project must depend only on `propext`, `Classical.choice` and
`Quot.sound` (CLAUDE.md, Plan.md section 3).  The guard parses the output below and fails on any
other axiom, including `sorryAx`.

To add a check: import the module that defines the theorem, then add one line
    #print axioms Namespace.theorem_name
Keep one line per top-level theorem (spec equivalences, totality and bound theorems).
This file is outside the library and is never imported.
-/
import SafePdf.Core.Limits

-- Smoke check on a definition that exists today; replace/extend as theorems land.
#print axioms SafePdf.Limits.default
