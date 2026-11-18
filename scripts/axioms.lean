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
import SafePdf

-- Smoke check on a definition that exists today; replace/extend as theorems land.
#print axioms SafePdf.Limits.default

-- Phase 1, task 1.1: object model (SafePdf/Core/Object.lean)
#print axioms SafePdf.Decimal.normalizeAux_isCanonical
#print axioms SafePdf.Decimal.normalize_isCanonical
#print axioms SafePdf.Decimal.normalizeAux_value
#print axioms SafePdf.Decimal.normalize_value
#print axioms SafePdf.Decimal.normalizeAux_of_isCanonical
#print axioms SafePdf.Decimal.normalize_of_isCanonical
#print axioms SafePdf.Decimal.normalize_normalize
#print axioms SafePdf.Dict.lookup_mem
#print axioms SafePdf.Dict.lookup_of_mem
#print axioms SafePdf.PdfObject.eq_of_beq
#print axioms SafePdf.PdfObject.eq_of_beqList
#print axioms SafePdf.PdfObject.eq_of_beqDict
#print axioms SafePdf.PdfObject.beq_self
#print axioms SafePdf.PdfObject.beqList_self
#print axioms SafePdf.PdfObject.beqDict_self
#print axioms SafePdf.PdfObject.depth_le_depthList
#print axioms SafePdf.PdfObject.depth_le_depthDict
#print axioms SafePdf.PdfObject.depth_lt_array
#print axioms SafePdf.PdfObject.depth_lt_dict
#print axioms SafePdf.PdfObject.size_pos
#print axioms SafePdf.PdfObject.size_le_sizeList
#print axioms SafePdf.PdfObject.size_le_sizeDict
#print axioms SafePdf.PdfObject.size_lt_array
#print axioms SafePdf.PdfObject.size_lt_dict
#print axioms SafePdf.PdfObject.sizeOf_lt_array
#print axioms SafePdf.PdfObject.sizeOf_lt_dict
#print axioms SafePdf.PdfObject.Canonical.of_mem_array
#print axioms SafePdf.PdfObject.Canonical.of_mem_dict
#print axioms SafePdf.PdfObject.Canonical.keys_nodup
#print axioms SafePdf.PdfObject.realOf_canonical
