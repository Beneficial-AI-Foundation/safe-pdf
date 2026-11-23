import SafePdf.Spec.RoundTrip
import SafePdf.Spec.ObjEquiv

/-!
# Object-level round trip for the efficient parser (Plan.md §6 Phase 1, milestone M1)

The M1 headline `parse (print o) = o`, stated for the efficient `ByteArray` parser
`Core.ObjParse.parseObject` that the viewer actually runs. It composes:

* `Spec.RoundTrip.lexAll_print` and `Spec.RoundTrip.parse_printTokens` (task 1.7): the
  printed bytes lex to `printTokens o`, and the grammar spec parses those tokens back to `o`
  with nothing left over;
* `Spec.ObjEquiv.parseObj_of_spec_full` (task 1.8): when the whole input lexes and the spec
  parses all of its tokens, the efficient parser returns the same object.

Hypotheses: the object is canonical (`PdfObject.Canonical`: canonical reals, NUL-free names,
distinct dictionary keys), its references are in range (`RefsInRange`: object number ≥ 1,
generation ≤ 65535), and its nesting depth is within `limits.maxObjectDepth`. Objects
outside these hypotheses are not produced by the parser in the first place
(`Spec.Object.Parses.canonical`, `Core.ObjParse.parseObject_depth`).
-/

namespace SafePdf.Spec.RoundTripCore

open SafePdf
open SafePdf.Core.Print

/-- The bytes of `print o` are `printObj o`. -/
theorem print_data_toList (o : PdfObject) : (print o).data.toList = printObj o := by
  simp [print]

/-- **Round trip (M1).** The efficient parser reads the printed bytes of a canonical object
back to the same object: `parseObject (print o) = o`. The returned position is followed only
by whitespace and comments (in fact the printer emits none, so it is the end of input). -/
theorem parseObject_print (limits : Limits) (o : PdfObject) (hc : o.Canonical)
    (hr : RefsInRange o) (hd : o.depth ≤ limits.maxObjectDepth) :
    ∃ r, Core.ObjParse.parseObject limits (print o) 0 = .ok (o, r) := by
  have hlex : Spec.Lex.lexAll (print o).data.toList = .ok (printTokens o) := by
    rw [print_data_toList]
    exact Spec.RoundTrip.lexAll_print o hc
  have hp := Spec.RoundTrip.parse_printTokens o limits.maxObjectDepth hc hr hd
  obtain ⟨l, _, _, h⟩ := Spec.ObjEquiv.parseObj_of_spec_full hlex hp
  exact ⟨_, h⟩

end SafePdf.Spec.RoundTripCore
