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

-- Phase 1, task 1.2: lexer spec (SafePdf/Spec/Lex.lean)
#print axioms SafePdf.Spec.Lex.skipWs_length_le
#print axioms SafePdf.Spec.Lex.skipComment_length_le
#print axioms SafePdf.Spec.Lex.regularRun_snd_length_le
#print axioms SafePdf.Spec.Lex.litBody_length_lt
#print axioms SafePdf.Spec.Lex.hexBody_length_le
#print axioms SafePdf.Spec.Lex.nextAt_consumes
#print axioms SafePdf.Spec.Lex.next_consumes
#print axioms SafePdf.Spec.Lex.nextAt_nil
#print axioms SafePdf.Spec.Lex.next_eq_none_of_skipWs_nil
#print axioms SafePdf.Spec.Lex.next_white
#print axioms SafePdf.Spec.Lex.skipComment_append
#print axioms SafePdf.Spec.Lex.skipWs_comment
#print axioms SafePdf.Spec.Lex.next_comment

-- Phase 1, task 1.3: tokenizer (SafePdf/Core/Lex.lean)
#print axioms SafePdf.Core.Lex.next_pos
#print axioms SafePdf.Core.Lex.litStr_bounds
#print axioms SafePdf.Core.Lex.hexStr_bounds
#print axioms SafePdf.Core.Lex.nameRun_bounds
#print axioms SafePdf.Core.Lex.readRun_bounds
#print axioms SafePdf.Core.Lex.lt_escapeAt

-- Phase 1, task 1.4: object grammar spec (SafePdf/Spec/Object.lean)
#print axioms SafePdf.Spec.Object.parse_eq_ok_iff
#print axioms SafePdf.Spec.Object.parse_isError_iff
#print axioms SafePdf.Spec.Object.Parses.unique
#print axioms SafePdf.Spec.Object.Parses.depth_le
#print axioms SafePdf.Spec.Object.parse_depth_le
#print axioms SafePdf.Spec.Object.Parses.length_lt
#print axioms SafePdf.Spec.Object.parse_length_lt
#print axioms SafePdf.Spec.Object.Parses.canonical

-- Phase 1, task 1.5: object parser (SafePdf/Core/ObjParse.lean)
#print axioms SafePdf.Core.ObjParse.parseObject_pos
#print axioms SafePdf.Core.ObjParse.parseObject_depth
#print axioms SafePdf.Core.ObjParse.parseObject_dict_keys_nodup
#print axioms SafePdf.Core.ObjParse.parseObj_pos
#print axioms SafePdf.Core.ObjParse.parseObj_depth

-- Phase 1, task 1.6: lexer equivalence, C5 (SafePdf/Spec/LexEquiv.lean)
#print axioms SafePdf.Spec.LexEquiv.next_eq
#print axioms SafePdf.Spec.LexEquiv.lexAll_eq
#print axioms SafePdf.Spec.LexEquiv.tokenAt_eq
#print axioms SafePdf.Spec.LexEquiv.litStr_eq
#print axioms SafePdf.Spec.LexEquiv.hexStr_eq
#print axioms SafePdf.Spec.LexEquiv.nameRun_eq
#print axioms SafePdf.Spec.LexEquiv.parseNumber_eq
#print axioms SafePdf.Spec.LexEquiv.skipWs_rest
#print axioms SafePdf.Spec.LexEquiv.readRun_eq

-- Phase 1, task 1.7: printer + round trip (SafePdf/Spec/RoundTrip.lean)
#print axioms SafePdf.Spec.RoundTrip.lexAll_print
#print axioms SafePdf.Spec.RoundTrip.parse_printTokens
#print axioms SafePdf.Spec.RoundTrip.roundTrip_spec
#print axioms SafePdf.Spec.RoundTrip.roundTrip_core
#print axioms SafePdf.Spec.RoundTrip.roundTrip_core_spec

-- Phase 1, task 1.8: object parser equivalence, C5 (SafePdf/Spec/ObjEquiv.lean)
#print axioms SafePdf.Spec.ObjEquiv.parseObj_ok_iff
#print axioms SafePdf.Spec.ObjEquiv.parseObj_error_iff
#print axioms SafePdf.Spec.ObjEquiv.parseObj_ok_iff_lexAll
#print axioms SafePdf.Spec.ObjEquiv.parseObj_error_iff_lexAll
#print axioms SafePdf.Spec.ObjEquiv.parseObj_of_spec_full
#print axioms SafePdf.Spec.ObjEquiv.parseObj_of_spec_full_size
#print axioms SafePdf.Spec.ObjEquiv.parseObj_of_parses_full
#print axioms SafePdf.Spec.ObjEquiv.lexFrom_of_lexAll

-- Phase 1, M1 headline: parseObject (print o) = o (SafePdf/Spec/RoundTripCore.lean)
#print axioms SafePdf.Spec.RoundTripCore.parseObject_print

-- Phase 2, task 2.1: classic xref table + trailer (SafePdf/Core/Xref.lean)
#print axioms SafePdf.Core.Xref.entryAt_eq
#print axioms SafePdf.Core.Xref.header_pos
#print axioms SafePdf.Core.Xref.entries_ok
#print axioms SafePdf.Core.Xref.sections_ok
#print axioms SafePdf.Core.Xref.XrefSection.keys_nodup
#print axioms SafePdf.Core.Xref.parseXrefTable_inUse_lt
#print axioms SafePdf.Core.Xref.parseXrefTable_gen_le
#print axioms SafePdf.Core.Xref.parseXrefTable_length_le
#print axioms SafePdf.Core.Xref.parseXrefTable_nodup
#print axioms SafePdf.Core.Xref.parseXrefTable_pos
#print axioms SafePdf.Core.Xref.findStartxref_lt

-- Phase 2, task 2.2: /Prev chain termination (SafePdf/Spec/XrefTerm.lean)
#print axioms SafePdf.Spec.XrefTerm.loadChain_terminates
#print axioms SafePdf.Spec.XrefTerm.loadChain_offsets_nodup
#print axioms SafePdf.Spec.XrefTerm.loadChain_offsets_lt
#print axioms SafePdf.Spec.XrefTerm.loadChain_length_le
#print axioms SafePdf.Spec.XrefTerm.loadChain_ok_reach
#print axioms SafePdf.Spec.XrefTerm.loadChain_cycle_rejected
#print axioms SafePdf.Spec.XrefTerm.loadChainCounted_calls_le
#print axioms SafePdf.Spec.XrefTerm.mergeChain_lookup
#print axioms SafePdf.Core.Xref.Chain.length_lt_of_fresh
#print axioms SafePdf.Core.Xref.Chain.mergeTwo_sorted

-- Phase 2, task 2.3: indirect /Length (SafePdf/Core/Xref/Length.lean)
#print axioms SafePdf.Core.Xref.Length.resolveLength_calls_le
#print axioms SafePdf.Core.Xref.Length.resolveLength_self
#print axioms SafePdf.Core.Xref.Length.lengthDict_self
#print axioms SafePdf.Core.Xref.Length.parseIndirectResolved_pos
#print axioms SafePdf.Core.Xref.Length.parseIndirectResolved_data

-- Phase 2, task 2.6: repair path (SafePdf/Repair.lean)
#print axioms SafePdf.Repair.scanAttempts_le
#print axioms SafePdf.Repair.scanFailures_le
#print axioms SafePdf.Repair.scanObjects_length_le
#print axioms SafePdf.Repair.scanObjects_header
#print axioms SafePdf.Repair.scanObjects_offset_lt
#print axioms SafePdf.Repair.scanObjects_sorted
#print axioms SafePdf.Repair.scanObjects_keys_nodup
#print axioms SafePdf.Repair.repair_ok
#print axioms SafePdf.Repair.repair_offset_lt
#print axioms SafePdf.Repair.repair_length_le
#print axioms SafePdf.Repair.repair_keys_nodup
