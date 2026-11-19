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

-- Phase 3, task 3.1: FlateDecode (SafePdf/Core/Filter/Flate.lean)
#print axioms SafePdf.Core.Filter.Flate.inflate_size_le
#print axioms SafePdf.Core.Filter.Flate.zlibDecode_size_le
#print axioms SafePdf.Core.Filter.Flate.flateDecode_size_le
#print axioms SafePdf.Core.Filter.Flate.copyBack_size

-- Phase 3, task 3.2: PNG/TIFF predictors (SafePdf/Core/Filter/Predictor.lean)
#print axioms SafePdf.Core.Filter.Predictor.decodePng_exact
#print axioms SafePdf.Core.Filter.Predictor.decodePng_size
#print axioms SafePdf.Core.Filter.Predictor.decodePng_size_le
#print axioms SafePdf.Core.Filter.Predictor.decodeTiff2_size
#print axioms SafePdf.Core.Filter.Predictor.decodeTiff2_exact
#print axioms SafePdf.Core.Filter.Predictor.decode_size
#print axioms SafePdf.Core.Filter.Predictor.decode_size_le
#print axioms SafePdf.Core.Filter.Predictor.unfilterRow_spec
#print axioms SafePdf.Core.Filter.Predictor.unfilterRowSpec_none
#print axioms SafePdf.Core.Filter.Predictor.unfilterRow_eq_specGo

-- Phase 2, task 2.4a: xref streams in the chain walk (SafePdf/Spec/XrefTerm.lean)
#print axioms SafePdf.Spec.XrefTerm.step_calls_le
#print axioms SafePdf.Spec.XrefTerm.step_ok
#print axioms SafePdf.Spec.XrefTerm.walk_calls_le
#print axioms SafePdf.Spec.XrefTerm.walk_ok
#print axioms SafePdf.Spec.XrefTerm.parseSection_of_table
#print axioms SafePdf.Spec.XrefTerm.PrevStep.of_table
#print axioms SafePdf.Spec.XrefTerm.parseSection_of_stream
#print axioms SafePdf.Spec.XrefTerm.PrevStep.of_stream

-- Phase 2, task 2.4b: object streams (SafePdf/Core/Xref/ObjStm.lean)
#print axioms SafePdf.Core.Xref.ObjStm.decodeObjStm_offsets_sorted
#print axioms SafePdf.Core.Xref.ObjStm.decodeObjStm_bounds
#print axioms SafePdf.Core.Xref.ObjStm.decodeObjStm_first_le
#print axioms SafePdf.Core.Xref.ObjStm.decodeObjStm_nums_pos
#print axioms SafePdf.Core.Xref.ObjStm.decodeObjStm_nums_nodup
#print axioms SafePdf.Core.Xref.ObjStm.decodeObjStm_count_le
#print axioms SafePdf.Core.Xref.ObjStm.getObject_depth
#print axioms SafePdf.Core.Xref.ObjStm.fetchCompressed_depth
#print axioms SafePdf.Core.Xref.ObjStm.fetchCompressed_no_recursion
#print axioms SafePdf.Core.Xref.ObjStm.fetchCompressed_rank
#print axioms SafePdf.Core.Xref.ObjStm.fetchCompressed_self
#print axioms SafePdf.Core.Xref.ObjStm.fetchCompressed_nested
#print axioms SafePdf.Core.Xref.ObjStm.fetchCompressed_work

-- Phase 2, task 2.5: unambiguity S6 (SafePdf/Spec/Unambiguous.lean)
#print axioms SafePdf.Spec.Unambiguous.resolveEntry_of_ok
#print axioms SafePdf.Spec.Unambiguous.resolveEntry_eq_error_iff
#print axioms SafePdf.Spec.Unambiguous.resolveEntry_eq_some_iff
#print axioms SafePdf.Spec.Unambiguous.resolveEntry_eq_none_iff
#print axioms SafePdf.Spec.Unambiguous.resolveEntry_winner_unique
#print axioms SafePdf.Spec.Unambiguous.mergeChain_keys_nodup
#print axioms SafePdf.Spec.Unambiguous.mergeChain_mem_unique
#print axioms SafePdf.Spec.Unambiguous.lookupEntry_mergeChain_iff
#print axioms SafePdf.Spec.Unambiguous.resolveEntry_of_cons
#print axioms SafePdf.Spec.Unambiguous.loadChain_update
#print axioms SafePdf.Spec.Unambiguous.resolveEntry_update
#print axioms SafePdf.Spec.Unambiguous.resolveEntry_hybrid_table
#print axioms SafePdf.Spec.Unambiguous.resolveEntry_hybrid_stream
#print axioms SafePdf.Spec.Unambiguous.checkSize_ok_iff
#print axioms SafePdf.Spec.Unambiguous.resolveEntry_lt_size
-- Phase 2, task 2.11: opening documents (SafePdf/Core/Open.lean)
#print axioms SafePdf.Core.Open.validate_eq
#print axioms SafePdf.Core.Open.validate_root
#print axioms SafePdf.Core.Open.repairOpen_repaired
#print axioms SafePdf.Core.Open.openFile_repaired
#print axioms SafePdf.Core.Open.openFile_strict
#print axioms SafePdf.Core.Open.openFile_root
#print axioms SafePdf.Core.Open.parseIndirectBodyWith_depth
#print axioms SafePdf.Core.Open.parseIndirectResolved_depth
#print axioms SafePdf.Core.Open.getObject_depth
#print axioms SafePdf.Core.Open.getObject_work
#print axioms SafePdf.Core.Open.getObject_length_calls_le

-- Phase 2, task 2.13: cycles are final (Error.cycle; Open, XrefTerm, ObjStm, Length)
#print axioms SafePdf.Core.Open.openFile_cycle
#print axioms SafePdf.Core.Open.openFile_loadChain_cycle
#print axioms SafePdf.Core.Open.openFile_cycle_not_ok
#print axioms SafePdf.Core.Xref.ObjStm.fetchCompressed_self_cycle
#print axioms SafePdf.Core.Xref.ObjStm.fetchCompressed_mutual_cycle
#print axioms SafePdf.Spec.XrefTerm.step_revisited
#print axioms SafePdf.Spec.XrefTerm.step_error_endless
#print axioms SafePdf.Spec.XrefTerm.walk_endless
#print axioms SafePdf.Spec.XrefTerm.loadChain_endless
#print axioms SafePdf.Spec.XrefTerm.loadChain_endless_cycle
#print axioms SafePdf.Spec.XrefTerm.openFile_endless
-- Phase 3, task 3.3: ASCIIHex, ASCII85, RunLength
#print axioms SafePdf.Core.Filter.Ascii.run_spec
#print axioms SafePdf.Core.Filter.Ascii.decodeWith_spec
#print axioms SafePdf.Core.Filter.Ascii.asciiHexDecode_spec
#print axioms SafePdf.Core.Filter.Ascii.asciiHexDecode_size_le
#print axioms SafePdf.Core.Filter.Ascii.asciiHexDecode_size_le_input
#print axioms SafePdf.Core.Filter.Ascii.asciiHexDecode_encode
#print axioms SafePdf.Core.Filter.Ascii.ascii85Decode_spec
#print axioms SafePdf.Core.Filter.Ascii.ascii85Decode_size_le
#print axioms SafePdf.Core.Filter.Ascii.ascii85Decode_size_le_input
#print axioms SafePdf.Core.Filter.Ascii.ascii85Decode_encode
#print axioms SafePdf.Core.Filter.RunLength.runLengthDecode_spec
#print axioms SafePdf.Core.Filter.RunLength.runLengthDecode_size_le
#print axioms SafePdf.Core.Filter.RunLength.runLengthDecode_size_le_input
#print axioms SafePdf.Core.Filter.RunLength.runLengthDecode_encode
#print axioms SafePdf.Core.Filter.RunLength.rlSpec_repeat
-- Phase 2, task 2.12: prefix stability (SafePdf/Spec/PrefixStable.lean), SameAt discharged,
-- hybrid update, /Size in the strict open path
#print axioms SafePdf.Spec.PrefixStable.next_ext
#print axioms SafePdf.Spec.PrefixStable.parseObjTok_ext
#print axioms SafePdf.Spec.PrefixStable.parseIndirect_ext
#print axioms SafePdf.Spec.PrefixStable.parseXrefTable_ext
#print axioms SafePdf.Spec.PrefixStable.parseXrefStream_ext
#print axioms SafePdf.Spec.PrefixStable.findStartxref_last
#print axioms SafePdf.Spec.PrefixStable.parseXrefTable_end_lt
#print axioms SafePdf.Spec.PrefixStable.parseIndirect_end_lt
#print axioms SafePdf.Spec.PrefixStable.parseXrefTable_stable
#print axioms SafePdf.Spec.PrefixStable.parseXrefStream_stable
#print axioms SafePdf.Spec.PrefixStable.section_stable
#print axioms SafePdf.Spec.PrefixStable.stream_stable
#print axioms SafePdf.Spec.Unambiguous.loadChain_parses
#print axioms SafePdf.Spec.Unambiguous.sameAt_of_extends
#print axioms SafePdf.Spec.Unambiguous.loadChain_sameAt
#print axioms SafePdf.Spec.Unambiguous.loadChain_append
#print axioms SafePdf.Spec.Unambiguous.resolveEntry_append
#print axioms SafePdf.Spec.Unambiguous.loadChain_update_hybrid
#print axioms SafePdf.Spec.Unambiguous.loadChain_append_hybrid
#print axioms SafePdf.Spec.Unambiguous.resolveEntry_append_hybrid
#print axioms SafePdf.Spec.Unambiguous.openFile_lt_size
#print axioms SafePdf.Core.Open.strictOpen_ok
#print axioms SafePdf.Core.Open.checkSize_ok
#print axioms SafePdf.Core.Open.strictOpen_lt_size
-- Phase 3, task 3.4: LZWDecode (SafePdf/Core/Filter/LZW.lean)
#print axioms SafePdf.Core.Filter.LZW.lzwDecode_size_le
#print axioms SafePdf.Core.Filter.LZW.lzwDecode_fuel_enough
#print axioms SafePdf.Core.Filter.LZW.loop_fuel_irrel
#print axioms SafePdf.Core.Filter.LZW.codeWidth_ge
#print axioms SafePdf.Core.Filter.LZW.codeWidth_le
#print axioms SafePdf.Core.Filter.LZW.addEntry_size_le
#print axioms SafePdf.Core.Filter.LZW.addEntry_wf
#print axioms SafePdf.Core.Filter.LZW.addEntry_size_ge
#print axioms SafePdf.Core.Filter.LZW.addEntry_size_eq
#print axioms SafePdf.Core.Filter.LZW.expand_ok
#print axioms SafePdf.Core.Filter.LZW.step_wf
#print axioms SafePdf.Core.Filter.LZW.init_wf

-- Phase 2, task 2.14: /Length through object streams (SafePdf/Core/Xref/Length.lean;
-- decoding split into SafePdf/Core/Xref/ObjStmDecode.lean, same names)
#print axioms SafePdf.Core.Xref.Length.containerLength_calls_le
#print axioms SafePdf.Core.Xref.Length.resolveLength_container_cycle
-- Phase 3, task 3.5: filter pipeline (SafePdf/Core/Filter.lean)
#print axioms SafePdf.Core.Filter.decodeStream_size_le
#print axioms SafePdf.Core.Filter.decodeStream_nil
#print axioms SafePdf.Core.Filter.applyStages_image
#print axioms SafePdf.Core.Filter.decodeStream_image
#print axioms SafePdf.Core.Filter.decodeStream_unknown
#print axioms SafePdf.Core.Filter.decodeStream_unknown_name
#print axioms SafePdf.Core.Filter.decodeOne_size_le
#print axioms SafePdf.Core.Filter.applyStages_size_le
#print axioms SafePdf.Core.Filter.parseChain_length_le
#print axioms SafePdf.Core.Filter.produced_le
#print axioms SafePdf.Core.Filter.produced_le_maxFilters
-- Phase 3, task 3.8: deflate encoder and Flate round trip (SafePdf/Core/Filter/Deflate.lean)
#print axioms SafePdf.Core.Filter.Deflate.inflate_deflateStored
#print axioms SafePdf.Core.Filter.Deflate.zlibDecode_zlibStored
#print axioms SafePdf.Core.Filter.Deflate.adler32_lt
-- Phase 4, task 4.1: catalog and page tree (SafePdf/Core/Doc.lean)
#print axioms SafePdf.Core.Doc.cropBox_sub_media
#print axioms SafePdf.Core.Doc.foldl_merge_mediaBox
#print axioms SafePdf.Core.Doc.foldl_merge_rotate
#print axioms SafePdf.Core.Doc.popLive_cycle
#print axioms SafePdf.Core.Doc.loop_cycle
#print axioms SafePdf.Core.Doc.visitNode_visited
#print axioms SafePdf.Core.Doc.walk_visits_le
#print axioms SafePdf.Core.Doc.walk_no_repeat
#print axioms SafePdf.Core.Doc.walk_pages_le
#print axioms SafePdf.Core.Doc.ofOpen_pages_le
#print axioms SafePdf.Core.Doc.ofOpen_pages_nodup
-- Phase 4, task 4.3a: crypto primitives (SafePdf/Core/Crypt/)
#print axioms SafePdf.Core.Crypt.Md5.md5_size
