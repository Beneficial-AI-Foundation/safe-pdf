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
import SafePdf.Shell.App.TclLemmas
import SafePdf.Shell.App.View
import SafePdf.Shell.App.Marks
import SafePdf.Shell.App.Bubble
import SafePdf.Shell.App.Select
import SafePdf.Shell.App.Links
import SafePdf.Shell.App.Toolbar

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
-- Phase 3, task 3.9: filter consolidation (Filter.lean, Xref/Stream.lean, Xref/ObjStmDecode.lean)
#print axioms SafePdf.Core.Filter.decodeStream_too_many
#print axioms SafePdf.Core.Filter.parseChain_crypt_first
#print axioms SafePdf.Core.Filter.decodeBytes_size_le
#print axioms SafePdf.Core.Xref.Stream.decodeData_size_le
#print axioms SafePdf.Core.Xref.ObjStm.decodeData_size_le
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
-- Phase 3, task 3.8b: Flate work bound (SafePdf/Spec/FlateWork.lean)
#print axioms SafePdf.Spec.FlateWork.decodeGoW_fst
#print axioms SafePdf.Spec.FlateWork.codesW_fst
#print axioms SafePdf.Spec.FlateWork.codesW_bound
#print axioms SafePdf.Spec.FlateWork.storedW_fst
#print axioms SafePdf.Spec.FlateWork.storedW_bound
#print axioms SafePdf.Spec.FlateWork.readLengthsW_fst
#print axioms SafePdf.Spec.FlateWork.readLengthsW_bound
#print axioms SafePdf.Spec.FlateWork.readDynamicW_fst
#print axioms SafePdf.Spec.FlateWork.readDynamicW_bound
#print axioms SafePdf.Spec.FlateWork.blocksW_fst
#print axioms SafePdf.Spec.FlateWork.blocksW_bound
#print axioms SafePdf.Spec.FlateWork.inflateAtW_fst
#print axioms SafePdf.Spec.FlateWork.inflateAtW_steps_le
#print axioms SafePdf.Spec.FlateWork.inflateAtW_steps_le_of_ok
#print axioms SafePdf.Spec.FlateWork.inflateW_fst
#print axioms SafePdf.Spec.FlateWork.inflateW_steps_le
#print axioms SafePdf.Spec.FlateWork.zlibDecodeOutW_fst
#print axioms SafePdf.Spec.FlateWork.flateDecodeW_fst
#print axioms SafePdf.Spec.FlateWork.flateDecodeW_steps_le
#print axioms SafePdf.Spec.FlateWork.flateDecodeW_steps_le_of_ok
-- Phase 3, task 3.12: LZW step errors are limit errors
#print axioms SafePdf.Core.Filter.LZW.step_error
-- Phase 3, task 3.10: document-wide decoded-bytes budget (SafePdf/Core/Filter.lean, Doc.lean)
#print axioms SafePdf.Core.Filter.applyStagesB_le
#print axioms SafePdf.Core.Filter.applyStagesB_nobyte
#print axioms SafePdf.Core.Filter.applyStagesB_ok
#print axioms SafePdf.Core.Filter.decodeStreamB_le
#print axioms SafePdf.Core.Filter.decodeStreamB_charge
#print axioms SafePdf.Core.Filter.decodeStreamB_size_le
#print axioms SafePdf.Core.Filter.decodeStreamB_exhausted
#print axioms SafePdf.Core.Filter.decodeAllB_total
#print axioms SafePdf.Core.Filter.decodeAllB_init
#print axioms SafePdf.Core.Doc.decodeBodyB_le
#print axioms SafePdf.Core.Doc.decodeBodyB_charge
#print axioms SafePdf.Core.Doc.Doc.decodeStreamOf_le
#print axioms SafePdf.Core.Doc.Doc.decodeStreamOf_charge
#print axioms SafePdf.Core.Doc.Doc.decodeStreamOf_size_le
#print axioms SafePdf.Core.Doc.contentData_ok
#print axioms SafePdf.Core.Doc.Doc.decodeRefsB_le
#print axioms SafePdf.Core.Doc.Doc.decodeRefsB_total
#print axioms SafePdf.Core.Doc.Doc.decodeContentsB_le
#print axioms SafePdf.Core.Doc.Doc.decodeContentsB_total

-- Phase 3, task 3.11: table-driven inflate and fast Adler-32 (SafePdf/Core/Filter/Flate.lean)
#print axioms SafePdf.Core.Filter.Flate.decodeSym_eq
#print axioms SafePdf.Core.Filter.Flate.decodeGoB_decodeGo
#print axioms SafePdf.Core.Filter.Flate.decodeGoB_some
#print axioms SafePdf.Core.Filter.Flate.peek9_bit
#print axioms SafePdf.Core.Filter.Flate.window_bit
#print axioms SafePdf.Core.Filter.Flate.twoPow_getD
#print axioms SafePdf.Core.Filter.Flate.adlerGo_eq_foldl
#print axioms SafePdf.Core.Filter.Flate.adler32_eq_foldl
#print axioms SafePdf.Spec.FlateWork.decodeSymW_fst
#print axioms SafePdf.Core.Filter.Deflate.or4_mod_eight
-- Phase 4, task 4.2: navigation (SafePdf/Core/Doc/Nav.lean)
#print axioms SafePdf.Core.Doc.Nav.treeLoop_inv
#print axioms SafePdf.Core.Doc.Nav.treeWalk_visited_le
#print axioms SafePdf.Core.Doc.Nav.treeWalk_nodup
#print axioms SafePdf.Core.Doc.Nav.destsTree_visited_le
#print axioms SafePdf.Core.Doc.Nav.outlineLoop_inv
#print axioms SafePdf.Core.Doc.Nav.outline_inv
#print axioms SafePdf.Core.Doc.Nav.outline_visited_le
#print axioms SafePdf.Core.Doc.Nav.outline_nodup
#print axioms SafePdf.Core.Doc.Nav.outline_items_le
#print axioms SafePdf.Core.Doc.Nav.labelTable_visited_le
#print axioms SafePdf.Core.Doc.Nav.labelTable_nodup

-- Phase 4, task 4.1b: page-tree end-to-end theorems (SafePdf/Spec/Doc.lean)
#print axioms SafePdf.Spec.PageTree.foldl_merge_resources
#print axioms SafePdf.Spec.PageTree.foldl_merge_cropBox
#print axioms SafePdf.Spec.PageTree.loop_paths
#print axioms SafePdf.Spec.PageTree.walk_path_nodup
#print axioms SafePdf.Spec.PageTree.walk_kid_not_ancestor
#print axioms SafePdf.Spec.PageTree.walk_page_inherit
#print axioms SafePdf.Spec.PageTree.PageInh.fields
#print axioms SafePdf.Spec.PageTree.getObject_ne_null_key
#print axioms SafePdf.Spec.PageTree.popLive_exhausted
#print axioms SafePdf.Spec.PageTree.loop_fuel_irrelevant
#print axioms SafePdf.Spec.PageTree.walk_fuel_irrelevant
#print axioms SafePdf.Spec.PageTree.ofOpen_path_nodup
#print axioms SafePdf.Spec.PageTree.openDoc_path_nodup
#print axioms SafePdf.Spec.PageTree.ofOpen_cycle_error
#print axioms SafePdf.Spec.PageTree.openDoc_cycle_error
#print axioms SafePdf.Spec.PageTree.ofOpen_page_inherit
#print axioms SafePdf.Spec.PageTree.openDoc_page_inherit

-- Phase 4, task 4.1c: unique root-to-page paths; cycle error kind (SafePdf/Spec/Doc.lean)
#print axioms SafePdf.Spec.PageTree.loop_forest
#print axioms SafePdf.Spec.PageTree.walk_descends_unique
#print axioms SafePdf.Spec.PageTree.ofOpen_descends_unique
#print axioms SafePdf.Spec.PageTree.ofOpen_page_path_unique
#print axioms SafePdf.Spec.PageTree.openDoc_page_path_unique
#print axioms SafePdf.Spec.PageTree.loop_ok_or_cycle
#print axioms SafePdf.Spec.PageTree.walk_ok_or_cycle
#print axioms SafePdf.Spec.PageTree.walk_cycle_error
#print axioms SafePdf.Spec.PageTree.walk_shared_error
#print axioms SafePdf.Spec.PageTree.ofOpen_cycle_error_kind
#print axioms SafePdf.Spec.PageTree.openDoc_cycle_error_kind
#print axioms SafePdf.Spec.PageTree.ofOpen_shared_error
#print axioms SafePdf.Spec.PageTree.openDoc_shared_error

-- Phase 3, task 3.13: structural decodes charged against the document budget
-- (SafePdf/Core/Filter/Structural.lean, Core/Xref/Chain.lean, Core/Xref/ObjStm.lean, Core/Open.lean)
#print axioms SafePdf.Core.Filter.capped_of_le
#print axioms SafePdf.Core.Filter.budgetErr_of_le
#print axioms SafePdf.Core.Filter.failCharge_le
#print axioms SafePdf.Core.Filter.applyStagesB_cost
#print axioms SafePdf.Core.Filter.decodeStreamB_cost
#print axioms SafePdf.Core.Filter.applyStagesB_eq
#print axioms SafePdf.Core.Filter.decodeStreamB_eq
#print axioms SafePdf.Core.Filter.decodeBytesB_le
#print axioms SafePdf.Core.Filter.decodeBytesB_charge
#print axioms SafePdf.Core.Filter.decodeBytesB_size_le
#print axioms SafePdf.Core.Filter.decodeBytesB_cost
#print axioms SafePdf.Core.Filter.decodeBytesB_eq
#print axioms SafePdf.Core.Xref.Chain.parseIndirect_data_le
#print axioms SafePdf.Core.Xref.Chain.parseXrefStream_split
#print axioms SafePdf.Core.Xref.Chain.xrefStreamPre_data_le
#print axioms SafePdf.Core.Xref.Chain.decodeXrefDataB_le
#print axioms SafePdf.Core.Xref.Chain.decodeXrefDataB_cost
#print axioms SafePdf.Core.Xref.Chain.decodeXrefDataB_eq
#print axioms SafePdf.Core.Xref.Chain.parseXrefStreamB_le
#print axioms SafePdf.Core.Xref.Chain.parseXrefStreamB_cost
#print axioms SafePdf.Core.Xref.Chain.parseXrefStreamB_eq
#print axioms SafePdf.Core.Xref.Chain.parseSectionB_le
#print axioms SafePdf.Core.Xref.Chain.parseSectionB_cost
#print axioms SafePdf.Core.Xref.Chain.parseSectionB_eq
#print axioms SafePdf.Core.Xref.Chain.stepB_le
#print axioms SafePdf.Core.Xref.Chain.budget_step
#print axioms SafePdf.Core.Xref.Chain.stepB_eq
#print axioms SafePdf.Core.Xref.Chain.walkB_le
#print axioms SafePdf.Core.Xref.Chain.walkB_eq
#print axioms SafePdf.Core.Xref.Chain.loadChainB_le
#print axioms SafePdf.Core.Xref.Chain.loadChainB_eq
#print axioms SafePdf.Core.Xref.Chain.stepB_cost
#print axioms SafePdf.Core.Xref.Chain.walkB_cost
#print axioms SafePdf.Core.Xref.Chain.loadChainB_cost
#print axioms SafePdf.Core.Xref.ObjStm.decodeObjStmB_le
#print axioms SafePdf.Core.Xref.ObjStm.decodeObjStmB_cost
#print axioms SafePdf.Core.Xref.ObjStm.decodeObjStmB_eq
#print axioms SafePdf.Core.Xref.ObjStm.fetchCompressedB_le
#print axioms SafePdf.Core.Xref.ObjStm.fetchCompressedB_cost
#print axioms SafePdf.Core.Xref.ObjStm.fetchCompressedB_hit
#print axioms SafePdf.Core.Xref.ObjStm.cacheExact_nil
#print axioms SafePdf.Core.Xref.ObjStm.fetchCompressedB_eq
#print axioms SafePdf.Core.Xref.ObjStm.fetchCompressedB_depth
#print axioms SafePdf.Core.Open.getObjectB_le
#print axioms SafePdf.Core.Open.getObjectB_cost
#print axioms SafePdf.Core.Open.getObjectB_eq
#print axioms SafePdf.Core.Open.getObjectB_depth
#print axioms SafePdf.Core.Open.validateB_le
#print axioms SafePdf.Core.Open.validateB_cost
#print axioms SafePdf.Core.Open.validateB_eq_self
#print axioms SafePdf.Core.Open.validateB_root
#print axioms SafePdf.Core.Open.validateB_eq
#print axioms SafePdf.Core.Open.strictOpenB_le
#print axioms SafePdf.Core.Open.repairOpenB_le
#print axioms SafePdf.Core.Open.openFileB_le
#print axioms SafePdf.Core.Open.openFileB_strict
#print axioms SafePdf.Core.Open.openFileB_cycle
#print axioms SafePdf.Core.Open.openFileB_loadChain_cycle
#print axioms SafePdf.Core.Open.openFileB_root
#print axioms SafePdf.Core.Open.openFileB_repaired
#print axioms SafePdf.Core.Open.cacheExact_nil
#print axioms SafePdf.Core.Open.strictOpenB_eq
#print axioms SafePdf.Core.Open.repairOpenB_eq
#print axioms SafePdf.Core.Open.openFileB_eq
#print axioms SafePdf.Core.Open.Session.getObject_le
#print axioms SafePdf.Core.Open.Session.getObject_eq
#print axioms SafePdf.Core.Open.Session.ofDoc_exact
#print axioms SafePdf.Core.Open.Session.open_eq
-- Phase 5, task 5.1: graphics state and DisplayList (SafePdf/Core/Content/)
#print axioms SafePdf.Core.Content.Fixed.ext
#print axioms SafePdf.Core.Content.Fixed.clamp_raw_of_le
#print axioms SafePdf.Core.Content.Fixed.clamp_raw
#print axioms SafePdf.Core.Content.Fixed.ofScaled2_eq
#print axioms SafePdf.Core.Content.Fixed.zero_raw
#print axioms SafePdf.Core.Content.Fixed.one_raw
#print axioms SafePdf.Core.Content.Fixed.add_zero
#print axioms SafePdf.Core.Content.Fixed.zero_add
#print axioms SafePdf.Core.Content.Fixed.add_comm
#print axioms SafePdf.Core.Content.Fixed.mul_one
#print axioms SafePdf.Core.Content.Fixed.one_mul
#print axioms SafePdf.Core.Content.Fixed.mul_zero
#print axioms SafePdf.Core.Content.Fixed.zero_mul
#print axioms SafePdf.Core.Content.Fixed.mul_comm
#print axioms SafePdf.Core.Content.Matrix.identity_mul
#print axioms SafePdf.Core.Content.Matrix.mul_identity
#print axioms SafePdf.Core.Content.Matrix.apply_identity
#print axioms SafePdf.Core.Content.Comp.ofFixed_toFixed
#print axioms SafePdf.Core.Content.GStack.push_depth_le
#print axioms SafePdf.Core.Content.GStack.push_depth
#print axioms SafePdf.Core.Content.GStack.push_error_iff
#print axioms SafePdf.Core.Content.GStack.pop_push
#print axioms SafePdf.Core.Content.GStack.restore_push
#print axioms SafePdf.Core.Content.GStack.restore_empty
#print axioms SafePdf.Core.Content.GStack.restore_depth_le
#print axioms SafePdf.Core.Content.GStack.bounded_empty
#print axioms SafePdf.Core.Content.GStack.push_bounded
#print axioms SafePdf.Core.Content.GStack.restore_bounded
#print axioms SafePdf.Core.Content.Paint.items_length_le
#print axioms SafePdf.Core.Content.Paint.items_ne_nil
-- Phase 4, task 4.3b: standard security handler (SafePdf/Core/Crypt.lean, Open.lean)
#print axioms SafePdf.Core.Crypt.decryptObj_depth
#print axioms SafePdf.Core.Crypt.decryptList_depth
#print axioms SafePdf.Core.Crypt.decryptDict_depth
#print axioms SafePdf.Core.Crypt.decryptBody_shape
#print axioms SafePdf.Core.Crypt.decryptBytes_size_le
#print axioms SafePdf.Core.Crypt.decryptBytes_rc4_size
#print axioms SafePdf.Core.Crypt.decryptBytes_aes_size
#print axioms SafePdf.Core.Crypt.decryptData_size_le
#print axioms SafePdf.Core.Crypt.decryptContainer_size_le
#print axioms SafePdf.Core.Open.withCrypt_ok
#print axioms SafePdf.Core.Open.withCrypt_plain
#print axioms SafePdf.Core.Open.decrypt_none
#print axioms SafePdf.Core.Open.decrypt_depth
#print axioms SafePdf.Core.Open.repairOpen_ok
#print axioms SafePdf.Core.Open.repairOpenB_ok
#print axioms SafePdf.Core.Open.openFile_setup_final
-- Phase 5, task 5.2a: content tokenizer and interpreter core
#print axioms SafePdf.Core.Content.interp_items_le
#print axioms SafePdf.Core.Content.interpBytes_items_le
#print axioms SafePdf.Core.Content.runOps_stack_bounded
#print axioms SafePdf.Core.Content.Ops.tokenize_ops_le
#print axioms SafePdf.Core.Content.Ops.tokenize_ops_le_max
-- Phase 4, task 4.6: encryption follow-ups (Crypt.lean, Open.lean)
#print axioms SafePdf.Core.Crypt.setupError_final
#print axioms SafePdf.Core.Crypt.identityEntry_depth
#print axioms SafePdf.Core.Crypt.identityParms_depth
#print axioms SafePdf.Core.Crypt.appliedParms_depth
#print axioms SafePdf.Core.Crypt.markApplied_depth
#print axioms SafePdf.Core.Open.openFile_final
#print axioms SafePdf.Core.Open.openFile_repair_encryption
-- Phase 5, task 5.3: interpreter transition spec (SafePdf/Spec/Content.lean)
#print axioms SafePdf.Spec.Content.step_iff_exec
#print axioms SafePdf.Spec.Content.exec_step
#print axioms SafePdf.Spec.Content.step_det
#print axioms SafePdf.Spec.Content.step_total
#print axioms SafePdf.Spec.Content.steps_det
#print axioms SafePdf.Spec.Content.steps_iff_runOps
#print axioms SafePdf.Spec.Content.interp_steps
#print axioms SafePdf.Spec.Content.interp_items_of_steps
-- Phase 4, task 4.5: budgeted /Length resolution, sessions for the page tree and decodes
#print axioms SafePdf.Core.Xref.ObjStm.mkObjStm_data
#print axioms SafePdf.Core.Xref.ObjStm.decodeObjStmB_charge
#print axioms SafePdf.Core.Xref.Length.containerMemberB_le
#print axioms SafePdf.Core.Xref.Length.containerMemberB_cost
#print axioms SafePdf.Core.Xref.Length.containerMemberB_eq
#print axioms SafePdf.Core.Xref.Length.containerLengthB_calls_le
#print axioms SafePdf.Core.Xref.Length.containerLengthB_le
#print axioms SafePdf.Core.Xref.Length.containerLengthB_cost
#print axioms SafePdf.Core.Xref.Length.containerLengthB_eq
#print axioms SafePdf.Core.Xref.Length.resolveLengthB_calls_le
#print axioms SafePdf.Core.Xref.Length.resolveLengthB_le
#print axioms SafePdf.Core.Xref.Length.resolveLengthB_cost
#print axioms SafePdf.Core.Xref.Length.resolveLengthB_self
#print axioms SafePdf.Core.Xref.Length.resolveLengthB_container_cycle
#print axioms SafePdf.Core.Xref.Length.resolveLengthB_eq
#print axioms SafePdf.Core.Xref.Length.lengthOfB_le
#print axioms SafePdf.Core.Xref.Length.lengthOfB_cost
#print axioms SafePdf.Core.Xref.Length.lengthOfB_eq
#print axioms SafePdf.Core.Xref.Length.parseIndirectResolved_eq_with
#print axioms SafePdf.Core.Xref.Length.parseStreamBodyWith_congr
#print axioms SafePdf.Core.Xref.Length.parseIndirectBodyWith_congr
#print axioms SafePdf.Core.Xref.Length.parseIndirectWith_congr
#print axioms SafePdf.Core.Xref.Length.parseIndirectWith_pos
#print axioms SafePdf.Core.Xref.Length.parseIndirectWith_data
#print axioms SafePdf.Core.Xref.Length.parseIndirectResolvedB_with
#print axioms SafePdf.Core.Xref.Length.parseIndirectResolvedB_le
#print axioms SafePdf.Core.Xref.Length.parseIndirectResolvedB_cost
#print axioms SafePdf.Core.Xref.Length.parseIndirectResolvedB_eq
#print axioms SafePdf.Core.Xref.Length.parseIndirectResolvedB_pos
#print axioms SafePdf.Core.Xref.Length.parseIndirectResolvedB_data
#print axioms SafePdf.Core.Xref.ObjStm.fetchCompressedB_eq_post
#print axioms SafePdf.Core.Open.parseIndirectWith_depth
#print axioms SafePdf.Core.Open.getObjectB_eq_post
#print axioms SafePdf.Core.Open.validateB_eq_post
#print axioms SafePdf.Core.Open.openFileB_bytes
#print axioms SafePdf.Core.Open.Session.open_bytes
#print axioms SafePdf.Core.Open.Session.getObject_eq_pre
#print axioms SafePdf.Core.Doc.sim_pure
#print axioms SafePdf.Core.Doc.sim_of_eq
#print axioms SafePdf.Core.Doc.fetchB_sim
#print axioms SafePdf.Core.Doc.resolveB_sim
#print axioms SafePdf.Core.Doc.keyB_sim
#print axioms SafePdf.Core.Doc.bindB_sim
#print axioms SafePdf.Core.Doc.attrsOfB_sim
#print axioms SafePdf.Core.Doc.popLiveB_sim
#print axioms SafePdf.Core.Doc.visitNodeB_sim
#print axioms SafePdf.Core.Doc.loopB_sim
#print axioms SafePdf.Core.Doc.walkB_sim
#print axioms SafePdf.Core.Doc.declaredCountOfB_sim
#print axioms SafePdf.Core.Doc.ofOpenB_sim
#print axioms SafePdf.Core.Doc.ofSession_le
#print axioms SafePdf.Core.Doc.ofSession_eq
#print axioms SafePdf.Core.Doc.openDocS_eq
#print axioms SafePdf.Core.Doc.resolveParamRefB_le
#print axioms SafePdf.Core.Doc.resolveParamsB_le
#print axioms SafePdf.Core.Doc.resolveParamB_le
#print axioms SafePdf.Core.Doc.resolveStreamDictB_le
#print axioms SafePdf.Core.Doc.decodeBodyS_le
#print axioms SafePdf.Core.Doc.decodeBodyS_charge
#print axioms SafePdf.Core.Doc.decodeStreamS_le
#print axioms SafePdf.Core.Doc.decodeStreamS_charge
#print axioms SafePdf.Core.Doc.decodeRefsS_total
#print axioms SafePdf.Core.Doc.contentPart_total
#print axioms SafePdf.Core.Doc.decodeContentsBC_total
#print axioms SafePdf.Core.Doc.decodeContentsS_total
-- Phase 6, task 6.4: encodings, standard-14 metrics, widths
#print axioms SafePdf.Core.Font.standardEncoding_size
#print axioms SafePdf.Core.Font.winAnsiEncoding_size
#print axioms SafePdf.Core.Font.macRomanEncoding_size
#print axioms SafePdf.Core.Font.pdfDocEncoding_size
#print axioms SafePdf.Core.Font.applyDiffsAux_size
#print axioms SafePdf.Core.Font.applyDifferences_size
#print axioms SafePdf.Core.Font.simpleEncoding_size
#print axioms SafePdf.Core.Font.std14_rows_size
#print axioms SafePdf.Core.Font.parseW_length_le
#print axioms SafePdf.Core.Font.setFirst_size
#print axioms SafePdf.Core.Font.fillConst_size
#print axioms SafePdf.Core.Font.fillRun_size
#print axioms SafePdf.Core.Font.buildWAux_size
#print axioms SafePdf.Core.Font.buildWTable_size
#print axioms SafePdf.Core.Font.SimpleMetrics.ofDict_table_size
#print axioms SafePdf.Core.Font.identityCodes_length
-- Phase 6, task 6.3: Type 1 fonts
#print axioms SafePdf.Core.Font.Type1.decrypt_size
#print axioms SafePdf.Core.Font.Type1.eexecDecrypt_size
#print axioms SafePdf.Core.Font.Type1.decryptCharstring_size
#print axioms SafePdf.Core.Font.Type1.scanWhile_bounds
#print axioms SafePdf.Core.Font.Type1.scanString_bounds
#print axioms SafePdf.Core.Font.Type1.tokAt_spec
#print axioms SafePdf.Core.Font.Type1.nextTok_spec
#print axioms SafePdf.Core.Font.Type1.encodingOf_size
#print axioms SafePdf.Core.Font.Type1.mkAdvances_get
#print axioms SafePdf.Core.Font.Type1.Font1.advance_eq
#print axioms SafePdf.Core.Font.Type1.run_stack_le
#print axioms SafePdf.Core.Font.Type1.run_calls_le
-- Phase 5, task 5.2b: content runner with resources (SafePdf/Core/Content/Run.lean)
#print axioms SafePdf.Core.Content.Run.formJob_num
#print axioms SafePdf.Core.Content.Run.doStep_form_fresh
#print axioms SafePdf.Core.Content.Run.viaExec_bound
#print axioms SafePdf.Core.Content.Run.localStep_bound
#print axioms SafePdf.Core.Content.Run.stepR_good
#print axioms SafePdf.Core.Content.Run.foldl_good
#print axioms SafePdf.Core.Content.Run.runOps_good
#print axioms SafePdf.Core.Content.St.init_good
#print axioms SafePdf.Core.Content.runPage_ops_le
#print axioms SafePdf.Core.Content.runPage_items_le
#print axioms SafePdf.Core.Content.runBytes_items_le_max
-- Phase 6, task 6.1: TrueType fonts
#print axioms SafePdf.Core.Font.TrueType.u8At_some_lt
#print axioms SafePdf.Core.Font.TrueType.u16At_some_lt
#print axioms SafePdf.Core.Font.TrueType.u32At_some_lt
#print axioms SafePdf.Core.Font.TrueType.i16At_some_lt
#print axioms SafePdf.Core.Font.TrueType.u16At_lt
#print axioms SafePdf.Core.Font.TrueType.findTable_bounds
#print axioms SafePdf.Core.Font.TrueType.tableBytes_size
#print axioms SafePdf.Core.Font.TrueType.seg4Find_lt
#print axioms SafePdf.Core.Font.TrueType.TTFont.advanceOfGlyph_lt
#print axioms SafePdf.Core.Font.TrueType.TTFont.lookupIn_lt
#print axioms SafePdf.Core.Font.TrueType.outlineAux_zero
#print axioms SafePdf.Core.Font.TrueType.outlineAux_visited
-- Phase 6, task 6.5: ToUnicode CMaps and text extraction
#print axioms SafePdf.Core.Font.CMap.parse_entries_le_tokens
#print axioms SafePdf.Core.Font.CMap.parse_entries_le_max
#print axioms SafePdf.Core.Font.CMap.tokenize_length_le
#print axioms SafePdf.Core.Font.CMap.CMap.codes_flatten
#print axioms SafePdf.Core.Font.CMap.CMap.decode_flatten
#print axioms SafePdf.Core.Text.SplitKind.codes_flatten
#print axioms SafePdf.Core.Text.extract_from_items
#print axioms SafePdf.Core.Text.runGlyphs_codes
#print axioms SafePdf.Core.Text.extractPage_glyphs
#print axioms SafePdf.Core.Text.extractPage_items

-- Phase 6, task 6.4b: Symbol/ZapfDingbats encodings (SafePdf/Core/Font/Encoding.lean)
#print axioms SafePdf.Core.Font.symbolEncoding_size
#print axioms SafePdf.Core.Font.zapfDingbatsEncoding_size
#print axioms SafePdf.Core.Font.symbolicBuiltin?_size
#print axioms SafePdf.Core.Font.implicitBase_size
#print axioms SafePdf.Core.Font.symbolic_rows_size

-- Phase 7, task 7.1: ℚ geometry and C2 (SafePdf/Core/Raster/Geom.lean)
#print axioms SafePdf.Core.Raster.Geom.Aff.mul_assoc
#print axioms SafePdf.Core.Raster.Geom.Aff.apply_mul
#print axioms SafePdf.Core.Raster.Geom.Aff.inv_apply_apply
#print axioms SafePdf.Core.Raster.Geom.Aff.apply_inv_apply
#print axioms SafePdf.Core.Raster.Geom.Fixed.toRat_injective
#print axioms SafePdf.Core.Raster.Geom.Aff.ofMatrix_mul_exact
#print axioms SafePdf.Core.Raster.Geom.Matrix.apply_x_err
#print axioms SafePdf.Core.Raster.Geom.Matrix.apply_y_err
#print axioms SafePdf.Core.Raster.Geom.rotAdd_assoc
#print axioms SafePdf.Core.Raster.Geom.rotationOfInt_degrees_add
#print axioms SafePdf.Core.Raster.Geom.toPage_toScreen
#print axioms SafePdf.Core.Raster.Geom.toScreen_toPage
#print axioms SafePdf.Core.Raster.Geom.toPageView_toScreenView
#print axioms SafePdf.Core.Raster.Geom.toScreenView_toPageView
#print axioms SafePdf.Core.Raster.Geom.toScreen_rotAdd_r90
#print axioms SafePdf.Core.Raster.Geom.toScreen_mem

-- Phase 6, task 6.2: CFF (SafePdf/Core/Font/CFF.lean)
#print axioms SafePdf.Core.Font.CFF.u8_lt
#print axioms SafePdf.Core.Font.CFF.readBE_lt
#print axioms SafePdf.Core.Font.CFF.Index.item_end_le
#print axioms SafePdf.Core.Font.CFF.Index.count_le
#print axioms SafePdf.Core.Font.CFF.Index.items_size
#print axioms SafePdf.Core.Font.CFF.bias_pos
#print axioms SafePdf.Core.Font.CFF.run_stack_le
#print axioms SafePdf.Core.Font.CFF.run_calls_le
#print axioms SafePdf.Core.Font.CFF.run_steps_le
#print axioms SafePdf.Core.Font.CFF.evalList_size
#print axioms SafePdf.Core.Font.CFF.CFFFont.advance_eq
#print axioms SafePdf.Core.Font.CFF.CFFFont.numGlyphs_le_max

-- Phase 7, task 7.2a: fill core (SafePdf/Core/Raster/Fill.lean)
#print axioms SafePdf.Core.Raster.Fill.bez_sub_chord
#print axioms SafePdf.Core.Raster.Fill.chord_err
#print axioms SafePdf.Core.Raster.Fill.flatten_err
#print axioms SafePdf.Core.Raster.Fill.flatten_err_tol
#print axioms SafePdf.Core.Raster.Fill.bezNum_eq
#print axioms SafePdf.Core.Raster.Fill.roundDivI_err
#print axioms SafePdf.Core.Raster.Fill.segCount_spec
#print axioms SafePdf.Core.Raster.Fill.flatten_size_le
#print axioms SafePdf.Core.Raster.Fill.rowLoop_inv
#print axioms SafePdf.Core.Raster.Fill.fillEdges_size
#print axioms SafePdf.Core.Raster.Fill.fillEdgesCounted_steps_le
#print axioms SafePdf.Core.Raster.Fill.maskRect_le
#print axioms SafePdf.Core.Raster.Fill.covByte_full

-- Phase 6, task 6.7c: CIDToGIDMap (SafePdf/Core/Text.lean)
#print axioms SafePdf.Core.Text.CIDToGID.gid_table_lt

-- Phase 7, task 7.2c: clipping and path rendering (SafePdf/Core/Raster/Clip.lean)
#print axioms SafePdf.Core.Raster.Clip.mul255_le_left
#print axioms SafePdf.Core.Raster.Clip.mul255_le_right
#print axioms SafePdf.Core.Raster.Clip.mul255_le_255
#print axioms SafePdf.Core.Raster.Fill.Mask.tabulate_size
#print axioms SafePdf.Core.Raster.Fill.Mask.tabulate_get
#print axioms SafePdf.Core.Raster.Fill.Mask.inter_get_le_left
#print axioms SafePdf.Core.Raster.Fill.Mask.inter_get_le_right
#print axioms SafePdf.Core.Raster.Clip.covAt_le_mask
#print axioms SafePdf.Core.Raster.Clip.covAt_le_clip
#print axioms SafePdf.Core.Raster.Clip.covAt_le_255
#print axioms SafePdf.Core.Raster.Clip.ClipCache.insert_length_le
#print axioms SafePdf.Core.Raster.Clip.clipMaskC_steps_le
#print axioms SafePdf.Core.Raster.Clip.renderItemsCounted_steps_le
#print axioms SafePdf.Core.Raster.Clip.renderItems_size
#print axioms SafePdf.Core.Raster.Clip.renderPaths_size
#print axioms SafePdf.Core.Raster.Clip.pageSize_le

-- Phase 7, task 7.2b: stroking (SafePdf/Core/Raster/Stroke.lean)
#print axioms SafePdf.Core.Raster.Stroke.sqrtQ_spec
#print axioms SafePdf.Core.Raster.Stroke.sqrtQ_rel
#print axioms SafePdf.Core.Raster.Stroke.pushPoly_size
#print axioms SafePdf.Core.Raster.Stroke.emit_size
#print axioms SafePdf.Core.Raster.Stroke.capStart_size
#print axioms SafePdf.Core.Raster.Stroke.capEnd_size
#print axioms SafePdf.Core.Raster.Stroke.dot_size
#print axioms SafePdf.Core.Raster.Stroke.join_size
#print axioms SafePdf.Core.Raster.Stroke.dashEnd_size
#print axioms SafePdf.Core.Raster.Stroke.dashThrough_size
#print axioms SafePdf.Core.Raster.Stroke.dashLoop_size
#print axioms SafePdf.Core.Raster.Stroke.solidSub_size
#print axioms SafePdf.Core.Raster.Stroke.strokeSub_size
#print axioms SafePdf.Core.Raster.Stroke.strokeSubs_size
#print axioms SafePdf.Core.Raster.Stroke.mkSegs_size
#print axioms SafePdf.Core.Raster.Stroke.strokeDPath_size_le
#print axioms SafePdf.Core.Raster.Stroke.subpaths_bound
#print axioms SafePdf.Core.Raster.Stroke.strokeEdges_size_le

-- Phase 7, task 7.2d: raster caps in Limits
#print axioms SafePdf.Core.Raster.Fill.segCount_tol_of_cap
#print axioms SafePdf.Core.Raster.Fill.Config.one_le_segCap
#print axioms SafePdf.Core.Raster.Stroke.Geo.make_polyCap

-- Phase 7, task 7.3a: glyph outlines (SafePdf/Core/Font/Outline.lean, SafePdf/Core/Raster/Glyph.lean)
#print axioms SafePdf.Core.Font.Outline.PathAcc.size_le
#print axioms SafePdf.Core.Font.Outline.PathAcc.push_size
#print axioms SafePdf.Core.Raster.Glyph.Cache.insert_length_le
#print axioms SafePdf.Core.Raster.Glyph.outlineToD_size
#print axioms SafePdf.Core.Raster.Glyph.addGlyph_size_le
#print axioms SafePdf.Core.Raster.Glyph.runPath_size_le
#print axioms SafePdf.Core.Raster.Glyph.paintAll_size
#print axioms SafePdf.Core.Raster.Glyph.renderItemG_size
#print axioms SafePdf.Core.Raster.Glyph.renderPage_size

-- Phase 7, task 7.2e: fast compositor (SafePdf/Core/Raster/Clip.lean)
#print axioms SafePdf.Core.Raster.Clip.composite_size
#print axioms SafePdf.Core.Raster.Clip.compositeSpec_size
#print axioms SafePdf.Core.Raster.Clip.compLoopSpec_size

-- Phase 7, task 7.3b: images (SafePdf/Core/Raster/Image.lean)
#print axioms SafePdf.Core.Raster.Image.rd_eq_getB
#print axioms SafePdf.Core.Raster.Image.sampleOffset_lt
#print axioms SafePdf.Core.Raster.Image.samplesLoop_size
#print axioms SafePdf.Core.Raster.Image.samples_size
#print axioms SafePdf.Core.Raster.Image.pushPixel_size
#print axioms SafePdf.Core.Raster.Image.rgbaLoop_size
#print axioms SafePdf.Core.Raster.Image.finish_dims
#print axioms SafePdf.Core.Raster.Image.decodePixmap_pixels
#print axioms SafePdf.Core.Raster.Image.putPx_size
#print axioms SafePdf.Core.Raster.Image.colLoop_size
#print axioms SafePdf.Core.Raster.Image.rowLoop_size
#print axioms SafePdf.Core.Raster.Image.place_size
#print axioms SafePdf.Core.Raster.Image.placeRect_area_le
#print axioms SafePdf.Core.Raster.Image.place_steps_le
#print axioms SafePdf.Core.Raster.Image.renderImage_size
#print axioms SafePdf.Core.Raster.Image.renderImage_steps_le

-- Phase 7, task 7.2f: fast scanline filler (SafePdf/Core/Raster/Fill.lean)
#print axioms SafePdf.Core.Raster.Fill.fillEdgesSpec_size
#print axioms SafePdf.Core.Raster.Fill.fillEdgesCountedSpec_steps_le
#print axioms SafePdf.Core.Raster.Fill.sortAct_size
#print axioms SafePdf.Core.Raster.Fill.rowLoopF_inv
#print axioms SafePdf.Core.Raster.Fill.fillRows_spec

-- Phase 7, task 7.3e: image masks, smooth sampling, fast placement
#print axioms SafePdf.Core.Raster.Image.u8_eq
#print axioms SafePdf.Core.Raster.Image.samplesRows_size
#print axioms SafePdf.Core.Raster.Image.keyLoop_size
#print axioms SafePdf.Core.Raster.Image.push4_size
#print axioms SafePdf.Core.Raster.Image.resCols_size
#print axioms SafePdf.Core.Raster.Image.resRows_size
#print axioms SafePdf.Core.Raster.Image.alphaLoop_size
#print axioms SafePdf.Core.Raster.Image.matteLoop_size
#print axioms SafePdf.Core.Raster.Image.pushAvg_size
#print axioms SafePdf.Core.Raster.Image.boxCols_size
#print axioms SafePdf.Core.Raster.Image.boxRows_size
#print axioms SafePdf.Core.Raster.Image.size_ite
#print axioms SafePdf.Core.Raster.Image.pixel_size
#print axioms SafePdf.Core.Raster.Image.downscales_le

-- Phase 7, task 7.3c: transparency (SafePdf/Core/Raster/Transparency.lean, Run, Glyph wiring)
#print axioms SafePdf.Core.Content.Run.FormJob.pre_post_le
#print axioms SafePdf.Core.Content.Run.gsStep_pend
#print axioms SafePdf.Core.Content.Run.gsR_good
#print axioms SafePdf.Core.Raster.Transparency.blendSep_le
#print axioms SafePdf.Core.Raster.Transparency.blendSep_normal
#print axioms SafePdf.Core.Raster.Transparency.blendRGB_le
#print axioms SafePdf.Core.Raster.Transparency.combinePx_size
#print axioms SafePdf.Core.Raster.Transparency.span_size
#print axioms SafePdf.Core.Raster.Transparency.spans_size
#print axioms SafePdf.Core.Raster.Transparency.combine_size
#print axioms SafePdf.Core.Raster.Transparency.addMask_length_le
#print axioms SafePdf.Core.Raster.Transparency.fillBuf_size
#print axioms SafePdf.Core.Raster.Transparency.beginLayer_open_le
#print axioms SafePdf.Core.Raster.Transparency.beginLayer_size
#print axioms SafePdf.Core.Raster.Transparency.endLayer_size
#print axioms SafePdf.Core.Raster.Transparency.beginGroup_size
#print axioms SafePdf.Core.Raster.Transparency.tabulate_size
#print axioms SafePdf.Core.Raster.Transparency.maskFrom_size
#print axioms SafePdf.Core.Raster.Transparency.addMask_stack
#print axioms SafePdf.Core.Raster.Transparency.paintFx_inv
#print axioms SafePdf.Core.Raster.Transparency.renderTx_inv
#print axioms SafePdf.Core.Raster.Transparency.foldl_renderTx_inv
#print axioms SafePdf.Core.Raster.Transparency.renderTx_items_size
#print axioms SafePdf.Core.Raster.Glyph.renderItemG_tx
#print axioms SafePdf.Core.Raster.Glyph.painterG_lawful

-- Phase 7, task 7.3d: shadings (SafePdf/Core/Raster/Shading.lean)
#print axioms SafePdf.Core.Raster.Shading.Fn.eval_length
#print axioms SafePdf.Core.Raster.Shading.lutIdx_lt
#print axioms SafePdf.Core.Raster.Shading.buildLut_size
#print axioms SafePdf.Core.Raster.Shading.paint_size
#print axioms SafePdf.Core.Raster.Shading.paint_steps_le
#print axioms SafePdf.Core.Raster.Shading.paintMesh_inv
#print axioms SafePdf.Core.Raster.Shading.withBBox_cost
#print axioms SafePdf.Core.Raster.Shading.renderShading_size
#print axioms SafePdf.Core.Raster.Shading.renderShading_steps_le
#print axioms SafePdf.Core.Raster.Shading.renderPatternFill_size
#print axioms SafePdf.Core.Raster.Shading.renderFill_size

-- Phase 7, task 7.3f: display-list gaps
#print axioms SafePdf.Core.Content.Run.annotAll_length
#print axioms SafePdf.Core.Raster.Shading.paintPattern_size
#print axioms SafePdf.Core.Raster.Shading.renderStroke_size

-- Phase 7, task 7.3g: tiling patterns (SafePdf/Core/Raster/Tiling.lean)
#print axioms SafePdf.Core.Raster.Tiling.blitRow_size
#print axioms SafePdf.Core.Raster.Tiling.blitRows_size
#print axioms SafePdf.Core.Raster.Tiling.blit_size
#print axioms SafePdf.Core.Raster.Tiling.forTiles_inv
#print axioms SafePdf.Core.Raster.Tiling.meanFill_size
#print axioms SafePdf.Core.Raster.Tiling.modeA_size
#print axioms SafePdf.Core.Raster.Tiling.modeB_size
#print axioms SafePdf.Core.Raster.Tiling.renderTiling_size
#print axioms SafePdf.Core.Raster.Tiling.renderTilingFill_size

-- Phase 7, task 7.2g: layer dirty rects, fast combine
#print axioms SafePdf.Core.Raster.Clip.u8_eq
#print axioms SafePdf.Core.Raster.Clip.toNat_u8_le
#print axioms SafePdf.Core.Raster.Clip.blend_eq
#print axioms SafePdf.Core.Raster.Transparency.combinePxF_size
#print axioms SafePdf.Core.Raster.Transparency.spanF_size
#print axioms SafePdf.Core.Raster.Transparency.spansF_size
#print axioms SafePdf.Core.Raster.Transparency.combineFast_size
#print axioms SafePdf.Core.Raster.Transparency.openCount_touchStack
#print axioms SafePdf.Core.Raster.Transparency.touchStack_ok
#print axioms SafePdf.Core.Raster.Transparency.touch_sized
#print axioms SafePdf.Core.Raster.Transparency.pushN_size
#print axioms SafePdf.Core.Raster.Transparency.appendN_size
#print axioms SafePdf.Core.Raster.Transparency.copySlice_size
#print axioms SafePdf.Core.Raster.Transparency.copyIn_size
#print axioms SafePdf.Core.Raster.Transparency.copyRows_size
#print axioms SafePdf.Core.Raster.Transparency.fillRows_size
#print axioms SafePdf.Core.Raster.Transparency.beginItem_size
#print axioms SafePdf.Core.Raster.Transparency.beginItem_open_le
#print axioms SafePdf.Core.Raster.Transparency.lumLoop_size
#print axioms SafePdf.Core.Raster.Transparency.alphaLoop_size
#print axioms SafePdf.Core.Raster.Transparency.maskFromSpec_size

-- Phase 8, task 8.3: annotation appearance streams (SafePdf/Core/Annot.lean)
#print axioms SafePdf.Core.Annot.aOf_corners
#print axioms SafePdf.Core.Annot.parseAll_length
#print axioms SafePdf.Core.Annot.widgetsLast_length
#print axioms SafePdf.Core.Annot.collect_drawn_le
#print axioms SafePdf.Core.Annot.runOne_good
#print axioms SafePdf.Core.Annot.foldl_runOne_good
#print axioms SafePdf.Core.Annot.runAppearances_ops_le
#print axioms SafePdf.Core.Annot.runAppearances_items_le
#print axioms SafePdf.Core.Annot.pageAnnots_bounds

-- Phase 7, task 7.2i: integer stroker
#print axioms SafePdf.Core.Raster.Stroke.gridQ_err

-- Phase 7, task 7.2h: fixed-point glyph transforms
#print axioms SafePdf.Core.Raster.Glyph.outlineToDF_size
#print axioms SafePdf.Core.Raster.Glyph.runPathSpec_size_le

-- Phase 8, task 8.2a: Tcl quoting (SafePdf/Shell/App/Tcl*.lean, copied from bib-lean)
#print axioms SafePdf.Shell.App.Tcl.parseWordStr_quote
#print axioms SafePdf.Shell.App.Tcl.parseWord_quoteList
#print axioms SafePdf.Shell.App.Tcl.parseWordStr_quote_append
#print axioms SafePdf.Shell.App.Tcl.parseCmd_render
#print axioms SafePdf.Shell.App.Tcl.parseScript_render
#print axioms SafePdf.Shell.App.Tcl.nul_not_mem_quoteList

-- Phase 7, task 7.2j: bucketed filler, forward differences
#print axioms SafePdf.Core.Raster.Fill.ySort_size
#print axioms SafePdf.Core.Raster.Fill.bezNum_d3
#print axioms SafePdf.Core.Raster.Fill.bezNum_fd0
#print axioms SafePdf.Core.Raster.Fill.cubicLoopFD_eq
#print axioms SafePdf.Core.Raster.Fill.cubicFD_eq

-- Phase 8, task 8.2b: viewer zoom anchoring
#print axioms SafePdf.Shell.App.View.reanchor_self

-- Phase 8, task 8.3b: shared annotation budget, annotation text
#print axioms SafePdf.Core.Annot.docAnnots_shared_ops
#print axioms SafePdf.Core.Annot.withAnnots_glyphs

-- Phase 7, task 7.3h2: tiling strokes, text, full cell painter
#print axioms SafePdf.Core.Raster.Tiling.renderTilingStroke_size
#print axioms SafePdf.Core.Raster.Tiling.paintTilingMask_size
#print axioms SafePdf.Core.Raster.Glyph.renderItemWith_size
#print axioms SafePdf.Core.Raster.Glyph.renderItemWith_tx
#print axioms SafePdf.Core.Raster.Glyph.cellPainterD_size

-- Phase 8, task 8.2c: viewer search soundness
#print axioms SafePdf.Shell.App.Select.findAll_sound

-- Phase 8, task 8.2d: viewer links and history
#print axioms SafePdf.Shell.App.Links.toNat_ofNat_small
#print axioms SafePdf.Shell.App.Links.hexDigit_ascii
#print axioms SafePdf.Shell.App.Links.uriByte_ascii
#print axioms SafePdf.Shell.App.Links.uriText_ascii
#print axioms SafePdf.Shell.App.Links.History.back_push

-- Phase 8, task 8.4: library API (SafePdf/Api.lean)
#print axioms SafePdf.Api.openBytes_strict
#print axioms SafePdf.Api.toPage_toScreen
#print axioms SafePdf.Api.toScreen_toPage
#print axioms SafePdf.Api.toScreen_eq
#print axioms SafePdf.Api.pageText_glyphs_ofCore
#print axioms SafePdf.Api.pageText_glyphs
#print axioms SafePdf.Api.glyph_provenance
#print axioms SafePdf.Api.glyph_codes
#print axioms SafePdf.Api.renderPage_size
#print axioms SafePdf.Api.outline_bounded

-- Phase 8, task 8.3d: NoRotate
#print axioms SafePdf.Core.Annot.noRotate_fixes_corner

-- Phase 7, task 7.3i1: knockout group emission (spec)
#print axioms SafePdf.Spec.Content.paintItems_eq

-- Phase 7, task 7.3j: Type 3 fonts (SafePdf/Core/Raster/Type3.lean)
#print axioms SafePdf.Core.Raster.Type3.renderRun_size
#print axioms SafePdf.Core.Raster.Type3.drawGlyph_size
#print axioms SafePdf.Core.Raster.Type3.drawImages_size
#print axioms SafePdf.Core.Raster.Type3.drawImage_size
#print axioms SafePdf.Core.Raster.Type3.placeNoFit_size

-- Phase 7, task 7.6a: baseline JPEG (SafePdf/Quarantine/DCT.lean)
#print axioms SafePdf.Quarantine.DCT.decode_pixels
#print axioms SafePdf.Quarantine.DCT.finalize_pixels

-- Phase 7, task 7.3k: MuPDF stencil scaler for Type 3 glyphs
#print axioms SafePdf.Core.Raster.Type3.drawImageWith_size
#print axioms SafePdf.Core.Raster.Type3.drawImagesC_size
#print axioms SafePdf.Core.Raster.Type3.drawCached_size

-- Phase 7, task 7.3l: page-wide Type 3 glyph cache
#print axioms SafePdf.Core.Raster.Type3.GlyphCache.insert_count_le
#print axioms SafePdf.Core.Raster.Type3.GlyphCache.insert_bytes_le
-- Phase 7, task 7.7: substitute fonts
#print axioms SafePdf.Core.Raster.Subst.widthTable_length_le
#print axioms SafePdf.Core.Raster.Glyph.substCodes_size
-- Phase 6, task 6.8d: ActualText marked content
#print axioms SafePdf.Core.Text.shownItems_eq_extract
#print axioms SafePdf.Spec.Content.mark_step
#print axioms SafePdf.Core.Content.Interp.markOp_marks_le
-- Phase 9, task 9.5a: incremental-update writer (C7)
#print axioms SafePdf.Spec.Write.c7
#print axioms SafePdf.Spec.Write.writeAnnots_prefix
#print axioms SafePdf.Spec.Write.writeAnnots_chain
#print axioms SafePdf.Spec.Write.writeAnnots_untouched
#print axioms SafePdf.Spec.Write.writeAnnots_open
#print axioms SafePdf.Spec.Write.writeAnnots_annots
#print axioms SafePdf.Spec.Write.plan_marks
#print axioms SafePdf.Spec.Write.plan_page
#print axioms SafePdf.Spec.Write.newDict_lookup_ne
#print axioms SafePdf.Spec.Write.serialize_roundtrip
-- Phase 9, task 9.4: marks model
#print axioms SafePdf.Shell.App.Marks.Store.add_id
#print axioms SafePdf.Shell.App.Marks.Store.add_next
-- Phase 9, task 9.5b: annotation objects for user marks
#print axioms SafePdf.Spec.Write.writeAnnots_aux
#print axioms SafePdf.Core.Write.Annots.utf16_utf16be
#print axioms SafePdf.Core.Write.Annots.textOf_textBytes_utf16
#print axioms SafePdf.Core.Write.Annots.annotDicts_isAnnot
#print axioms SafePdf.Core.Write.Annots.IsAnnot.lookup
#print axioms SafePdf.Core.Write.Annots.build_ok
#print axioms SafePdf.Core.Write.Annots.quadsOf_quadPoints
#print axioms SafePdf.Core.Write.Annots.quadPoints_length
#print axioms SafePdf.Core.Write.Annots.pageDicts_length
#print axioms SafePdf.Core.Write.Annots.decRound_canonical
-- Phase 9, task 9.8: bubble placement
#print axioms SafePdf.Shell.App.Bubble.place_inside
#print axioms SafePdf.Shell.App.Bubble.clampInto_lo
#print axioms SafePdf.Shell.App.Bubble.clampInto_hi
#print axioms SafePdf.Shell.App.Bubble.Ui.escape_closes
-- Phase 6, task 6.8f: text clipped by clip paths
#print axioms SafePdf.Core.Text.unclipped_of_none
-- Phase 9, task 9.5f: annotating encrypted documents (writer rule W10)
#print axioms SafePdf.Spec.Write.writeAnnots_aux_plain
#print axioms SafePdf.Spec.Write.writeAnnots_crypt
#print axioms SafePdf.Spec.Write.sameCrypt_ok
#print axioms SafePdf.Core.Write.Incremental.auxBody_none
#print axioms SafePdf.Core.Write.Encrypt.pkcs7Pad_size
#print axioms SafePdf.Core.Write.Encrypt.pkcs7Pad_mod
#print axioms SafePdf.Core.Write.Encrypt.pkcs7Pad_gt
#print axioms SafePdf.Core.Write.Encrypt.encLen_none
-- Phase 7, task 7.9: render-time tail
#print axioms SafePdf.Core.Raster.Stroke.arcCountGoI_eq
#print axioms SafePdf.Core.Raster.Stroke.arcCount_eq
#print axioms SafePdf.Core.Raster.Stroke.strokePathT_empty
#print axioms SafePdf.Core.Raster.Transparency.restoreAll_size
#print axioms SafePdf.Core.Raster.Transparency.materializeTop_sized
#print axioms SafePdf.Core.Raster.Transparency.materializeS_inv
#print axioms SafePdf.Core.Raster.Transparency.knockItemL_inv
#print axioms SafePdf.Core.Raster.Transparency.paintKL_inv
#print axioms SafePdf.Core.Raster.Transparency.paintKTL_inv
#print axioms SafePdf.Core.Raster.Transparency.pushKnockL_size
-- Phase 9, task 9.3: view-mode layout
#print axioms SafePdf.Shell.App.View.mem_spreadPages
#print axioms SafePdf.Shell.App.View.spreadOf_lt_count
#print axioms SafePdf.Shell.App.View.spreadOf_spreadFirst
#print axioms SafePdf.Shell.App.View.nextPage_spread
#print axioms SafePdf.Shell.App.View.stack_pairwise
-- Phase 7, task 7.9b: per-page form cache
#print axioms SafePdf.Core.Content.Run.formJobT_num
#print axioms SafePdf.Core.Content.Run.FormCache.find?_spec
#print axioms SafePdf.Core.Content.Run.FormCache.code_hit
#print axioms SafePdf.Core.Content.Run.FormCache.code_miss
#print axioms SafePdf.Core.Content.Run.FormCache.code_ok
#print axioms SafePdf.Core.Content.Run.FormCache.code_fst_eq
#print axioms SafePdf.Core.Content.runPageUncached_ops_le
#print axioms SafePdf.Core.Content.runPageUncached_items_le
-- Phase 9, task 9.5g: edits and removals of saved marks (writer rule W11)
#print axioms SafePdf.Spec.Write.c7Update
#print axioms SafePdf.Spec.Write.writeUpdate_prefix
#print axioms SafePdf.Spec.Write.writeUpdate_chain
#print axioms SafePdf.Spec.Write.writeUpdate_untouched
#print axioms SafePdf.Spec.Write.writeUpdate_open
#print axioms SafePdf.Spec.Write.writeUpdate_annots
#print axioms SafePdf.Spec.Write.writeUpdate_sups
#print axioms SafePdf.Spec.Write.writeUpdate_aux
#print axioms SafePdf.Spec.Write.writeUpdate_crypt
#print axioms SafePdf.Spec.Write.planUpdate_edits
#print axioms SafePdf.Spec.Write.plan_removed
#print axioms SafePdf.Spec.Write.plan_sups
#print axioms SafePdf.Spec.Write.mem_kept
#print axioms SafePdf.Spec.Write.newDict_annots_kept
-- Phase 7, task 7.9c: 64-bit chord geometry
#print axioms SafePdf.Core.Raster.Stroke.mulW_toNat
#print axioms SafePdf.Core.Raster.Stroke.mul128_eq
#print axioms SafePdf.Core.Raster.Stroke.sqInv_step
#print axioms SafePdf.Core.Raster.Stroke.sqInv_sqrt
#print axioms SafePdf.Core.Raster.Stroke.sqDigit_toNat
#print axioms SafePdf.Core.Raster.Stroke.isqLoop_eq
#print axioms SafePdf.Core.Raster.Stroke.isqrtW_eq
#print axioms SafePdf.Core.Raster.Stroke.gcd64_eq
#print axioms SafePdf.Core.Raster.Stroke.roundDivI_qr
#print axioms SafePdf.Core.Raster.Stroke.rdivFin_eq
#print axioms SafePdf.Core.Raster.Stroke.shLoop_eq
#print axioms SafePdf.Core.Raster.Stroke.rdiv36_eq
#print axioms SafePdf.Core.Raster.Stroke.mul64_toInt
#print axioms SafePdf.Core.Raster.Stroke.lin64_toInt
#print axioms SafePdf.Core.Raster.Stroke.abs64_toNat
#print axioms SafePdf.Core.Raster.Stroke.IMatW.of_ok
#print axioms SafePdf.Core.Raster.Stroke.ratW_eq
-- Phase 9, task 9.5e: C7 at the value level
#print axioms SafePdf.Spec.Write.writeUpdate_value
#print axioms SafePdf.Spec.Write.writeAnnots_value
#print axioms SafePdf.Spec.Write.c7Value
#print axioms SafePdf.Spec.Write.c7Value_plain
#print axioms SafePdf.Spec.Write.c7ValueAnnots
#print axioms SafePdf.Spec.Write.openFile_self
#print axioms SafePdf.Spec.Write.keys_notLen
#print axioms SafePdf.Spec.WritePrefix.resolveLengthAux_transfer
#print axioms SafePdf.Spec.WritePrefix.resolveLengthAux_det
#print axioms SafePdf.Spec.WritePrefix.parseIndirectResolved_transfer
#print axioms SafePdf.Spec.WritePrefix.fetchCompressed_transfer
#print axioms SafePdf.Spec.WritePrefix.getObject_transfer
#print axioms SafePdf.Spec.WritePrefix.notLen_of_dict
#print axioms SafePdf.Spec.WritePrefix.lookup_eq
#print axioms SafePdf.Spec.WritePrefix.crypt_eq_of_ref
-- Phase 9, task 9.5e2: value-level C7 without side condition
#print axioms SafePdf.Spec.Write.sameHandler_ok
#print axioms SafePdf.Spec.Write.sameState_ok
#print axioms SafePdf.Spec.Write.checkObjects_crypt
#print axioms SafePdf.Spec.Write.writeUpdate_crypt_eq
#print axioms SafePdf.Spec.Write.writeAnnots_crypt_eq
#print axioms SafePdf.Spec.Write.writeUpdate_value'
#print axioms SafePdf.Spec.Write.writeAnnots_value'
#print axioms SafePdf.Spec.Write.c7Value'
#print axioms SafePdf.Spec.Write.c7ValueAnnots'
-- Phase 8, task 8.6: image memory bounds
#print axioms SafePdf.Core.Raster.Image.rowRGBA_size
#print axioms SafePdf.Core.Raster.Image.Src.row_size
#print axioms SafePdf.Core.Raster.Image.gridRow_size
#print axioms SafePdf.Core.Raster.Image.gridRows_size
#print axioms SafePdf.Core.Raster.Image.pushSums_size
#print axioms SafePdf.Core.Raster.Image.boxGrid_size
#print axioms SafePdf.Core.Raster.Image.fitTarget_le
#print axioms SafePdf.Core.Raster.Image.finishTo_dims
-- Phase 9, task 9.9: FreeText and Ink
#print axioms SafePdf.Core.Write.Annots.mkAnnot_lookup
#print axioms SafePdf.Core.Write.Annots.mkAnnot_lookup_first
#print axioms SafePdf.Core.Write.Annots.freeTextDict_shape
#print axioms SafePdf.Core.Write.Annots.inkDict_shape
#print axioms SafePdf.Core.Write.Annots.inkListObj_length
#print axioms SafePdf.Core.Write.Annots.inkListObj_getElem?
#print axioms SafePdf.Core.Write.Annots.strokeNums_length
#print axioms SafePdf.Core.Write.Annots.slots_freeText_ink
#print axioms SafePdf.Shell.App.Bubble.Ui.selectEditor_exclusive
#print axioms SafePdf.Shell.App.Bubble.Ui.toolClick_exclusive
-- Phase 8, task 8.10: pre-sized Flate output, filled buffers
#print axioms SafePdf.Core.Filter.applyStages_cap
#print axioms SafePdf.Core.Filter.applyStagesB_cap
#print axioms SafePdf.Core.Filter.decodeStream_eq
#print axioms SafePdf.Core.Filter.decodeOne_cap
#print axioms SafePdf.Core.Filter.Flate.flateDecode_cap
#print axioms SafePdf.Core.Raster.Clip.filledBuf_eq
#print axioms SafePdf.Core.Doc.OpenSettings.read_dest_page
#print axioms SafePdf.Core.Doc.OpenSettings.titleOf_le
#print axioms SafePdf.Core.Doc.OpenSettings.zoomOf_percent_bounds
#print axioms SafePdf.Core.Doc.OptionalContent.isVisible_inactive
#print axioms SafePdf.Core.Doc.OptionalContent.isVisible_default
#print axioms SafePdf.Core.Doc.OptionalContent.State.set_known
#print axioms SafePdf.Core.Doc.OptionalContent.orderOf_count_le
#print axioms SafePdf.Core.Content.OcMarks.push_visible
#print axioms SafePdf.Core.Content.OcMarks.pop_visible
#print axioms SafePdf.Core.Content.Run.ocKeep_length_le
#print axioms SafePdf.Core.Content.Run.ocKeep_visible
#print axioms SafePdf.Core.Content.Run.bdcVisible_inactive
#print axioms SafePdf.Core.Content.Run.dictVisible_inactive
#print axioms SafePdf.Core.Content.Run.ocTrack_inactive
#print axioms SafePdf.Core.Content.Run.gsStep_oc
#print axioms SafePdf.Core.Content.Run.stepR_oc_visible
#print axioms SafePdf.Core.Content.Run.foldl_oc_visible
#print axioms SafePdf.Core.Content.Run.runOps_oc_visible
#print axioms SafePdf.Core.Doc.Attachments.list_entries_le
#print axioms SafePdf.Core.Doc.Attachments.clean_length_le
#print axioms SafePdf.Core.Doc.Attachments.clean_safe
#print axioms SafePdf.Core.Doc.Attachments.fileNameOf_noSlash
#print axioms SafePdf.Core.Doc.Attachments.decode_size_le
#print axioms SafePdf.Shell.App.Marks.History.undo_record
#print axioms SafePdf.Shell.App.Marks.History.redo_undo
#print axioms SafePdf.Shell.App.Marks.History.undo_redo
#print axioms SafePdf.Shell.App.Marks.History.start_bounded
#print axioms SafePdf.Shell.App.Marks.History.record_bounded
#print axioms SafePdf.Shell.App.Marks.History.undo_bounded
#print axioms SafePdf.Shell.App.Marks.History.redo_bounded
#print axioms SafePdf.Shell.App.Toolbar.Transient.mem_order
#print axioms SafePdf.Shell.App.Toolbar.onEscape_sub
#print axioms SafePdf.Shell.App.Toolbar.onEscape_nonempty
#print axioms SafePdf.Shell.App.Toolbar.mem_onClick
#print axioms SafePdf.Shell.App.Toolbar.onOpen_rivals
#print axioms SafePdf.Shell.App.Toolbar.Transient.not_self_rival
#print axioms SafePdf.Shell.App.View.stepInZ_gt
#print axioms SafePdf.Shell.App.View.stepOutZ_lt
#print axioms SafePdf.Shell.App.View.stepInZ_isSome
#print axioms SafePdf.Shell.App.View.stepOutZ_isSome
#print axioms SafePdf.Shell.App.View.quant_mono
#print axioms SafePdf.Shell.App.View.pctZoom_mono
#print axioms SafePdf.Shell.App.View.zoomSteps_pairwise
#print axioms SafePdf.Shell.App.View.stepOutZ_stepInZ_le
#print axioms SafePdf.Shell.App.Toolbar.Mode.of_default
#print axioms SafePdf.Shell.App.Toolbar.Mode.of_selectTool
#print axioms SafePdf.Shell.App.Toolbar.pressed_unique
#print axioms SafePdf.Shell.App.Toolbar.Mode.of_selectEditor_twice
#print axioms SafePdf.Shell.App.Toolbar.Mode.of_toolClick_twice
#print axioms SafePdf.Shell.App.Select.shape_covers
#print axioms SafePdf.Shell.App.Select.meetAt_spec
#print axioms SafePdf.Shell.App.Select.bandAt_meet
#print axioms SafePdf.Shell.App.Select.bandAt_covers
-- Phase 12, task 12.7: C4 with explicit hypotheses (SafePdf/Spec/RepairAgree.lean)
#print axioms SafePdf.Spec.RepairAgree.c4
#print axioms SafePdf.Spec.RepairAgree.c4_check
#print axioms SafePdf.Spec.RepairAgree.entries_eq
#print axioms SafePdf.Spec.RepairAgree.newestHits_mem_iff
#print axioms SafePdf.Core.Write.Encrypt.aesEncrypt_prefix
#print axioms SafePdf.Core.Write.Encrypt.aesEncrypt_extract
#print axioms SafePdf.Core.Write.Encrypt.aesEncrypt_iv_ne
-- Phase 12, task 12.7a: C4 with free entries (SafePdf/Spec/RepairAgreeFree.lean)
#print axioms SafePdf.Spec.RepairAgreeFree.c4_free
#print axioms SafePdf.Spec.RepairAgreeFree.c4_free_check
#print axioms SafePdf.Spec.RepairAgreeFree.resolveLengthAux_mono
#print axioms SafePdf.Spec.RepairAgreeFree.parseIndirectResolved_mono
#print axioms SafePdf.Spec.RepairAgreeFree.fetchCompressed_mono
#print axioms SafePdf.Spec.RepairAgreeFree.resolve_agree
#print axioms SafePdf.Spec.RepairAgreeFree.getObject_agree
-- Phase 12, task 12.1: true strict mode
#print axioms SafePdf.Core.Open.openFileWith_true
#print axioms SafePdf.Core.Open.openFileWith_false
#print axioms SafePdf.Core.Open.openFileLogged_strictOnly
#print axioms SafePdf.Core.Open.openFileLogged_refused
#print axioms SafePdf.Core.Open.strictOpen_not_repaired
#print axioms SafePdf.Core.Open.openFileWith_false_repaired
#print axioms SafePdf.Core.Open.openFileBLogged_true
#print axioms SafePdf.Core.Open.openFileBLogged_false
#print axioms SafePdf.Core.Open.strictOpenB_not_repaired
#print axioms SafePdf.Core.Open.Session.openLogged_true
#print axioms SafePdf.Core.Open.Session.openLogged_false
#print axioms SafePdf.parseLogged_strictOnly
#print axioms SafePdf.parseLogged_refused
#print axioms SafePdf.Api.openBytes_strict_no_repair
-- Phase 12, task 12.5: invisible-text provenance
#print axioms SafePdf.Core.Text.runGlyphs_visible
#print axioms SafePdf.Core.Text.extract_visible
#print axioms SafePdf.Core.Text.Options.keeps_hiddenWhy
#print axioms SafePdf.Core.Text.Options.hiddenWhy_isSome_of_invisible
-- Phase 12, task 12.7b: C4 with a byte-level hypothesis (SafePdf/Spec/RepairAgreeBytes.lean)
#print axioms SafePdf.Spec.RepairAgreeBytes.c4_bytes
#print axioms SafePdf.Spec.RepairAgreeBytes.c4_bytes_check
#print axioms SafePdf.Spec.RepairAgreeBytes.c4_free_bytes
#print axioms SafePdf.Spec.RepairAgreeBytes.c4_free_bytes_check
#print axioms SafePdf.Spec.RepairAgreeBytes.hits_eq_headers
#print axioms SafePdf.Spec.RepairAgreeBytes.hits_sublist_headers
#print axioms SafePdf.Spec.RepairAgreeBytes.mem_headers
#print axioms SafePdf.Spec.RepairAgreeFree.c4_free_eq
#print axioms SafePdf.Spec.RepairAgreeFree.c4_free_eq_check
#print axioms SafePdf.Spec.RepairAgreeFree.getObject_eq
-- Phase 12, task 12.8: raster error bounds
#print axioms SafePdf.Spec.RasterError.mul_err
#print axioms SafePdf.Spec.RasterError.ctm_err
#print axioms SafePdf.Spec.RasterError.ctm_err_linear
#print axioms SafePdf.Spec.RasterError.ctm_apply_err
#print axioms SafePdf.Spec.RasterError.ofDecimal_err
#print axioms SafePdf.Spec.RasterError.toSub_err
#print axioms SafePdf.Spec.RasterError.polyline_tol
#print axioms SafePdf.Spec.RasterError.device_curve_err
#print axioms SafePdf.Spec.RasterError.qd_err
