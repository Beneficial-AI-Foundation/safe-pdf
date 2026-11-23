import SafePdf.Core.Write.Incremental
import SafePdf.Spec.Unambiguous
import SafePdf.Spec.RoundTripCore
import SafePdf.Spec.WritePrefix
import SafePdf.Spec.Doc

/-!
# C7: the incremental update is conservative (Plan.md §4 C7/S8, §6 Phase 9; task 9.5a)

Plan.md C7: `writeAnnots doc marks = bytes ++ update`; the strict parser on the result yields
every original object unchanged and, as the pages' annotations, exactly the old ones
followed by `marks`. The update is checked by the same parser; there is no writer-side
spec. This file proves, for every successful `Core.Write.Incremental.writeAnnots`:

1. **Prefix** (`writeAnnots_prefix`, `writeAnnots_extends`): the result is
   `doc.file.bytes ++ u` — the original bytes are never modified (S8).
2. **Revision structure** (`writeAnnots_chain`): the result's cross-reference chain is the
   original chain with exactly one new section in front, whose `/Prev` is the original
   `startxref` and whose object numbers are exactly `Plan.keys` (the rewritten pages, the
   new annotations, the auxiliary streams of rule W9, and for an xref-stream update the
   stream itself).
3. **Every other object resolves as before** (`writeAnnots_untouched`): for an object number
   not in `Plan.keys`, `Spec.Unambiguous.resolveEntry` on the result equals that on the
   original — the same cross-reference entry (in-use offset and generation, or object-stream
   container and index), hence the same bytes of the original file.
4. **Strict re-open** (`writeAnnots_open`): `Open.openFile` opens the result strictly
   (`repaired = false`) and fetches every written object exactly as planned.
5. **Annotations** (`writeAnnots_annots`): for each page of `marks`, `annotsOf` on the
   original gives the old list, and on the result the old list followed by references to
   the new objects, each of which fetches to exactly the given annotation dictionary; the
   new objects are fresh (numbers at or above the old `/Size`); every key of the page
   dictionary other than `/Annots` is unchanged (`newDict_lookup_ne`); the plan covers
   exactly `marks` (`plan_marks`) and each planned page is the page at that index
   (`plan_page`).
5a. **Auxiliary streams** (`writeAnnots_aux`, rule W9, task 9.5b): the appearance streams
   passed with the annotations are numbered from the old `/Size` plus the annotation count,
   in order, and each fetches back exactly (dictionary with `/Length`, raw data).
5b. **Encrypted documents** (task 9.5f, rule W10): no statement is weakened. `getObject`
   of the re-opened result decrypts, so facts 4 and 5 say that every written object
   *decrypts* back to exactly the planned plaintext; `writeAnnots_crypt` adds that the result
   has the original's decryption state (file key, methods, `/Encrypt` object). Only the
   auxiliary streams' `/Length` differs (the written, encrypted length, `auxBody`);
   `writeAnnots_aux_plain` restates 9.5b's form for unencrypted documents. That the
   encryption itself (`Core.Write.Encrypt`, RC4 / AES-CBC with an IV derived from the
   caller's seed) is the inverse of `Crypt.decryptBody` is not proved — the primitives are
   vector-tested, not verified (Plan.md §6 Phase 4) — it is *checked* on every write by the
   self-check, and tested on the encrypted fixtures and corpus files.
5c. **Every IV seed** (task 12.4): the writer's entry points take an AES IV seed
   (`ivSeed`, fresh OS randomness in the viewer, `Encrypt` rule E3'); every theorem of this
   file is stated for an arbitrary seed (the section `variable {ivSeed}`), since the proofs
   rest only on the self-check.
6. `serialize_roundtrip`: the serializer is the Phase 1 printer, whose round trip
   `parseObject (serialize o) = o` is M1's `Spec.RoundTripCore.parseObject_print`.
7. **Removal and supersession** (rule W11, task 9.5g; `writeUpdate`, of which `writeAnnots`
   is the add-only case). Facts 1–4 hold for `writeUpdate` as stated (`writeUpdate_prefix`,
   `writeUpdate_chain`, `writeUpdate_untouched`, `writeUpdate_open`, `writeUpdate_aux`,
   `writeUpdate_crypt`), where `Plan.keys` now also contains the superseded numbers. Fact 5
   becomes `writeUpdate_annots`: each edited page's annotation list on the result is the old
   list **without the removed references** (`PagePlan.kept`, a filter of the old list: the
   other elements, superseded references included, keep their order and position relative
   to each other) followed by the new references; every removed reference was on the page
   (`removed ⊆ old`). `writeUpdate_sups`: every superseded object existed in the original
   as a dictionary under that number and generation, is below the old `/Size` and is no
   page object, and the re-opened result fetches **exactly its new dictionary** under the
   same number and generation. `writeUpdate_edits` says the plan covers exactly the given
   edits. `c7Update` bundles them. The 9.5a statements (`writeAnnots_*`, `c7`) are
   unchanged and are now corollaries (for `writeAnnots`, every page plan removes nothing,
   `plan_removed`, and nothing is superseded, `plan_sups`). Two helper lemmas about a page
   plan, `newDict_annots` and `annotItems_newDict`, now take the hypothesis
   `pp.removed = []`; their general forms are `newDict_annots_kept` and
   `annotItems_newDict_kept`.

8. **Every other object keeps its value** (task 9.5e; `writeUpdate_value`,
   `writeAnnots_value`): for a document opened from its own bytes (`hd0`; `openFile_self`
   derives it from `Doc.openDoc`), every object number not in `Plan.keys` fetches on the
   re-opened result exactly what it fetches on the original — every successful
   `OpenDoc.getObject` (any generation, `null` for undefined objects included), with
   indirect `/Length` resolution, object-stream members and decryption — and the result has
   *exactly* the original's decryption state. Side condition `EncKept`: the document is
   unencrypted (`encKept_plain`), or its encryption dictionary is an indirect object whose
   number the update does not write. Proof: `Spec.WritePrefix` (prefix stability of object
   resolution); the numbers in `Plan.keys` are new (above the old `/Size`, no entry) or
   rewritten pages and superseded objects, which fetch as dictionaries and therefore cannot
   be a `/Length` value or an object-stream container (`keys_cases`, `keys_notLen`).
   `c7Value` (general writer), `c7Value_plain` (unencrypted, no side condition) and
   `c7ValueAnnots` (`writeAnnots`) bundle it next to the unchanged `c7` / `c7Update`.
8a. **No side condition** (task 9.5e2; `writeUpdate_value'`, `writeAnnots_value'`,
   `c7Value'`, `c7ValueAnnots'`): fact 8 for *every* successful write — also a direct
   trailer `/Encrypt` dictionary, and an indirect one that the update supersedes (rule W11
   allows superseding any non-page dictionary). The decryption-state equality now comes from
   the writer's self-check: `checkObjects` also requires `sameState` (every field of
   `Crypt.State`: the whole handler incl. `/EncryptMetadata` and the named crypt filters, the
   file key, the `/Encrypt` object, the `/Perms` result), so `checkObjects_crypt` /
   `writeUpdate_crypt_eq` give `d'.crypt = doc.file.crypt` outright; the rest of the proof
   (prefix stability, `keys_notLen`) is unchanged. The old statements (`writeUpdate_value`,
   `writeAnnots_value`, `c7Value`, `c7ValueAnnots`, with `EncKept`) are unchanged and are now
   corollaries; `WritePrefix.crypt_eq_of_ref` (the 9.5e route for an indirect `/Encrypt`) is
   kept, no longer needed.

`c7` bundles 1–5; `c7Update` bundles 1–5 and 7 for the general writer; `c7Value` adds 8,
`c7Value'` adds 8a.

## What is proved by construction, what by the writer's self-check

Facts 2, 4 and the "after" half of 5 rest on the writer's own strict re-parse (rule W8:
`checkChain`, `checkObjects`): `writeAnnots` returns bytes only when they hold, and the
theorems turn those Boolean checks into statements about the parser — via
`Spec.Unambiguous.resolveEntry_append` (prefix stability of the old sections, task 2.12) for
3. The writer is therefore *sound* by proof; that it *succeeds* on well-formed inputs
(completeness: the serializer's section and objects always parse) is tested, not proved
(`Tests/WriteIncremental.lean`, fixtures and corpus).

**Not proved (recorded obstacles):**

* That the update's trailer carries the original `/Encrypt` *by construction* (rule W6).
  Task 9.5e2 closed fact 8 for a direct `/Encrypt` through the self-check (`sameState`,
  option (b) of the task) rather than by a parse-back theorem (option (a)): that would need
  serializer completeness for the cross-reference section — `Xref.Chain.parseSection` on
  `xrefTable` (classic subsections, `trailer` keyword, dictionary) and on the uncompressed
  xref stream (`streamRows`, `/Index`, `/W`, the stream parser with its `/Length`) — which is
  tested, never proved, and would still leave the case of a superseded indirect `/Encrypt`
  object open. The check is exactly as strong as needed: the result's state *is* the
  original's, whatever the trailer says.
* Only successful fetches are claimed stable: an original object whose fetch *fails* may
  fail differently (or succeed) on the result, as in `Spec.PrefixStable`.
The object-level property stays checked by the test suite on every original object of
every fixture and of the corpus sample.
-/

namespace SafePdf.Spec.Write

open SafePdf SafePdf.Core
open SafePdf.Core.Write.Incremental
open SafePdf.Core.Xref (XrefEntry XrefSection Trailer)
open SafePdf.Core.Xref.Chain (Revision loadChain lookupEntry)
open SafePdf.Spec.Unambiguous (resolveEntry)

-- The AES IV seed of the write (task 12.4): every theorem below holds for every seed.
variable {ivSeed : ByteArray}

/-! ## The serializer round trip -/

/-- **Serializer round trip** (M1 reused): the strict object parser reads the serialized
bytes of a canonical object with in-range references back to the same object. -/
theorem serialize_roundtrip (limits : Limits) (o : PdfObject) (hc : o.Canonical)
    (hr : Print.RefsInRange o) (hd : o.depth ≤ limits.maxObjectDepth) :
    ∃ r, ObjParse.parseObject limits ⟨(Write.Serialize.serialize o).toArray⟩ 0 = .ok (o, r) :=
  Spec.RoundTripCore.parseObject_print limits o hc hr hd

/-! ## Unfolding the writer -/

/-- A successful general write (rule W11) comes from a plan whose result passed both
self-checks. -/
theorem writeUpdate_ok {limits : Limits} {doc : Doc.Doc} {edits : Edits}
    {sups : List Supersede} {aux : List AuxStream} {out : ByteArray}
    (h : writeUpdate limits doc edits sups aux ivSeed = .ok out) :
    ∃ p, planUpdate limits doc edits sups aux ivSeed = .ok p ∧ out = result doc.file.bytes p ∧
      checkChain limits doc.file.bytes out p.start p.keys = true ∧
      checkObjects limits out p.objects p.auxExpected p.crypt = true := by
  unfold writeUpdate at h
  split at h
  · cases h
  · rename_i p hp
    dsimp only at h
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true] at hc
      exact ⟨p, hp, rfl, hc.1, hc.2⟩
    · cases h

/-- A successful write comes from a plan whose result passed both self-checks. -/
theorem writeAnnots_ok {limits : Limits} {doc : Doc.Doc} {marks : Marks} {aux : List AuxStream}
    {out : ByteArray}
    (h : writeAnnots limits doc marks aux ivSeed = .ok out) :
    ∃ p, plan limits doc marks aux ivSeed = .ok p ∧ out = result doc.file.bytes p ∧
      checkChain limits doc.file.bytes out p.start p.keys = true ∧
      checkObjects limits out p.objects p.auxExpected p.crypt = true :=
  writeUpdate_ok h

/-- **C7 (1), prefix, general writer** (rule W11): the original bytes are a prefix. -/
theorem writeUpdate_prefix {limits : Limits} {doc : Doc.Doc} {edits : Edits}
    {sups : List Supersede} {aux : List AuxStream} {out : ByteArray}
    (h : writeUpdate limits doc edits sups aux ivSeed = .ok out) : ∃ u, out = doc.file.bytes ++ u := by
  obtain ⟨p, _, rfl, _, _⟩ := writeUpdate_ok h
  exact ⟨_, rfl⟩

/-- The general writer's result extends the original. -/
theorem writeUpdate_extends {limits : Limits} {doc : Doc.Doc} {edits : Edits}
    {sups : List Supersede} {aux : List AuxStream} {out : ByteArray}
    (h : writeUpdate limits doc edits sups aux ivSeed = .ok out) :
    PrefixStable.Extends doc.file.bytes out := by
  obtain ⟨u, rfl⟩ := writeUpdate_prefix h
  exact PrefixStable.Extends.append _ _

/-- **C7 (1), prefix.** The original bytes are a prefix of the result (S8). -/
theorem writeAnnots_prefix {limits : Limits} {doc : Doc.Doc} {marks : Marks} {aux : List AuxStream}
    {out : ByteArray}
    (h : writeAnnots limits doc marks aux ivSeed = .ok out) : ∃ u, out = doc.file.bytes ++ u :=
  writeUpdate_prefix h

/-- The result extends the original (`PrefixStable.Extends`). -/
theorem writeAnnots_extends {limits : Limits} {doc : Doc.Doc} {marks : Marks} {aux : List AuxStream}
    {out : ByteArray}
    (h : writeAnnots limits doc marks aux ivSeed = .ok out) : PrefixStable.Extends doc.file.bytes out :=
  writeUpdate_extends h

/-! ## The chain check -/

/-- What `checkChain` guarantees. -/
theorem checkChain_ok {limits : Limits} {bytes out : ByteArray} {start : Nat} {keys : List Nat}
    (h : checkChain limits bytes out start keys = true) :
    ∃ revs off' sec' tr',
      Xref.findStartxref bytes = .ok start ∧ loadChain limits bytes = .ok revs ∧
      Xref.findStartxref out = .ok off' ∧ bytes.size ≤ off' ∧
      revs.length + 1 ≤ limits.maxRevisions ∧
      Xref.Chain.parseSection limits out off' = .ok (sec', tr') ∧
      Xref.Chain.hybridStm out off' tr' = none ∧ tr'.prev? = some start ∧
      sec'.entries.map Prod.fst = keys := by
  unfold checkChain at h
  split at h
  · rename_i s revs off' h1 h2 h3
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hs, hsz⟩, hrev⟩, hrest⟩ := h
    subst hs
    split at hrest
    · rename_i sec' tr' hsec
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hrest
      exact ⟨revs, off', sec', tr', h1, h2, h3, hsz, hrev, hsec, hrest.1.1, hrest.1.2, hrest.2⟩
    · cases hrest
  · cases h

/-- **C7 (2), revision structure, general writer** (rule W11). -/
theorem writeUpdate_chain {limits : Limits} {doc : Doc.Doc} {edits : Edits}
    {sups : List Supersede} {aux : List AuxStream} {out : ByteArray}
    (h : writeUpdate limits doc edits sups aux ivSeed = .ok out) :
    ∃ p revs sec' tr' off', planUpdate limits doc edits sups aux ivSeed = .ok p ∧
      loadChain limits doc.file.bytes = .ok revs ∧
      loadChain limits out = .ok ((sec', tr', off') :: revs) ∧
      doc.file.bytes.size ≤ off' ∧ tr'.prev? = some p.start ∧
      Xref.findStartxref doc.file.bytes = .ok p.start ∧
      sec'.entries.map Prod.fst = p.keys := by
  obtain ⟨p, hp, hout, hc, _⟩ := writeUpdate_ok h
  obtain ⟨revs, off', sec', tr', h1, h2, h3, hsz, hrev, hsec, hhyb, hprev, hkeys⟩ :=
    checkChain_ok hc
  have hext := writeUpdate_extends h
  refine ⟨p, revs, sec', tr', off', hp, h2, ?_, hsz, hprev, h1, hkeys⟩
  exact Spec.Unambiguous.loadChain_append h2 h1 hext h3 hsz hsec hhyb hprev hrev

/-- **C7 (2), revision structure.** The result's chain is the original chain with one new
section in front: its `/Prev` is the original `startxref`, its object numbers are exactly
the plan's keys. -/
theorem writeAnnots_chain {limits : Limits} {doc : Doc.Doc} {marks : Marks} {aux : List AuxStream}
    {out : ByteArray}
    (h : writeAnnots limits doc marks aux ivSeed = .ok out) :
    ∃ p revs sec' tr' off', plan limits doc marks aux ivSeed = .ok p ∧
      loadChain limits doc.file.bytes = .ok revs ∧
      loadChain limits out = .ok ((sec', tr', off') :: revs) ∧
      doc.file.bytes.size ≤ off' ∧ tr'.prev? = some p.start ∧
      Xref.findStartxref doc.file.bytes = .ok p.start ∧
      sec'.entries.map Prod.fst = p.keys :=
  writeUpdate_chain h

/-- **C7 (3), untouched objects, general writer** (rule W11): an object number that the
update does not write (not a rewritten page, new annotation, superseded object, auxiliary
stream or xref stream) resolves to the same cross-reference entry as in the original. -/
theorem writeUpdate_untouched {limits : Limits} {doc : Doc.Doc} {edits : Edits}
    {sups : List Supersede} {aux : List AuxStream}
    {out : ByteArray} {p : Plan} (h : writeUpdate limits doc edits sups aux ivSeed = .ok out)
    (hp : planUpdate limits doc edits sups aux ivSeed = .ok p) {n : Nat} (hn : n ∉ p.keys) :
    resolveEntry limits out n = resolveEntry limits doc.file.bytes n := by
  obtain ⟨p', revs, sec', tr', off', hp', h2, hnew, _, _, _, hkeys⟩ := writeUpdate_chain h
  rw [hp] at hp'
  cases hp'
  rw [Spec.Unambiguous.resolveEntry_of_cons hnew h2 n]
  have hnone : lookupEntry n sec'.entries = none := by
    rw [Spec.Unambiguous.lookupEntry_eq_none_iff, hkeys]
    exact hn
  rw [hnone]
  cases resolveEntry limits doc.file.bytes n <;> rfl

/-- **C7 (3), untouched objects.** An object number that the update does not write resolves
to the same cross-reference entry in the result as in the original. -/
theorem writeAnnots_untouched {limits : Limits} {doc : Doc.Doc} {marks : Marks}
    {aux : List AuxStream}
    {out : ByteArray} {p : Plan} (h : writeAnnots limits doc marks aux ivSeed = .ok out)
    (hp : plan limits doc marks aux ivSeed = .ok p) {n : Nat} (hn : n ∉ p.keys) :
    resolveEntry limits out n = resolveEntry limits doc.file.bytes n :=
  writeUpdate_untouched h hp hn

/-! ## The object check -/

/-- `bodyIs` succeeds only on exactly that object. -/
theorem bodyIs_eq {r : Except Error IndirectBody} {o : PdfObject} (h : bodyIs r o = true) :
    r = .ok (.obj o) := by
  unfold bodyIs at h
  split at h
  · simp only [decide_eq_true_eq] at h
    rw [h]
  · cases h

/-- `auxIs` succeeds only on exactly that body (rule W9). -/
theorem auxIs_eq {r : Except Error IndirectBody} {b : IndirectBody} (h : auxIs r b = true) :
    r = .ok b := by
  unfold auxIs at h
  split at h
  · simp only [decide_eq_true_eq] at h
    rw [h]
  · cases h

/-- What `sameCrypt` guarantees (rule W10): both states absent, or both present with the
same file key bytes, string and stream methods and encryption-dictionary object. -/
def SameCrypt (a b : Option Crypt.State) : Prop :=
  (a = none ∧ b = none) ∨
  ∃ x y, a = some x ∧ b = some y ∧ x.fileKey.data = y.fileKey.data ∧
    x.handler.strF = y.handler.strF ∧ x.handler.stmF = y.handler.stmF ∧ x.encRef = y.encRef

/-- `sameCrypt` decides `SameCrypt`. -/
theorem sameCrypt_ok {a b : Option Crypt.State} (h : sameCrypt a b = true) : SameCrypt a b := by
  unfold SameCrypt
  cases a with
  | none =>
    cases b with
    | none => exact Or.inl ⟨rfl, rfl⟩
    | some y => simp [sameCrypt] at h
  | some x =>
    cases b with
    | none => simp [sameCrypt] at h
    | some y =>
      simp only [sameCrypt, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      exact Or.inr ⟨x, y, rfl, rfl, h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- What `checkObjects` guarantees. -/
theorem checkObjects_ok {limits : Limits} {out : ByteArray}
    {objs : List (Nat × Nat × PdfObject)} {aux : List (Nat × IndirectBody)}
    {crypt : Option Crypt.State}
    (h : checkObjects limits out objs aux crypt = true) :
    ∃ d', Open.openFile limits out = .ok d' ∧ d'.repaired = false ∧
      (∀ o ∈ objs, d'.getObject limits o.1 o.2.1 = .ok (.obj o.2.2)) ∧
      (∀ a ∈ aux, d'.getObject limits a.1 0 = .ok a.2) ∧ SameCrypt d'.crypt crypt := by
  unfold checkObjects at h
  split at h
  · rename_i d' hd
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at h
    exact ⟨d', hd, h.1.1.1.1, fun o ho => bodyIs_eq (h.1.1.1.2 o ho),
      fun a ha => auxIs_eq (h.1.1.2 a ha), sameCrypt_ok h.1.2⟩
  · cases h

/-- `sameHandler` decides equality of security handlers (task 9.5e2). -/
theorem sameHandler_ok {a b : Crypt.Handler} (h : sameHandler a b = true) : a = b := by
  obtain ⟨v, r, kl, p, ⟨o⟩, ⟨u⟩, ⟨oe⟩, ⟨ue⟩, ⟨pm⟩, em, sm, sf, fl⟩ := a
  obtain ⟨v', r', kl', p', ⟨o'⟩, ⟨u'⟩, ⟨oe'⟩, ⟨ue'⟩, ⟨pm'⟩, em', sm', sf', fl'⟩ := b
  simp only [sameHandler, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := h
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  rfl

/-- `sameState` decides equality of decryption states (task 9.5e2). -/
theorem sameState_ok {a b : Option Crypt.State} (h : sameState a b = true) : a = b := by
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some _ => simp [sameState] at h
  | some x =>
    cases b with
    | none => simp [sameState] at h
    | some y =>
      obtain ⟨hx, ⟨fk⟩, er, po⟩ := x
      obtain ⟨hy, ⟨fk'⟩, er', po'⟩ := y
      simp only [sameState, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨hh, hk⟩, he⟩, hp⟩ := h
      have := sameHandler_ok hh
      subst this hk he hp
      rfl

/-- **The object check fixes the decryption state** (task 9.5e2): a passing `checkObjects`
re-opens the result with exactly the state `crypt` (`sameState`). -/
theorem checkObjects_crypt {limits : Limits} {out : ByteArray}
    {objs : List (Nat × Nat × PdfObject)} {aux : List (Nat × IndirectBody)}
    {crypt : Option Crypt.State}
    (h : checkObjects limits out objs aux crypt = true) :
    ∃ d', Open.openFile limits out = .ok d' ∧ d'.crypt = crypt := by
  unfold checkObjects at h
  split at h
  · rename_i d' hd
    simp only [Bool.and_eq_true] at h
    exact ⟨d', hd, sameState_ok h.2⟩
  · cases h

/-- **C7 (4), strict re-open, general writer** (rule W11): every written object — the
superseded ones included — fetches exactly as planned. -/
theorem writeUpdate_open {limits : Limits} {doc : Doc.Doc} {edits : Edits}
    {sups : List Supersede} {aux : List AuxStream} {out : ByteArray}
    (h : writeUpdate limits doc edits sups aux ivSeed = .ok out) :
    ∃ p d', planUpdate limits doc edits sups aux ivSeed = .ok p ∧ Open.openFile limits out = .ok d' ∧
      d'.repaired = false ∧
      (∀ o ∈ p.objects, d'.getObject limits o.1 o.2.1 = .ok (.obj o.2.2)) ∧
      (∀ a ∈ p.aux, d'.getObject limits a.1 0 = .ok (auxBody p.crypt a.2)) ∧
      SameCrypt d'.crypt p.crypt := by
  obtain ⟨p, hp, _, _, hc⟩ := writeUpdate_ok h
  obtain ⟨d', hd, hr, hobj, haux, hcr⟩ := checkObjects_ok hc
  refine ⟨p, d', hp, hd, hr, hobj, fun a ha => ?_, hcr⟩
  exact haux (a.1, auxBody p.crypt a.2) (List.mem_map.mpr ⟨a, ha, rfl⟩)

/-- **C7 (4), strict re-open.** The result opens strictly and every written object fetches
exactly as planned — for an encrypted document, after decryption by the reader (rule W10);
the result's decryption state agrees with the plan's (the original's, `plan_ok`). -/
theorem writeAnnots_open {limits : Limits} {doc : Doc.Doc} {marks : Marks} {aux : List AuxStream}
    {out : ByteArray}
    (h : writeAnnots limits doc marks aux ivSeed = .ok out) :
    ∃ p d', plan limits doc marks aux ivSeed = .ok p ∧ Open.openFile limits out = .ok d' ∧
      d'.repaired = false ∧
      (∀ o ∈ p.objects, d'.getObject limits o.1 o.2.1 = .ok (.obj o.2.2)) ∧
      (∀ a ∈ p.aux, d'.getObject limits a.1 0 = .ok (auxBody p.crypt a.2)) ∧
      SameCrypt d'.crypt p.crypt :=
  writeUpdate_open h

/-! ## The plan -/

/-- `numberFrom` keeps the dictionaries. -/
theorem numberFrom_snd (n : Nat) (ms : List Dict) : (numberFrom n ms).map Prod.snd = ms := by
  induction ms generalizing n with
  | nil => rfl
  | cons m ms ih => simp [numberFrom, ih]

/-- `numberFrom n` numbers from `n` on. -/
theorem numberFrom_ge {n : Nat} {ms : List Dict} {a : Nat × Dict} (h : a ∈ numberFrom n ms) :
    n ≤ a.1 := by
  induction ms generalizing n with
  | nil => simp [numberFrom] at h
  | cons m ms ih =>
    simp only [numberFrom, List.mem_cons] at h
    rcases h with rfl | h
    · exact Nat.le_refl _
    · have := ih h
      omega

/-- What a planned page is (rules W2, W4). -/
structure PageOk (limits : Limits) (doc : Doc.Doc) (next : Nat) (pp : PagePlan) : Prop where
  /-- It is the page at its index. -/
  page : ∃ pg, doc.pages[pp.index]? = some pg ∧ pg.num = pp.num ∧ pg.gen = pp.gen
  /-- Its dictionary as the original opens it. -/
  dict : doc.file.getObject limits pp.num pp.gen = .ok (.obj (.dict pp.dict))
  /-- Its original annotation list. -/
  old : annotItems doc.file limits pp.dict = .ok pp.old
  /-- The new annotations are numbered from `next` on. -/
  fresh : ∀ a ∈ pp.annots, next ≤ a.1

/-- What a planned page edit adds to `PageOk` (rule W11): the removed references, each on
the page's old list. -/
theorem planEditPage_ok {limits : Limits} {doc : Doc.Doc} {next : Nat} {pe : PageEdit}
    {pp : PagePlan} (h : planEditPage limits doc next pe = .ok pp) :
    PageOk limits doc next pp ∧ pp.index = pe.index ∧ pp.annots = numberFrom next pe.add ∧
      pp.removed = refObjs pe.remove ∧ ∀ r ∈ pp.removed, r ∈ pp.old := by
  unfold planEditPage at h
  split at h
  · cases h
  · rename_i pg hpg
    split at h
    · split at h
      · rename_i pd hpd
        split at h
        · rename_i old hold
          split at h
          · rename_i hrem
            cases h
            refine ⟨⟨⟨pg, hpg, rfl, rfl⟩, hpd, hold, fun a ha => numberFrom_ge ha⟩, rfl, rfl,
              rfl, fun r hr => ?_⟩
            simp only [List.all_eq_true, decide_eq_true_eq] at hrem
            exact hrem r hr
          · cases h
        · cases h
      · cases h
      · cases h
    · cases h

/-- One planned page. -/
theorem planPage_ok {limits : Limits} {doc : Doc.Doc} {next : Nat} {pm : Nat × List Dict}
    {pp : PagePlan} (h : planPage limits doc next pm = .ok pp) :
    PageOk limits doc next pp ∧ pp.index = pm.1 ∧ pp.annots = numberFrom next pm.2 := by
  obtain ⟨h1, h2, h3, _⟩ := planEditPage_ok h
  exact ⟨h1, h2, h3⟩

/-- All planned page edits (rule W11): they cover exactly `edits` (index, removed references,
added dictionaries), each is a `PageOk` with annotation numbers at or above `next`, and its
removed references are on its old list. -/
theorem planEditPages_ok {limits : Limits} {doc : Doc.Doc} :
    ∀ {next : Nat} {edits : Edits} {pps : List PagePlan},
      planEditPages limits doc next edits = .ok pps →
      pps.map (fun pp => (pp.index, pp.removed, pp.annots.map Prod.snd)) =
          edits.map (fun e => (e.index, refObjs e.remove, e.add)) ∧
        ∀ pp ∈ pps, PageOk limits doc next pp ∧ ∀ r ∈ pp.removed, r ∈ pp.old
  | next, [], pps, h => by
    simp only [planEditPages, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, fun _ h => by cases h⟩
  | next, pe :: rest, pps, h => by
    simp only [planEditPages] at h
    split at h
    · cases h
    · rename_i pp hpp
      split at h
      · cases h
      · rename_i pps' hpps
        cases h
        obtain ⟨hok, hidx, hann, hrem, hsub⟩ := planEditPage_ok hpp
        obtain ⟨hm, hall⟩ := planEditPages_ok hpps
        refine ⟨?_, ?_⟩
        · simp only [List.map_cons, hm, hidx, hann, hrem, numberFrom_snd]
        · intro q hq
          rcases List.mem_cons.mp hq with rfl | hq
          · exact ⟨hok, hsub⟩
          · have hq' := (hall q hq).1
            exact ⟨⟨hq'.page, hq'.dict, hq'.old, fun a ha => by
              have := hq'.fresh a ha
              omega⟩, (hall q hq).2⟩

/-- All planned pages: they cover exactly `marks`, and each is a `PageOk` with annotation
numbers at or above `next`. -/
theorem planPages_ok {limits : Limits} {doc : Doc.Doc} {next : Nat} {marks : Marks}
    {pps : List PagePlan} (h : planPages limits doc next marks = .ok pps) :
    pps.map (fun pp => (pp.index, pp.annots.map Prod.snd)) = marks ∧
      ∀ pp ∈ pps, PageOk limits doc next pp := by
  obtain ⟨hm, hall⟩ := planEditPages_ok h
  refine ⟨?_, fun pp hpp => (hall pp hpp).1⟩
  have := congrArg (List.map fun t => (t.1, t.2.2)) hm
  simp only [List.map_map] at this
  rw [show (fun pp : PagePlan => (pp.index, pp.annots.map Prod.snd)) =
      (fun t : Nat × List PdfObject × List Dict => (t.1, t.2.2)) ∘
        (fun pp : PagePlan => (pp.index, pp.removed, pp.annots.map Prod.snd)) from rfl, this]
  induction marks with
  | nil => rfl
  | cons m ms ih => simp [PageEdit.ofMarks, Function.comp_def]

/-- An add-only page plan removes nothing (rule W11 for `writeAnnots`). -/
theorem planPages_removed {limits : Limits} {doc : Doc.Doc} {next : Nat} {marks : Marks}
    {pps : List PagePlan} (h : planPages limits doc next marks = .ok pps) :
    ∀ pp ∈ pps, pp.removed = [] := by
  obtain ⟨hm, _⟩ := planEditPages_ok h
  intro pp hpp
  have hmem : (pp.index, pp.removed, pp.annots.map Prod.snd) ∈
      (marks.map PageEdit.ofMarks).map (fun e => (e.index, refObjs e.remove, e.add)) := by
    rw [← hm]
    exact List.mem_map.mpr ⟨pp, hpp, rfl⟩
  simp only [List.map_map, List.mem_map, Function.comp_def, PageEdit.ofMarks, refObjs,
    List.map_nil] at hmem
  obtain ⟨_, _, he⟩ := hmem
  simp only [Prod.mk.injEq] at he
  exact he.2.1.symm

/-- What `supOk` guarantees (rule W11). -/
theorem supOk_ok {limits : Limits} {doc : Doc.Doc} {size : Nat} {s : Supersede}
    (h : supOk limits doc size s = true) :
    s.1 < size ∧ (∀ pg ∈ doc.pages.toList, pg.num ≠ s.1) ∧
      ∃ od, doc.file.getObject limits s.1 s.2.1 = .ok (.obj (.dict od)) := by
  unfold supOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Array.all_eq_true_iff_forall_mem,
    bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨hlt, hpg⟩, _⟩, hget⟩ := h
  refine ⟨hlt, fun pg hpg' => hpg pg (Array.mem_toList_iff.mp hpg'), ?_⟩
  split at hget
  · rename_i od hod
    exact ⟨od, hod⟩
  · cases hget

/-- What a successful general plan says about its input (rules W1–W3, W9–W11). -/
theorem planUpdate_ok {limits : Limits} {doc : Doc.Doc} {edits : Edits} {sups : List Supersede}
    {aux : List AuxStream} {p : Plan}
    (h : planUpdate limits doc edits sups aux ivSeed = .ok p) :
    doc.file.repaired = false ∧ p.crypt = doc.file.crypt ∧
      p.size = doc.file.trailer.size ∧
      planEditPages limits doc doc.file.trailer.size edits = .ok p.pages ∧
      p.aux = numberAux (doc.file.trailer.size + (p.pages.map fun pp => pp.annots.length).sum)
        aux ∧
      p.sups = sups ∧ (sups.map Prod.fst).Nodup ∧
      ∀ s ∈ sups, supOk limits doc doc.file.trailer.size s = true := by
  unfold planUpdate at h
  simp only at h
  split at h
  · cases h
  · rename_i hrep
    split at h
    · cases h
    · rename_i henc
      split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · rename_i hnd
            split at h
            · cases h
            · rename_i hsok
              split at h
              · cases h
              · split at h
                · cases h
                · rename_i pps hpps
                  split at h
                  · cases h
                  · split at h
                    · cases h
                      simp only [Bool.not_eq_true] at hrep
                      simp only [Bool.not_eq_true', decide_eq_false_iff_not,
                        Classical.not_not] at hnd
                      simp only [Bool.not_eq_true', Bool.not_eq_false, List.all_eq_true] at hsok
                      exact ⟨hrep, rfl, rfl, hpps, rfl, rfl, hnd, hsok⟩
                    · cases h
                    · cases h

/-- What a successful plan says about its input (rules W1–W3, W9, W10). -/
theorem plan_ok {limits : Limits} {doc : Doc.Doc} {marks : Marks} {aux : List AuxStream}
    {p : Plan}
    (h : plan limits doc marks aux ivSeed = .ok p) :
    doc.file.repaired = false ∧ p.crypt = doc.file.crypt ∧
      p.size = doc.file.trailer.size ∧
      planPages limits doc doc.file.trailer.size marks = .ok p.pages ∧
      p.aux = numberAux (doc.file.trailer.size + (p.pages.map fun pp => pp.annots.length).sum)
        aux := by
  obtain ⟨h1, h2, h3, h4, h5, _⟩ := planUpdate_ok h
  exact ⟨h1, h2, h3, h4, h5⟩

/-- `writeAnnots`'s plan supersedes nothing (rule W11). -/
theorem plan_sups {limits : Limits} {doc : Doc.Doc} {marks : Marks} {aux : List AuxStream}
    {p : Plan} (h : plan limits doc marks aux ivSeed = .ok p) : p.sups = [] :=
  (planUpdate_ok h).2.2.2.2.2.1

/-- `writeAnnots`'s page plans remove nothing (rule W11). -/
theorem plan_removed {limits : Limits} {doc : Doc.Doc} {marks : Marks} {aux : List AuxStream}
    {p : Plan} (h : plan limits doc marks aux ivSeed = .ok p) : ∀ pp ∈ p.pages, pp.removed = [] :=
  planPages_removed (plan_ok h).2.2.2.1

/-- **The plan covers exactly `marks`**: page indices and annotation dictionaries, in order. -/
theorem plan_marks {limits : Limits} {doc : Doc.Doc} {marks : Marks} {aux : List AuxStream}
    {p : Plan}
    (h : plan limits doc marks aux ivSeed = .ok p) :
    p.pages.map (fun pp => (pp.index, pp.annots.map Prod.snd)) = marks :=
  (planPages_ok (plan_ok h).2.2.2.1).1

/-- **Each planned page is the page at its index**, read from the original document; the
new annotation numbers are fresh (at or above the original `/Size`). -/
theorem plan_page {limits : Limits} {doc : Doc.Doc} {marks : Marks} {aux : List AuxStream}
    {p : Plan}
    (h : plan limits doc marks aux ivSeed = .ok p) {pp : PagePlan} (hpp : pp ∈ p.pages) :
    PageOk limits doc doc.file.trailer.size pp :=
  (planPages_ok (plan_ok h).2.2.2.1).2 pp hpp

/-- **The general plan covers exactly `edits`** (rule W11): page indices, removed references
and added dictionaries, in order. -/
theorem planUpdate_edits {limits : Limits} {doc : Doc.Doc} {edits : Edits}
    {sups : List Supersede} {aux : List AuxStream} {p : Plan}
    (h : planUpdate limits doc edits sups aux ivSeed = .ok p) :
    p.pages.map (fun pp => (pp.index, pp.removed, pp.annots.map Prod.snd)) =
      edits.map (fun e => (e.index, refObjs e.remove, e.add)) :=
  (planEditPages_ok (planUpdate_ok h).2.2.2.1).1

/-- Each page of a general plan is a `PageOk` whose removed references are on its old list. -/
theorem planUpdate_page {limits : Limits} {doc : Doc.Doc} {edits : Edits}
    {sups : List Supersede} {aux : List AuxStream} {p : Plan}
    (h : planUpdate limits doc edits sups aux ivSeed = .ok p) {pp : PagePlan} (hpp : pp ∈ p.pages) :
    PageOk limits doc doc.file.trailer.size pp ∧ ∀ r ∈ pp.removed, r ∈ pp.old :=
  (planEditPages_ok (planUpdate_ok h).2.2.2.1).2 pp hpp

/-! ## Page dictionaries -/

/-- Without removals the kept list is the old list. -/
theorem kept_of_removed_nil {pp : PagePlan} (h : pp.removed = []) : pp.kept = pp.old := by
  unfold PagePlan.kept
  rw [h]
  simp

/-- The kept list is the old list filtered: an old element stays exactly when it is not
removed, and the kept ones keep their order (rule W11). -/
theorem mem_kept {pp : PagePlan} {o : PdfObject} : o ∈ pp.kept ↔ o ∈ pp.old ∧ o ∉ pp.removed := by
  simp [PagePlan.kept]

/-- The rewritten page dictionary has the new `/Annots` array (rule W11: the kept old
references, then the new ones). -/
theorem newDict_annots_kept (pp : PagePlan) :
    Dict.get? pp.newDict nameAnnots = some (.array (pp.kept ++ pp.refs)) := by
  simp [PagePlan.newDict, Dict.get?, lookup_setKey]

/-- The rewritten page dictionary has the new `/Annots` array (no removals). -/
theorem newDict_annots (pp : PagePlan) (h : pp.removed = []) :
    Dict.get? pp.newDict nameAnnots = some (.array (pp.old ++ pp.refs)) := by
  rw [newDict_annots_kept, kept_of_removed_nil h]

/-- **Every other key of the page dictionary is unchanged.** -/
theorem newDict_lookup_ne (pp : PagePlan) {k : Name} (hk : k ≠ nameAnnots) :
    Dict.lookup pp.newDict k = Dict.lookup pp.dict k :=
  lookup_setKey_ne _ _ hk

/-- The annotation list of the rewritten page dictionary (rule W11). -/
theorem annotItems_newDict_kept (d : Open.OpenDoc) (limits : Limits) (pp : PagePlan) :
    annotItems d limits pp.newDict = .ok (pp.kept ++ pp.refs) := by
  simp [annotItems, newDict_annots_kept]

/-- The annotation list of the rewritten page dictionary (no removals). -/
theorem annotItems_newDict (d : Open.OpenDoc) (limits : Limits) (pp : PagePlan)
    (h : pp.removed = []) :
    annotItems d limits pp.newDict = .ok (pp.old ++ pp.refs) := by
  rw [annotItems_newDict_kept, kept_of_removed_nil h]

/-- A page's objects are among the plan's. -/
theorem mem_objects {p : Plan} {pp : PagePlan} (hpp : pp ∈ p.pages) {o : Nat × Nat × PdfObject}
    (ho : o ∈ pp.objects) : o ∈ p.objects :=
  List.mem_append_left _ (List.mem_flatMap.mpr ⟨pp, hpp, ho⟩)

/-- A superseded object is among the plan's objects (rule W11). -/
theorem mem_objects_sup {p : Plan} {s : Supersede} (hs : s ∈ p.sups) :
    (s.1, s.2.1, PdfObject.dict s.2.2) ∈ p.objects :=
  List.mem_append_right _ (List.mem_map.mpr ⟨s, hs, rfl⟩)

/-- **C7 (5), annotations, general writer** (rule W11). For every page of the plan: the
original annotation list is `pp.old`, the removed references are on it, and on the result
the list is `pp.kept` (the old list without the removed references, in order) followed by
`pp.refs`; each new reference fetches exactly its annotation dictionary; the new numbers
are fresh; the page fetches as its rewritten dictionary. -/
theorem writeUpdate_annots {limits : Limits} {doc : Doc.Doc} {edits : Edits}
    {sups : List Supersede} {aux : List AuxStream} {out : ByteArray}
    (h : writeUpdate limits doc edits sups aux ivSeed = .ok out) :
    ∃ p d', planUpdate limits doc edits sups aux ivSeed = .ok p ∧ Open.openFile limits out = .ok d' ∧
      d'.repaired = false ∧
      p.pages.map (fun pp => (pp.index, pp.removed, pp.annots.map Prod.snd)) =
        edits.map (fun e => (e.index, refObjs e.remove, e.add)) ∧
      ∀ pp ∈ p.pages,
        annotsOf doc.file limits pp.num pp.gen = .ok pp.old ∧
        (∀ r ∈ pp.removed, r ∈ pp.old) ∧
        annotsOf d' limits pp.num pp.gen = .ok (pp.kept ++ pp.refs) ∧
        pp.refs = pp.annots.map (fun a => .ref a.1 0) ∧
        (∀ a ∈ pp.annots, d'.getObject limits a.1 0 = .ok (.obj (.dict a.2)) ∧
          doc.file.trailer.size ≤ a.1) ∧
        d'.getObject limits pp.num pp.gen = .ok (.obj (.dict pp.newDict)) := by
  obtain ⟨p, d', hp, hd, hr, hobj, _, _⟩ := writeUpdate_open h
  refine ⟨p, d', hp, hd, hr, planUpdate_edits hp, fun pp hpp => ?_⟩
  obtain ⟨hok, hsub⟩ := planUpdate_page hp hpp
  have hpage : d'.getObject limits pp.num pp.gen = .ok (.obj (.dict pp.newDict)) :=
    hobj (pp.num, pp.gen, .dict pp.newDict) (mem_objects hpp (by simp [PagePlan.objects]))
  refine ⟨?_, hsub, ?_, rfl, fun a ha => ⟨?_, hok.fresh a ha⟩, hpage⟩
  · simp only [annotsOf, hok.dict, hok.old]
  · simp only [annotsOf, hpage, annotItems_newDict_kept]
  · exact hobj (a.1, 0, .dict a.2) (mem_objects hpp (by
      simp only [PagePlan.objects, List.mem_append, List.mem_map, List.mem_singleton]
      exact Or.inl ⟨a, ha, rfl⟩))

/-- **C7 (5b), superseded objects** (rule W11). For a successful general write, the plan
supersedes exactly `sups`; each superseded object existed in the original as a dictionary
under that number and generation, its number is below the original `/Size`, distinct from
the other superseded numbers, and not the object of any page; and the strictly re-opened
result fetches under the same number and generation **exactly the new dictionary** (for an
encrypted document after decryption, rule W10). -/
theorem writeUpdate_sups {limits : Limits} {doc : Doc.Doc} {edits : Edits}
    {sups : List Supersede} {aux : List AuxStream} {out : ByteArray}
    (h : writeUpdate limits doc edits sups aux ivSeed = .ok out) :
    ∃ p d', planUpdate limits doc edits sups aux ivSeed = .ok p ∧ Open.openFile limits out = .ok d' ∧
      p.sups = sups ∧ (sups.map Prod.fst).Nodup ∧
      ∀ s ∈ sups,
        s.1 < doc.file.trailer.size ∧ (∀ pg ∈ doc.pages.toList, pg.num ≠ s.1) ∧
        (∃ od, doc.file.getObject limits s.1 s.2.1 = .ok (.obj (.dict od))) ∧
        d'.getObject limits s.1 s.2.1 = .ok (.obj (.dict s.2.2)) := by
  obtain ⟨p, d', hp, hd, _, hobj, _, _⟩ := writeUpdate_open h
  obtain ⟨_, _, _, _, _, hs, hnd, hok⟩ := planUpdate_ok hp
  refine ⟨p, d', hp, hd, hs, hnd, fun s hsm => ?_⟩
  obtain ⟨h1, h2, h3⟩ := supOk_ok (hok s hsm)
  exact ⟨h1, h2, h3, hobj _ (mem_objects_sup (hs ▸ hsm))⟩

/-- **C7 (5), annotations.** For every page of the plan: the original annotation list is
`pp.old`; on the result it is `pp.old` followed by `pp.refs`; each new reference fetches
exactly its annotation dictionary; the new numbers are fresh. -/
theorem writeAnnots_annots {limits : Limits} {doc : Doc.Doc} {marks : Marks} {aux : List AuxStream}
    {out : ByteArray}
    (h : writeAnnots limits doc marks aux ivSeed = .ok out) :
    ∃ p d', plan limits doc marks aux ivSeed = .ok p ∧ Open.openFile limits out = .ok d' ∧
      d'.repaired = false ∧
      p.pages.map (fun pp => (pp.index, pp.annots.map Prod.snd)) = marks ∧
      ∀ pp ∈ p.pages,
        annotsOf doc.file limits pp.num pp.gen = .ok pp.old ∧
        annotsOf d' limits pp.num pp.gen = .ok (pp.old ++ pp.refs) ∧
        pp.refs = pp.annots.map (fun a => .ref a.1 0) ∧
        (∀ a ∈ pp.annots, d'.getObject limits a.1 0 = .ok (.obj (.dict a.2)) ∧
          doc.file.trailer.size ≤ a.1) ∧
        d'.getObject limits pp.num pp.gen = .ok (.obj (.dict pp.newDict)) := by
  obtain ⟨p, d', hp, hd, hr, _, hall⟩ := writeUpdate_annots h
  refine ⟨p, d', hp, hd, hr, plan_marks hp, fun pp hpp => ?_⟩
  obtain ⟨h1, _, h3, h4, h5, h6⟩ := hall pp hpp
  rw [kept_of_removed_nil (plan_removed hp pp hpp)] at h3
  exact ⟨h1, h3, h4, h5, h6⟩

/-- `numberAux` keeps the streams. -/
theorem numberAux_snd (n : Nat) (as : List AuxStream) : (numberAux n as).map Prod.snd = as := by
  induction as generalizing n with
  | nil => rfl
  | cons a as ih => simp [numberAux, ih]

/-- `numberAux n` numbers consecutively from `n`: stream `j` gets `n + j`. -/
theorem numberAux_fst (n : Nat) (as : List AuxStream) :
    (numberAux n as).map Prod.fst = (List.range as.length).map (n + ·) := by
  induction as generalizing n with
  | nil => rfl
  | cons a as ih =>
    simp only [numberAux, List.map_cons, List.length_cons, List.range_succ_eq_map, ih,
      List.map_map, Nat.add_zero]
    congr 1
    apply List.map_congr_left
    intro j _
    simp only [Function.comp, Nat.succ_eq_add_one]
    omega

/-- **Auxiliary streams, general writer** (rules W9–W11): numbered from the original `/Size`
plus the number of added annotations (superseded objects take no new numbers). -/
theorem writeUpdate_aux {limits : Limits} {doc : Doc.Doc} {edits : Edits}
    {sups : List Supersede} {aux : List AuxStream}
    {out : ByteArray} (h : writeUpdate limits doc edits sups aux ivSeed = .ok out) :
    ∃ p d', planUpdate limits doc edits sups aux ivSeed = .ok p ∧ Open.openFile limits out = .ok d' ∧
      p.aux.map Prod.snd = aux ∧
      p.aux.map Prod.fst = (List.range aux.length).map
        (doc.file.trailer.size + (p.pages.map fun pp => pp.annots.length).sum + ·) ∧
      ∀ a ∈ p.aux, d'.getObject limits a.1 0 = .ok (auxBody doc.file.crypt a.2) := by
  obtain ⟨p, d', hp, hd, _, _, haux, _⟩ := writeUpdate_open h
  have hn := (planUpdate_ok hp).2.2.2.2.1
  have hc := (planUpdate_ok hp).2.1
  exact ⟨p, d', hp, hd, by rw [hn, numberAux_snd], by rw [hn, numberAux_fst],
    fun a ha => hc ▸ haux a ha⟩

/-- **Auxiliary streams (rules W9, W10).** For a successful write with auxiliary streams
`aux` (task 9.5b: appearance streams), the plan numbers them consecutively from the original
`/Size` plus the number of new annotations, in order, and each fetches from the strictly
re-opened result as exactly that stream with `/Length` set to the length of its written
data (`auxBody`: the data length for an unencrypted document, see `writeAnnots_aux_plain`;
the encrypted length `Encrypt.encLen` for an encrypted one, whose data the reader decrypts
back to exactly the given bytes). -/
theorem writeAnnots_aux {limits : Limits} {doc : Doc.Doc} {marks : Marks} {aux : List AuxStream}
    {out : ByteArray} (h : writeAnnots limits doc marks aux ivSeed = .ok out) :
    ∃ p d', plan limits doc marks aux ivSeed = .ok p ∧ Open.openFile limits out = .ok d' ∧
      p.aux.map Prod.snd = aux ∧
      p.aux.map Prod.fst = (List.range aux.length).map
        (doc.file.trailer.size + (p.pages.map fun pp => pp.annots.length).sum + ·) ∧
      ∀ a ∈ p.aux, d'.getObject limits a.1 0 = .ok (auxBody doc.file.crypt a.2) :=
  writeUpdate_aux h

/-- **Auxiliary streams of an unencrypted document** (rule W9, the 9.5b statement): each
fetches back as exactly `a.body` (`/Length` = its data length). -/
theorem writeAnnots_aux_plain {limits : Limits} {doc : Doc.Doc} {marks : Marks}
    {aux : List AuxStream} {out : ByteArray} (h : writeAnnots limits doc marks aux ivSeed = .ok out)
    (hplain : doc.file.crypt = none) :
    ∃ p d', plan limits doc marks aux ivSeed = .ok p ∧ Open.openFile limits out = .ok d' ∧
      p.aux.map Prod.snd = aux ∧
      ∀ a ∈ p.aux, d'.getObject limits a.1 0 = .ok a.2.body := by
  obtain ⟨p, d', hp, hd, hs, _, haux⟩ := writeAnnots_aux h
  refine ⟨p, d', hp, hd, hs, fun a ha => ?_⟩
  rw [haux a ha, hplain, auxBody_none]

/-- **The result keeps the original's encryption, general writer** (rules W10, W11). -/
theorem writeUpdate_crypt {limits : Limits} {doc : Doc.Doc} {edits : Edits}
    {sups : List Supersede} {aux : List AuxStream} {out : ByteArray}
    (h : writeUpdate limits doc edits sups aux ivSeed = .ok out) :
    ∃ d', Open.openFile limits out = .ok d' ∧ SameCrypt d'.crypt doc.file.crypt := by
  obtain ⟨p, d', hp, hd, _, _, _, hcr⟩ := writeUpdate_open h
  exact ⟨d', hd, (planUpdate_ok hp).2.1 ▸ hcr⟩

/-- **The result has exactly the original's decryption state, general writer** (rules W10,
W11, task 9.5e2): the strict re-open of every successful `writeUpdate` has a decryption state
equal (every field: handler incl. `/EncryptMetadata` and crypt filters, file key,
`/Encrypt` object, `/Perms` result) to the original's — whether `/Encrypt` is direct in the
trailer or indirect, superseded or not. -/
theorem writeUpdate_crypt_eq {limits : Limits} {doc : Doc.Doc} {edits : Edits}
    {sups : List Supersede} {aux : List AuxStream} {out : ByteArray}
    (h : writeUpdate limits doc edits sups aux ivSeed = .ok out) :
    ∃ d', Open.openFile limits out = .ok d' ∧ d'.crypt = doc.file.crypt := by
  obtain ⟨p, hp, _, _, hc⟩ := writeUpdate_ok h
  obtain ⟨d', hd, hcr⟩ := checkObjects_crypt hc
  exact ⟨d', hd, hcr.trans (planUpdate_ok hp).2.1⟩

/-- **The result has exactly the original's decryption state** (task 9.5e2) for
`writeAnnots`: see `writeUpdate_crypt_eq`. -/
theorem writeAnnots_crypt_eq {limits : Limits} {doc : Doc.Doc} {marks : Marks}
    {aux : List AuxStream} {out : ByteArray} (h : writeAnnots limits doc marks aux ivSeed = .ok out) :
    ∃ d', Open.openFile limits out = .ok d' ∧ d'.crypt = doc.file.crypt :=
  writeUpdate_crypt_eq h

/-- **The result keeps the original's encryption** (rule W10, task 9.5f): it re-opens with a
decryption state exactly when the original has one, with the same file key, string and
stream methods and encryption-dictionary object — the new objects are encrypted for the
same readers as the old ones, never written in the clear into an encrypted file without
the reader noticing (the self-check decrypts them back, `writeAnnots_open`). -/
theorem writeAnnots_crypt {limits : Limits} {doc : Doc.Doc} {marks : Marks}
    {aux : List AuxStream} {out : ByteArray} (h : writeAnnots limits doc marks aux ivSeed = .ok out) :
    ∃ d', Open.openFile limits out = .ok d' ∧ SameCrypt d'.crypt doc.file.crypt :=
  writeUpdate_crypt h

/-! ## Untouched objects keep their value (task 9.5e) -/

/-- `numberAux n` numbers from `n` on. -/
theorem numberAux_ge {n : Nat} {as : List AuxStream} {a : Nat × AuxStream}
    (h : a ∈ numberAux n as) : n ≤ a.1 := by
  induction as generalizing n with
  | nil => simp [numberAux] at h
  | cons x xs ih =>
    simp only [numberAux, List.mem_cons] at h
    rcases h with rfl | h
    · exact Nat.le_refl _
    · have := ih h
      omega

/-- **What the update writes over**: every number of the update's section is either new (at
or above the original `/Size`: an added annotation, an auxiliary stream, the xref stream) or
an original object that fetches as a dictionary (a rewritten page or a superseded object,
rule W11). -/
theorem keys_cases {limits : Limits} {doc : Doc.Doc} {edits : Edits} {sups : List Supersede}
    {aux : List AuxStream} {p : Plan} (hp : planUpdate limits doc edits sups aux ivSeed = .ok p)
    {m : Nat} (hm : m ∈ p.keys) :
    doc.file.trailer.size ≤ m ∨
      ∃ gk dd, doc.file.getObject limits m gk = .ok (.obj (.dict dd)) := by
  obtain ⟨_, _, hsize, _, haux, hsups, _, hsok⟩ := planUpdate_ok hp
  unfold Plan.keys at hm
  rw [List.mem_mergeSort] at hm
  simp only [List.mem_append, List.mem_map] at hm
  rcases hm with (⟨o, ho, rfl⟩ | ⟨a, ha, rfl⟩) | hx
  · unfold Plan.objects at ho
    rcases List.mem_append.mp ho with ho | ho
    · obtain ⟨pp, hpp, ho⟩ := List.mem_flatMap.mp ho
      have hok := (planUpdate_page hp hpp).1
      unfold PagePlan.objects at ho
      rcases List.mem_append.mp ho with ho | ho
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ho
        exact Or.inl (hok.fresh a ha)
      · rw [List.mem_singleton] at ho
        subst ho
        exact Or.inr ⟨pp.gen, pp.dict, hok.dict⟩
    · unfold supObjects at ho
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ho
      rw [hsups] at hs
      obtain ⟨-, -, od, hod⟩ := supOk_ok (hsok s hs)
      exact Or.inr ⟨s.2.1, od, hod⟩
  · rw [haux] at ha
    have := numberAux_ge ha
    exact Or.inl (by omega)
  · left
    split at hx
    · rw [List.mem_singleton] at hx
      subst hx
      unfold Plan.xrefNum
      omega
    · cases hx

/-- The numbers the update writes over cannot take part in a `/Length` resolution of the
original (`WritePrefix.NotLen`): new numbers have no entry, rewritten pages and superseded
objects are dictionaries. -/
theorem keys_notLen {limits : Limits} {doc : Doc.Doc} {edits : Edits} {sups : List Supersede}
    {aux : List AuxStream} {p : Plan} (hp : planUpdate limits doc edits sups aux ivSeed = .ok p)
    (hd0 : Open.openFile limits doc.file.bytes = .ok doc.file) {m : Nat} (hm : m ∈ p.keys) :
    WritePrefix.NotLen doc.file.pre doc.file.lookup limits doc.file.bytes m := by
  rcases keys_cases hp hm with hge | ⟨gk, dd, hg⟩
  · apply WritePrefix.notLen_of_none
    rcases hl : doc.file.lookup m with _ | e
    · rfl
    · exfalso
      rw [WritePrefix.lookup_eq] at hl
      have hmem := (Unambiguous.lookupEntry_eq_some_iff doc.file.xref.keys_nodup).mp hl
      have := Unambiguous.openFile_lt_size hd0 (planUpdate_ok hp).1 _ hmem
      simp only at this
      omega
  · exact WritePrefix.notLen_of_dict hg

/-- The original's decryption state is kept by the update in the case task 9.5e proved
(rule W10): the document is unencrypted, or its encryption dictionary is an indirect object
that the update does not write. Task 9.5e2 made it unnecessary (`c7Value'`: the writer's
self-check compares the whole state, `sameState`); kept for the 9.5e statements. -/
def EncKept (doc : Doc.Doc) (p : Plan) : Prop :=
  ∀ st, doc.file.crypt = some st → ∃ r, st.encRef = some r ∧ r.1 ∉ p.keys

/-- An unencrypted document satisfies `EncKept`. -/
theorem encKept_plain {doc : Doc.Doc} (p : Plan) (h : doc.file.crypt = none) : EncKept doc p := by
  intro st hst
  rw [h] at hst
  cases hst

/-- **C7 (3), value level, general writer, no side condition** (tasks 9.5e, 9.5e2; rules
G1–G5, W10, W11). For a successful `writeUpdate` of a document opened from its bytes — plain,
or encrypted with a direct or an indirect `/Encrypt` — the result opens with exactly the
original's decryption state (`writeUpdate_crypt_eq`, from the self-check's `sameState`), and
every object number the update does not write **fetches the same value**: every successful
`getObject` of the original (any generation; `null` for undefined objects included) gives the
same body on the result, `/Length` resolution, object streams and decryption included. -/
theorem writeUpdate_value' {limits : Limits} {doc : Doc.Doc} {edits : Edits}
    {sups : List Supersede} {aux : List AuxStream} {out : ByteArray}
    (h : writeUpdate limits doc edits sups aux ivSeed = .ok out)
    (hd0 : Open.openFile limits doc.file.bytes = .ok doc.file) {p : Plan}
    (hp : planUpdate limits doc edits sups aux ivSeed = .ok p) :
    ∃ d', Open.openFile limits out = .ok d' ∧ d'.crypt = doc.file.crypt ∧
      ∀ n, n ∉ p.keys → ∀ g v, doc.file.getObject limits n g = .ok v →
        d'.getObject limits n g = .ok v := by
  obtain ⟨p1, revs, sec', tr', off', hp1, hold, hnew, _, _, hstart, hkeys⟩ := writeUpdate_chain h
  rw [hp] at hp1
  cases hp1
  obtain ⟨p2, d', hp2, hd', hr', _, _, _⟩ := writeUpdate_open h
  rw [hp] at hp2
  cases hp2
  obtain ⟨d'', hd'', hc⟩ := writeUpdate_crypt_eq h
  rw [hd'] at hd''
  cases hd''
  obtain ⟨hrep, -, -⟩ := planUpdate_ok hp
  have hE := writeUpdate_extends h
  have hs : WritePrefix.HasEnd doc.file.bytes := ⟨_, hstart⟩
  -- the two documents
  obtain ⟨revs0, sec0, tr0, o0, rest0, hl0, hrv0, hw0⟩ := WritePrefix.openFile_shape hd0 hrep
  rw [hold] at hl0
  cases hl0
  obtain ⟨revs1, sec1, tr1, o1, rest1, hl1, hrv1, hw1⟩ := WritePrefix.openFile_shape hd' hr'
  rw [hnew] at hl1
  cases hl1
  obtain ⟨hb0, hx0, -⟩ := WritePrefix.withCrypt_mk' hw0
  obtain ⟨hb1, hx1, -⟩ := WritePrefix.withCrypt_mk' hw1
  -- lookups agree outside the keys
  have hL : ∀ m, m ∉ p.keys → d'.lookup m = doc.file.lookup m := by
    intro m hm
    rw [WritePrefix.lookup_eq, WritePrefix.lookup_eq, hx0, hx1]
    apply WritePrefix.mergeChain_cons_lookup_none
    simp only
    rw [hkeys]
    exact hm
  have hfuel : doc.file.objectCount ≤ d'.objectCount := by
    rw [WritePrefix.objectCount_eq, WritePrefix.objectCount_eq, hx0, hx1]
    exact WritePrefix.mergeChain_cons_length _ _
  refine ⟨d', hd', hc, fun n hn g v hv => ?_⟩
  have hE' : PrefixStable.Extends doc.file.bytes d'.bytes := by rw [hb1]; exact hE
  exact WritePrefix.getObject_transfer hE' hs hL (fun m hm => keys_notLen hp hd0 hm) hfuel hc hn hv

/-- **C7 (3), value level, general writer** (task 9.5e; rules G1–G5, W10, W11). For a
successful `writeUpdate` of a document opened from its bytes, if the encryption dictionary
(if any) is indirect and not written over (`EncKept`; always true for unencrypted
documents): the result opens with exactly the original's decryption state, and every object
number the update does not write **fetches the same value** — every successful
`getObject` of the original (any generation; `null` for undefined objects included) gives the
same body on the result, `/Length` resolution, object streams and decryption included.
Since task 9.5e2 a corollary of `writeUpdate_value'`, which needs no `EncKept`. -/
theorem writeUpdate_value {limits : Limits} {doc : Doc.Doc} {edits : Edits}
    {sups : List Supersede} {aux : List AuxStream} {out : ByteArray}
    (h : writeUpdate limits doc edits sups aux ivSeed = .ok out)
    (hd0 : Open.openFile limits doc.file.bytes = .ok doc.file) {p : Plan}
    (hp : planUpdate limits doc edits sups aux ivSeed = .ok p) (_henc : EncKept doc p) :
    ∃ d', Open.openFile limits out = .ok d' ∧ d'.crypt = doc.file.crypt ∧
      ∀ n, n ∉ p.keys → ∀ g v, doc.file.getObject limits n g = .ok v →
        d'.getObject limits n g = .ok v :=
  writeUpdate_value' h hd0 hp

/-- **C7 (3), value level** (task 9.5e) for `writeAnnots`: see `writeUpdate_value`. -/
theorem writeAnnots_value {limits : Limits} {doc : Doc.Doc} {marks : Marks} {aux : List AuxStream}
    {out : ByteArray} (h : writeAnnots limits doc marks aux ivSeed = .ok out)
    (hd0 : Open.openFile limits doc.file.bytes = .ok doc.file) {p : Plan}
    (hp : plan limits doc marks aux ivSeed = .ok p) (henc : EncKept doc p) :
    ∃ d', Open.openFile limits out = .ok d' ∧ d'.crypt = doc.file.crypt ∧
      ∀ n, n ∉ p.keys → ∀ g v, doc.file.getObject limits n g = .ok v →
        d'.getObject limits n g = .ok v :=
  writeUpdate_value h hd0 hp henc

/-- **C7 (3), value level, no side condition** (tasks 9.5e, 9.5e2) for `writeAnnots`: see
`writeUpdate_value'`. -/
theorem writeAnnots_value' {limits : Limits} {doc : Doc.Doc} {marks : Marks}
    {aux : List AuxStream} {out : ByteArray} (h : writeAnnots limits doc marks aux ivSeed = .ok out)
    (hd0 : Open.openFile limits doc.file.bytes = .ok doc.file) {p : Plan}
    (hp : plan limits doc marks aux ivSeed = .ok p) :
    ∃ d', Open.openFile limits out = .ok d' ∧ d'.crypt = doc.file.crypt ∧
      ∀ n, n ∉ p.keys → ∀ g v, doc.file.getObject limits n g = .ok v →
        d'.getObject limits n g = .ok v :=
  writeUpdate_value' h hd0 hp

/-! ## C7 -/

/-- **C7 (Plan.md §4): the incremental update is conservative.** For every successful
`writeAnnots limits doc marks aux ivSeed = .ok out`:

* the original bytes are a prefix of `out` (S8);
* `out`'s chain is the original chain with one new section (`/Prev` = old `startxref`)
  whose object numbers are exactly the plan's keys, and every other object number resolves
  to the same cross-reference entry as in the original;
* `out` opens strictly, and for each page of `marks` its annotation list is the original
  list followed by fresh references that fetch exactly the given annotation dictionaries.

(The object-value form of "every other object unchanged" is `c7ValueAnnots`,
`writeAnnots_value`.) -/
theorem c7 {limits : Limits} {doc : Doc.Doc} {marks : Marks} {aux : List AuxStream}
    {out : ByteArray}
    (h : writeAnnots limits doc marks aux ivSeed = .ok out) :
    (∃ u, out = doc.file.bytes ++ u) ∧
    ∃ p revs sec' tr' off' d',
      plan limits doc marks aux ivSeed = .ok p ∧
      loadChain limits out = .ok ((sec', tr', off') :: revs) ∧
      loadChain limits doc.file.bytes = .ok revs ∧
      tr'.prev? = some p.start ∧ Xref.findStartxref doc.file.bytes = .ok p.start ∧
      sec'.entries.map Prod.fst = p.keys ∧
      (∀ n, n ∉ p.keys → resolveEntry limits out n = resolveEntry limits doc.file.bytes n) ∧
      Open.openFile limits out = .ok d' ∧ d'.repaired = false ∧
      p.pages.map (fun pp => (pp.index, pp.annots.map Prod.snd)) = marks ∧
      ∀ pp ∈ p.pages,
        annotsOf doc.file limits pp.num pp.gen = .ok pp.old ∧
        annotsOf d' limits pp.num pp.gen = .ok (pp.old ++ pp.refs) ∧
        ∀ a ∈ pp.annots, d'.getObject limits a.1 0 = .ok (.obj (.dict a.2)) ∧
          doc.file.trailer.size ≤ a.1 := by
  refine ⟨writeAnnots_prefix h, ?_⟩
  obtain ⟨p, revs, sec', tr', off', hp, hold, hnew, _, hprev, hstart, hkeys⟩ :=
    writeAnnots_chain h
  obtain ⟨p', d', hp', hd, hr, hm, hall⟩ := writeAnnots_annots h
  rw [hp] at hp'
  cases hp'
  exact ⟨p, revs, sec', tr', off', d', hp, hnew, hold, hprev, hstart, hkeys,
    fun n hn => writeAnnots_untouched h hp hn, hd, hr, hm,
    fun pp hpp => ⟨(hall pp hpp).1, (hall pp hpp).2.1, (hall pp hpp).2.2.2.1⟩⟩

/-- **C7 for the generalized update** (Plan.md §4 C7, rule W11, task 9.5g). For every
successful `writeUpdate limits doc edits sups aux ivSeed = .ok out`:

* the original bytes are a prefix of `out` (S8);
* `out`'s chain is the original chain with one new section (`/Prev` = old `startxref`)
  whose object numbers are exactly the plan's keys, and every other object number resolves
  to the same cross-reference entry as in the original (untouched numbers keep their xref
  entries);
* `out` opens strictly; the plan covers exactly `edits`; for each edited page its
  annotation list on `out` is the original list without the removed references (which were
  on it), the other references unchanged in order (superseded ones included, `mem_kept`),
  followed by fresh references that fetch exactly the added dictionaries;
* every superseded object existed as a dictionary under its number and generation, and
  `out` fetches exactly its new dictionary there. -/
theorem c7Update {limits : Limits} {doc : Doc.Doc} {edits : Edits} {sups : List Supersede}
    {aux : List AuxStream} {out : ByteArray}
    (h : writeUpdate limits doc edits sups aux ivSeed = .ok out) :
    (∃ u, out = doc.file.bytes ++ u) ∧
    ∃ p revs sec' tr' off' d',
      planUpdate limits doc edits sups aux ivSeed = .ok p ∧
      loadChain limits out = .ok ((sec', tr', off') :: revs) ∧
      loadChain limits doc.file.bytes = .ok revs ∧
      tr'.prev? = some p.start ∧ Xref.findStartxref doc.file.bytes = .ok p.start ∧
      sec'.entries.map Prod.fst = p.keys ∧
      (∀ n, n ∉ p.keys → resolveEntry limits out n = resolveEntry limits doc.file.bytes n) ∧
      Open.openFile limits out = .ok d' ∧ d'.repaired = false ∧
      p.pages.map (fun pp => (pp.index, pp.removed, pp.annots.map Prod.snd)) =
        edits.map (fun e => (e.index, refObjs e.remove, e.add)) ∧
      (∀ pp ∈ p.pages,
        annotsOf doc.file limits pp.num pp.gen = .ok pp.old ∧
        (∀ r ∈ pp.removed, r ∈ pp.old) ∧
        annotsOf d' limits pp.num pp.gen =
          .ok (pp.old.filter (fun o => decide (o ∉ pp.removed)) ++ pp.refs) ∧
        ∀ a ∈ pp.annots, d'.getObject limits a.1 0 = .ok (.obj (.dict a.2)) ∧
          doc.file.trailer.size ≤ a.1) ∧
      ∀ s ∈ sups,
        (∃ od, doc.file.getObject limits s.1 s.2.1 = .ok (.obj (.dict od))) ∧
        d'.getObject limits s.1 s.2.1 = .ok (.obj (.dict s.2.2)) := by
  refine ⟨writeUpdate_prefix h, ?_⟩
  obtain ⟨p, revs, sec', tr', off', hp, hold, hnew, _, hprev, hstart, hkeys⟩ :=
    writeUpdate_chain h
  obtain ⟨p', d', hp', hd, hr, hm, hall⟩ := writeUpdate_annots h
  obtain ⟨p'', d'', hp'', hd', _, _, hsups⟩ := writeUpdate_sups h
  rw [hp] at hp' hp''
  cases hp'
  cases hp''
  rw [hd] at hd'
  cases hd'
  exact ⟨p, revs, sec', tr', off', d', hp, hnew, hold, hprev, hstart, hkeys,
    fun n hn => writeUpdate_untouched h hp hn, hd, hr, hm,
    fun pp hpp => ⟨(hall pp hpp).1, (hall pp hpp).2.1, (hall pp hpp).2.2.1,
      (hall pp hpp).2.2.2.2.1⟩,
    fun s hs => ⟨(hsups s hs).2.2.1, (hsups s hs).2.2.2⟩⟩

/-- A document opened by `Doc.openDoc` strictly (the writer refuses repaired documents) is
the strict open of its own bytes: the hypothesis `hd0` of `writeUpdate_value`. -/
theorem openFile_self {limits : Limits} {bytes : ByteArray} {doc : Doc.Doc}
    (h : Doc.openDoc limits bytes = .ok doc) (hr : doc.file.repaired = false) :
    Open.openFile limits doc.file.bytes = .ok doc.file := by
  have h1 := (Spec.PageTree.openDoc_ok h).1
  obtain ⟨_, _, _, _, _, _, _, hw⟩ := WritePrefix.openFile_shape h1 hr
  rw [(WritePrefix.withCrypt_mk' hw).1]
  exact h1

/-- **C7 at the value level, general writer, no side condition** (tasks 9.5e, 9.5e2;
alongside `c7Update`, whose statement is unchanged). For every successful
`writeUpdate limits doc edits sups aux ivSeed = .ok out` of a document opened from its bytes
(`openFile_self` for `Doc.openDoc`) — unencrypted, or encrypted with a direct trailer
`/Encrypt` dictionary or an indirect one (superseded or not) — the plan `p` and the strictly
opened result `d'` are those of `c7Update`, the result has exactly the original's decryption
state, and every object number not in `p.keys` fetches exactly as in the original (every
successful `getObject`, any generation). -/
theorem c7Value' {limits : Limits} {doc : Doc.Doc} {edits : Edits} {sups : List Supersede}
    {aux : List AuxStream} {out : ByteArray}
    (h : writeUpdate limits doc edits sups aux ivSeed = .ok out)
    (hd0 : Open.openFile limits doc.file.bytes = .ok doc.file) :
    ∃ p d', planUpdate limits doc edits sups aux ivSeed = .ok p ∧ Open.openFile limits out = .ok d' ∧
      d'.crypt = doc.file.crypt ∧
      ∀ n, n ∉ p.keys → ∀ g v, doc.file.getObject limits n g = .ok v →
        d'.getObject limits n g = .ok v := by
  obtain ⟨p, hp, -⟩ := writeUpdate_ok h
  obtain ⟨d', hd, hc, hv⟩ := writeUpdate_value' h hd0 hp
  exact ⟨p, d', hp, hd, hc, hv⟩

/-- **C7 at the value level, general writer** (task 9.5e; alongside `c7Update`, whose
statement is unchanged). For every successful `writeUpdate limits doc edits sups aux ivSeed = .ok out`
of a document opened from its bytes (`openFile_self` for `Doc.openDoc`): the plan `p` and the
strictly opened result `d'` are those of `c7Update`, and if the encryption dictionary is kept
(`EncKept`: unencrypted, or `/Encrypt` an indirect object not in `p.keys`) the result has the
original's decryption state and every object number not in `p.keys` fetches exactly as in
the original (every successful `getObject`, any generation). Since task 9.5e2 a corollary
of `c7Value'`, which drops the `EncKept` condition. -/
theorem c7Value {limits : Limits} {doc : Doc.Doc} {edits : Edits} {sups : List Supersede}
    {aux : List AuxStream} {out : ByteArray}
    (h : writeUpdate limits doc edits sups aux ivSeed = .ok out)
    (hd0 : Open.openFile limits doc.file.bytes = .ok doc.file) :
    ∃ p d', planUpdate limits doc edits sups aux ivSeed = .ok p ∧ Open.openFile limits out = .ok d' ∧
      (EncKept doc p → d'.crypt = doc.file.crypt ∧
        ∀ n, n ∉ p.keys → ∀ g v, doc.file.getObject limits n g = .ok v →
          d'.getObject limits n g = .ok v) := by
  obtain ⟨p, d', hp, hd, hc, hv⟩ := c7Value' h hd0
  exact ⟨p, d', hp, hd, fun _ => ⟨hc, hv⟩⟩

/-- **C7 at the value level for unencrypted documents** (task 9.5e): no side condition. -/
theorem c7Value_plain {limits : Limits} {doc : Doc.Doc} {edits : Edits} {sups : List Supersede}
    {aux : List AuxStream} {out : ByteArray}
    (h : writeUpdate limits doc edits sups aux ivSeed = .ok out)
    (hd0 : Open.openFile limits doc.file.bytes = .ok doc.file) (hplain : doc.file.crypt = none) :
    ∃ p d', planUpdate limits doc edits sups aux ivSeed = .ok p ∧ Open.openFile limits out = .ok d' ∧
      ∀ n, n ∉ p.keys → ∀ g v, doc.file.getObject limits n g = .ok v →
        d'.getObject limits n g = .ok v := by
  obtain ⟨p, d', hp, hd, hv⟩ := c7Value h hd0
  exact ⟨p, d', hp, hd, (hv (encKept_plain p hplain)).2⟩

/-- **C7 at the value level for `writeAnnots`** (task 9.5e; alongside `c7`). -/
theorem c7ValueAnnots {limits : Limits} {doc : Doc.Doc} {marks : Marks} {aux : List AuxStream}
    {out : ByteArray} (h : writeAnnots limits doc marks aux ivSeed = .ok out)
    (hd0 : Open.openFile limits doc.file.bytes = .ok doc.file) :
    ∃ p d', plan limits doc marks aux ivSeed = .ok p ∧ Open.openFile limits out = .ok d' ∧
      (EncKept doc p → d'.crypt = doc.file.crypt ∧
        ∀ n, n ∉ p.keys → ∀ g v, doc.file.getObject limits n g = .ok v →
          d'.getObject limits n g = .ok v) :=
  c7Value h hd0

/-- **C7 at the value level for `writeAnnots`, no side condition** (tasks 9.5e, 9.5e2;
alongside `c7`): see `c7Value'`. -/
theorem c7ValueAnnots' {limits : Limits} {doc : Doc.Doc} {marks : Marks} {aux : List AuxStream}
    {out : ByteArray} (h : writeAnnots limits doc marks aux ivSeed = .ok out)
    (hd0 : Open.openFile limits doc.file.bytes = .ok doc.file) :
    ∃ p d', plan limits doc marks aux ivSeed = .ok p ∧ Open.openFile limits out = .ok d' ∧
      d'.crypt = doc.file.crypt ∧
      ∀ n, n ∉ p.keys → ∀ g v, doc.file.getObject limits n g = .ok v →
        d'.getObject limits n g = .ok v :=
  c7Value' h hd0

end SafePdf.Spec.Write
