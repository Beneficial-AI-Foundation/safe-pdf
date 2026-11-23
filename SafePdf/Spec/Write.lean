import SafePdf.Core.Write.Incremental
import SafePdf.Spec.Unambiguous
import SafePdf.Spec.RoundTripCore

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
   encryption itself (`Core.Write.Encrypt`, RC4 / AES-CBC with a deterministic IV) is the
   inverse of `Crypt.decryptBody` is not proved — the primitives are vector-tested, not
   verified (Plan.md §6 Phase 4) — it is *checked* on every write by the self-check, and
   tested on the encrypted fixtures and corpus files.
6. `serialize_roundtrip`: the serializer is the Phase 1 printer, whose round trip
   `parseObject (serialize o) = o` is M1's `Spec.RoundTripCore.parseObject_print`.

`c7` bundles 1–5.

## What is proved by construction, what by the writer's self-check

Facts 2, 4 and the "after" half of 5 rest on the writer's own strict re-parse (rule W8:
`checkChain`, `checkObjects`): `writeAnnots` returns bytes only when they hold, and the
theorems turn those Boolean checks into statements about the parser — via
`Spec.Unambiguous.resolveEntry_append` (prefix stability of the old sections, task 2.12) for
3. The writer is therefore *sound* by proof; that it *succeeds* on well-formed inputs
(completeness: the serializer's section and objects always parse) is tested, not proved
(`Tests/WriteIncremental.lean`, fixtures and corpus).

**Not proved here (recorded obstacle, split in the ledger):** fact 3 is stated at the level
of cross-reference entries. Lifting it to `OpenDoc.getObject` ("the object *value* is
unchanged") needs prefix stability of object resolution itself — `Length.parseIndirectResolved`
(an indirect `/Length` looked up through the *new* section, with fuel = the new object
count), `ObjStm.fetchCompressed` (container decode on extended bytes) and decryption — none of
which has `_ext` lemmas yet (`Spec.PrefixStable` covers the lexer, the object parser, xref
tables and xref streams). The object-level property is checked by the test suite on every
original object of every fixture and of the corpus sample.
-/

namespace SafePdf.Spec.Write

open SafePdf SafePdf.Core
open SafePdf.Core.Write.Incremental
open SafePdf.Core.Xref (XrefEntry XrefSection Trailer)
open SafePdf.Core.Xref.Chain (Revision loadChain lookupEntry)
open SafePdf.Spec.Unambiguous (resolveEntry)

/-! ## The serializer round trip -/

/-- **Serializer round trip** (M1 reused): the strict object parser reads the serialized
bytes of a canonical object with in-range references back to the same object. -/
theorem serialize_roundtrip (limits : Limits) (o : PdfObject) (hc : o.Canonical)
    (hr : Print.RefsInRange o) (hd : o.depth ≤ limits.maxObjectDepth) :
    ∃ r, ObjParse.parseObject limits ⟨(Write.Serialize.serialize o).toArray⟩ 0 = .ok (o, r) :=
  Spec.RoundTripCore.parseObject_print limits o hc hr hd

/-! ## Unfolding the writer -/

/-- A successful write comes from a plan whose result passed both self-checks. -/
theorem writeAnnots_ok {limits : Limits} {doc : Doc.Doc} {marks : Marks} {aux : List AuxStream}
    {out : ByteArray}
    (h : writeAnnots limits doc marks aux = .ok out) :
    ∃ p, plan limits doc marks aux = .ok p ∧ out = result doc.file.bytes p ∧
      checkChain limits doc.file.bytes out p.start p.keys = true ∧
      checkObjects limits out p.objects p.auxExpected p.crypt = true := by
  unfold writeAnnots at h
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

/-- **C7 (1), prefix.** The original bytes are a prefix of the result (S8). -/
theorem writeAnnots_prefix {limits : Limits} {doc : Doc.Doc} {marks : Marks} {aux : List AuxStream}
    {out : ByteArray}
    (h : writeAnnots limits doc marks aux = .ok out) : ∃ u, out = doc.file.bytes ++ u := by
  obtain ⟨p, _, rfl, _, _⟩ := writeAnnots_ok h
  exact ⟨_, rfl⟩

/-- The result extends the original (`PrefixStable.Extends`). -/
theorem writeAnnots_extends {limits : Limits} {doc : Doc.Doc} {marks : Marks} {aux : List AuxStream}
    {out : ByteArray}
    (h : writeAnnots limits doc marks aux = .ok out) : PrefixStable.Extends doc.file.bytes out := by
  obtain ⟨u, rfl⟩ := writeAnnots_prefix h
  exact PrefixStable.Extends.append _ _

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

/-- **C7 (2), revision structure.** The result's chain is the original chain with one new
section in front: its `/Prev` is the original `startxref`, its object numbers are exactly
the plan's keys. -/
theorem writeAnnots_chain {limits : Limits} {doc : Doc.Doc} {marks : Marks} {aux : List AuxStream}
    {out : ByteArray}
    (h : writeAnnots limits doc marks aux = .ok out) :
    ∃ p revs sec' tr' off', plan limits doc marks aux = .ok p ∧
      loadChain limits doc.file.bytes = .ok revs ∧
      loadChain limits out = .ok ((sec', tr', off') :: revs) ∧
      doc.file.bytes.size ≤ off' ∧ tr'.prev? = some p.start ∧
      Xref.findStartxref doc.file.bytes = .ok p.start ∧
      sec'.entries.map Prod.fst = p.keys := by
  obtain ⟨p, hp, hout, hc, _⟩ := writeAnnots_ok h
  obtain ⟨revs, off', sec', tr', h1, h2, h3, hsz, hrev, hsec, hhyb, hprev, hkeys⟩ :=
    checkChain_ok hc
  have hext := writeAnnots_extends h
  refine ⟨p, revs, sec', tr', off', hp, h2, ?_, hsz, hprev, h1, hkeys⟩
  exact Spec.Unambiguous.loadChain_append h2 h1 hext h3 hsz hsec hhyb hprev hrev

/-- **C7 (3), untouched objects.** An object number that the update does not write resolves
to the same cross-reference entry in the result as in the original. -/
theorem writeAnnots_untouched {limits : Limits} {doc : Doc.Doc} {marks : Marks}
    {aux : List AuxStream}
    {out : ByteArray} {p : Plan} (h : writeAnnots limits doc marks aux = .ok out)
    (hp : plan limits doc marks aux = .ok p) {n : Nat} (hn : n ∉ p.keys) :
    resolveEntry limits out n = resolveEntry limits doc.file.bytes n := by
  obtain ⟨p', revs, sec', tr', off', hp', h2, hnew, _, _, _, hkeys⟩ := writeAnnots_chain h
  rw [hp] at hp'
  cases hp'
  rw [Spec.Unambiguous.resolveEntry_of_cons hnew h2 n]
  have hnone : lookupEntry n sec'.entries = none := by
    rw [Spec.Unambiguous.lookupEntry_eq_none_iff, hkeys]
    exact hn
  rw [hnone]
  cases resolveEntry limits doc.file.bytes n <;> rfl

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
    exact ⟨d', hd, h.1.1.1, fun o ho => bodyIs_eq (h.1.1.2 o ho),
      fun a ha => auxIs_eq (h.1.2 a ha), sameCrypt_ok h.2⟩
  · cases h

/-- **C7 (4), strict re-open.** The result opens strictly and every written object fetches
exactly as planned — for an encrypted document, after decryption by the reader (rule W10);
the result's decryption state agrees with the plan's (the original's, `plan_ok`). -/
theorem writeAnnots_open {limits : Limits} {doc : Doc.Doc} {marks : Marks} {aux : List AuxStream}
    {out : ByteArray}
    (h : writeAnnots limits doc marks aux = .ok out) :
    ∃ p d', plan limits doc marks aux = .ok p ∧ Open.openFile limits out = .ok d' ∧
      d'.repaired = false ∧
      (∀ o ∈ p.objects, d'.getObject limits o.1 o.2.1 = .ok (.obj o.2.2)) ∧
      (∀ a ∈ p.aux, d'.getObject limits a.1 0 = .ok (auxBody p.crypt a.2)) ∧
      SameCrypt d'.crypt p.crypt := by
  obtain ⟨p, hp, _, _, hc⟩ := writeAnnots_ok h
  obtain ⟨d', hd, hr, hobj, haux, hcr⟩ := checkObjects_ok hc
  refine ⟨p, d', hp, hd, hr, hobj, fun a ha => ?_, hcr⟩
  exact haux (a.1, auxBody p.crypt a.2) (List.mem_map.mpr ⟨a, ha, rfl⟩)

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

/-- One planned page. -/
theorem planPage_ok {limits : Limits} {doc : Doc.Doc} {next : Nat} {pm : Nat × List Dict}
    {pp : PagePlan} (h : planPage limits doc next pm = .ok pp) :
    PageOk limits doc next pp ∧ pp.index = pm.1 ∧ pp.annots = numberFrom next pm.2 := by
  unfold planPage at h
  split at h
  · cases h
  · rename_i pg hpg
    split at h
    · split at h
      · rename_i pd hpd
        split at h
        · rename_i old hold
          cases h
          exact ⟨⟨⟨pg, hpg, rfl, rfl⟩, hpd, hold, fun a ha => numberFrom_ge ha⟩, rfl, rfl⟩
        · cases h
      · cases h
      · cases h
    · cases h

/-- All planned pages: they cover exactly `marks`, and each is a `PageOk` with annotation
numbers at or above `next`. -/
theorem planPages_ok {limits : Limits} {doc : Doc.Doc} :
    ∀ {next : Nat} {marks : Marks} {pps : List PagePlan},
      planPages limits doc next marks = .ok pps →
      pps.map (fun pp => (pp.index, pp.annots.map Prod.snd)) = marks ∧
        ∀ pp ∈ pps, PageOk limits doc next pp
  | next, [], pps, h => by
    simp only [planPages, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, fun _ h => by cases h⟩
  | next, pm :: rest, pps, h => by
    simp only [planPages] at h
    split at h
    · cases h
    · rename_i pp hpp
      split at h
      · cases h
      · rename_i pps' hpps
        cases h
        obtain ⟨hok, hidx, hann⟩ := planPage_ok hpp
        obtain ⟨hm, hall⟩ := planPages_ok hpps
        refine ⟨?_, ?_⟩
        · simp only [List.map_cons, hm, hidx, hann, numberFrom_snd]
        · intro q hq
          rcases List.mem_cons.mp hq with rfl | hq
          · exact hok
          · have hq' := hall q hq
            exact ⟨hq'.page, hq'.dict, hq'.old, fun a ha => by
              have := hq'.fresh a ha
              omega⟩

/-- What a successful plan says about its input (rules W1–W3, W9, W10). -/
theorem plan_ok {limits : Limits} {doc : Doc.Doc} {marks : Marks} {aux : List AuxStream}
    {p : Plan}
    (h : plan limits doc marks aux = .ok p) :
    doc.file.repaired = false ∧ p.crypt = doc.file.crypt ∧
      p.size = doc.file.trailer.size ∧
      planPages limits doc doc.file.trailer.size marks = .ok p.pages ∧
      p.aux = numberAux (doc.file.trailer.size + (p.pages.map fun pp => pp.annots.length).sum)
        aux := by
  unfold plan at h
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
          · split at h
            · cases h
            · rename_i pps hpps
              split at h
              · cases h
              · split at h
                · cases h
                  simp only [Bool.not_eq_true] at hrep
                  exact ⟨hrep, rfl, rfl, hpps, rfl⟩
                · cases h
                · cases h

/-- **The plan covers exactly `marks`**: page indices and annotation dictionaries, in order. -/
theorem plan_marks {limits : Limits} {doc : Doc.Doc} {marks : Marks} {aux : List AuxStream}
    {p : Plan}
    (h : plan limits doc marks aux = .ok p) :
    p.pages.map (fun pp => (pp.index, pp.annots.map Prod.snd)) = marks :=
  (planPages_ok (plan_ok h).2.2.2.1).1

/-- **Each planned page is the page at its index**, read from the original document; the
new annotation numbers are fresh (at or above the original `/Size`). -/
theorem plan_page {limits : Limits} {doc : Doc.Doc} {marks : Marks} {aux : List AuxStream}
    {p : Plan}
    (h : plan limits doc marks aux = .ok p) {pp : PagePlan} (hpp : pp ∈ p.pages) :
    PageOk limits doc doc.file.trailer.size pp :=
  (planPages_ok (plan_ok h).2.2.2.1).2 pp hpp

/-! ## Page dictionaries -/

/-- The rewritten page dictionary has the new `/Annots` array. -/
theorem newDict_annots (pp : PagePlan) :
    Dict.get? pp.newDict nameAnnots = some (.array (pp.old ++ pp.refs)) := by
  simp [PagePlan.newDict, Dict.get?, lookup_setKey]

/-- **Every other key of the page dictionary is unchanged.** -/
theorem newDict_lookup_ne (pp : PagePlan) {k : Name} (hk : k ≠ nameAnnots) :
    Dict.lookup pp.newDict k = Dict.lookup pp.dict k :=
  lookup_setKey_ne _ _ hk

/-- The annotation list of the rewritten page dictionary. -/
theorem annotItems_newDict (d : Open.OpenDoc) (limits : Limits) (pp : PagePlan) :
    annotItems d limits pp.newDict = .ok (pp.old ++ pp.refs) := by
  simp [annotItems, newDict_annots]

/-- A page's objects are among the plan's. -/
theorem mem_objects {p : Plan} {pp : PagePlan} (hpp : pp ∈ p.pages) {o : Nat × Nat × PdfObject}
    (ho : o ∈ pp.objects) : o ∈ p.objects :=
  List.mem_flatMap.mpr ⟨pp, hpp, ho⟩

/-- **C7 (5), annotations.** For every page of the plan: the original annotation list is
`pp.old`; on the result it is `pp.old` followed by `pp.refs`; each new reference fetches
exactly its annotation dictionary; the new numbers are fresh. -/
theorem writeAnnots_annots {limits : Limits} {doc : Doc.Doc} {marks : Marks} {aux : List AuxStream}
    {out : ByteArray}
    (h : writeAnnots limits doc marks aux = .ok out) :
    ∃ p d', plan limits doc marks aux = .ok p ∧ Open.openFile limits out = .ok d' ∧
      d'.repaired = false ∧
      p.pages.map (fun pp => (pp.index, pp.annots.map Prod.snd)) = marks ∧
      ∀ pp ∈ p.pages,
        annotsOf doc.file limits pp.num pp.gen = .ok pp.old ∧
        annotsOf d' limits pp.num pp.gen = .ok (pp.old ++ pp.refs) ∧
        pp.refs = pp.annots.map (fun a => .ref a.1 0) ∧
        (∀ a ∈ pp.annots, d'.getObject limits a.1 0 = .ok (.obj (.dict a.2)) ∧
          doc.file.trailer.size ≤ a.1) ∧
        d'.getObject limits pp.num pp.gen = .ok (.obj (.dict pp.newDict)) := by
  obtain ⟨p, d', hp, hd, hr, hobj, _, _⟩ := writeAnnots_open h
  refine ⟨p, d', hp, hd, hr, plan_marks hp, fun pp hpp => ?_⟩
  have hok := plan_page hp hpp
  have hpage : d'.getObject limits pp.num pp.gen = .ok (.obj (.dict pp.newDict)) :=
    hobj (pp.num, pp.gen, .dict pp.newDict) (mem_objects hpp (by simp [PagePlan.objects]))
  refine ⟨?_, ?_, rfl, fun a ha => ⟨?_, hok.fresh a ha⟩, hpage⟩
  · simp only [annotsOf, hok.dict, hok.old]
  · simp only [annotsOf, hpage, annotItems_newDict]
  · exact hobj (a.1, 0, .dict a.2) (mem_objects hpp (by
      simp only [PagePlan.objects, List.mem_append, List.mem_map, List.mem_singleton]
      exact Or.inl ⟨a, ha, rfl⟩))

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

/-- **Auxiliary streams (rules W9, W10).** For a successful write with auxiliary streams
`aux` (task 9.5b: appearance streams), the plan numbers them consecutively from the original
`/Size` plus the number of new annotations, in order, and each fetches from the strictly
re-opened result as exactly that stream with `/Length` set to the length of its written
data (`auxBody`: the data length for an unencrypted document, see `writeAnnots_aux_plain`;
the encrypted length `Encrypt.encLen` for an encrypted one, whose data the reader decrypts
back to exactly the given bytes). -/
theorem writeAnnots_aux {limits : Limits} {doc : Doc.Doc} {marks : Marks} {aux : List AuxStream}
    {out : ByteArray} (h : writeAnnots limits doc marks aux = .ok out) :
    ∃ p d', plan limits doc marks aux = .ok p ∧ Open.openFile limits out = .ok d' ∧
      p.aux.map Prod.snd = aux ∧
      p.aux.map Prod.fst = (List.range aux.length).map
        (doc.file.trailer.size + (p.pages.map fun pp => pp.annots.length).sum + ·) ∧
      ∀ a ∈ p.aux, d'.getObject limits a.1 0 = .ok (auxBody doc.file.crypt a.2) := by
  obtain ⟨p, d', hp, hd, _, _, haux, _⟩ := writeAnnots_open h
  have hn := (plan_ok hp).2.2.2.2
  have hc := (plan_ok hp).2.1
  exact ⟨p, d', hp, hd, by rw [hn, numberAux_snd], by rw [hn, numberAux_fst],
    fun a ha => hc ▸ haux a ha⟩

/-- **Auxiliary streams of an unencrypted document** (rule W9, the 9.5b statement): each
fetches back as exactly `a.body` (`/Length` = its data length). -/
theorem writeAnnots_aux_plain {limits : Limits} {doc : Doc.Doc} {marks : Marks}
    {aux : List AuxStream} {out : ByteArray} (h : writeAnnots limits doc marks aux = .ok out)
    (hplain : doc.file.crypt = none) :
    ∃ p d', plan limits doc marks aux = .ok p ∧ Open.openFile limits out = .ok d' ∧
      p.aux.map Prod.snd = aux ∧
      ∀ a ∈ p.aux, d'.getObject limits a.1 0 = .ok a.2.body := by
  obtain ⟨p, d', hp, hd, hs, _, haux⟩ := writeAnnots_aux h
  refine ⟨p, d', hp, hd, hs, fun a ha => ?_⟩
  rw [haux a ha, hplain, auxBody_none]

/-- **The result keeps the original's encryption** (rule W10, task 9.5f): it re-opens with a
decryption state exactly when the original has one, with the same file key, string and
stream methods and encryption-dictionary object — the new objects are encrypted for the
same readers as the old ones, never written in the clear into an encrypted file without
the reader noticing (the self-check decrypts them back, `writeAnnots_open`). -/
theorem writeAnnots_crypt {limits : Limits} {doc : Doc.Doc} {marks : Marks}
    {aux : List AuxStream} {out : ByteArray} (h : writeAnnots limits doc marks aux = .ok out) :
    ∃ d', Open.openFile limits out = .ok d' ∧ SameCrypt d'.crypt doc.file.crypt := by
  obtain ⟨p, d', hp, hd, _, _, _, hcr⟩ := writeAnnots_open h
  exact ⟨d', hd, (plan_ok hp).2.1 ▸ hcr⟩

/-! ## C7 -/

/-- **C7 (Plan.md §4): the incremental update is conservative.** For every successful
`writeAnnots limits doc marks aux = .ok out`:

* the original bytes are a prefix of `out` (S8);
* `out`'s chain is the original chain with one new section (`/Prev` = old `startxref`)
  whose object numbers are exactly the plan's keys, and every other object number resolves
  to the same cross-reference entry as in the original;
* `out` opens strictly, and for each page of `marks` its annotation list is the original
  list followed by fresh references that fetch exactly the given annotation dictionaries.

(The object-value form of "every other object unchanged" is tested, see the module doc.) -/
theorem c7 {limits : Limits} {doc : Doc.Doc} {marks : Marks} {aux : List AuxStream}
    {out : ByteArray}
    (h : writeAnnots limits doc marks aux = .ok out) :
    (∃ u, out = doc.file.bytes ++ u) ∧
    ∃ p revs sec' tr' off' d',
      plan limits doc marks aux = .ok p ∧
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

end SafePdf.Spec.Write
