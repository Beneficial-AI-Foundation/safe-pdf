import SafePdf.Core.Open
import SafePdf.Spec.Unambiguous

/-!
# Prefix stability of object resolution (task 9.5e)

Plan.md §4 C7/S8 (the incremental update is conservative), §5.2 (object resolution);
ISO 32000-2 §7.5.6 (incremental updates append bytes).

`Spec.PrefixStable` (task 2.12) shows that the lexer, the object parser and the
cross-reference readers give the same successful results on an extension `b'` of `b`. This
file lifts that to **object resolution** (`Core.Open.OpenDoc.getObject`), the step task 9.5a
left open for C7 (`Spec.Write.writeUpdate_value`). Object resolution depends on more than the
bytes: the lookup (the merged cross-reference section), the fuel (its size), the
object-stream pre-pass and the decryption state. The results:

* **Frame** (`HasEnd`): in a file whose `startxref` is found, the file ends with `%%EOF` and
  optional whitespace, so a keyword such as `endobj` or `stream` never ends at the very end
  (`endobj_lt`, `stream_lt`); every object parse ends with `endobj` (`parseIndirectWith_last`).
  Hence `parseIndirectWith_ext`, `parseLengthObj_ext`, `parseContainerHead_ext`,
  `containerMember_ext`: the pieces of rules L4–L6 are prefix-stable.
* **Resolver change** (`parseIndirectWith_lift`): the length resolver is called at most once
  (`Length.callPoint`); a successful parse stays successful with any resolver that returns
  every length the first returns.
* **`/Length` resolution** (`resolveLengthAux_transfer`): a successful resolution gives the
  same length with the same number of parses on the extension, with more fuel, and with a
  lookup that may differ on a set `K` of numbers that cannot take part in a resolution
  (`NotLen`: no resolution of a reference to them succeeds, and an in-use one is not a
  stream, so it is no object-stream container). The second recursive call of rule L6 gets
  `fuel - used`, which is monotone because the count is preserved. Resolution is also
  deterministic in its value across fuel and visiting lists (`resolveLengthAux_det`).
* **Objects** (`parseIndirectResolved_transfer`, `fetchCompressed_transfer`,
  `getObject_transfer`): every successful fetch of a number outside `K` is the same on the
  extended document, provided the decryption state is the same (then the pre-pass and the
  decryption are the same functions).
* **Which numbers are in `K`** (`notLen_of_none`, `notLen_of_dict`): a number without an entry,
  or one whose object fetches as a dictionary — rules L4/L6 need an integer or a reference
  (decryption keeps an object's kind, `decrypt_dict`), and a container needs a stream. For an
  object in an object stream this compares the member that rule L6 would read with the one
  `fetchCompressed` read: same container, same data length (`containerLength_lengthOf`, by
  determinism), same decode.
* **The lookup** (`lookup_eq`): the binary search of `OpenDoc.lookup` is exactly
  `lookupEntry` on the section (`bsearch_sound`, `bsearch_complete`); one more revision in
  front changes only the numbers it lists (`mergeChain_cons_lookup_none`) and never shrinks
  the section (`mergeChain_cons_length`, so the fuel grows).
* **The decryption state** (`crypt_eq_of_ref`): two strict documents whose states have the
  same key bytes and the same *indirect* encryption dictionary `r` (same entry in both
  sections) have equal states — the dictionary fetches identically (`getObject_transfer_obj`,
  a direct object needs no `/Length`), and `Crypt.setup` is determined by it and the key
  (`setup_eq`).

Only successful results are claimed stable (as in `Spec.PrefixStable`): an error of the
original may become another error, or a success, on the extension.
-/

namespace SafePdf.Spec.WritePrefix

open SafePdf SafePdf.Core
open SafePdf.Core.Xref (XrefEntry)
open SafePdf.Spec.PrefixStable (Extends)

/-! ## The end of a file with a `startxref` -/

/-- The input has a `startxref` that is found: it ends with `%%EOF` and optional whitespace,
so no keyword token ends at its very end (`PrefixStable.findStartxref_last`). -/
def HasEnd (b : ByteArray) : Prop := ∃ start, Xref.findStartxref b = .ok start

/-- In a file with an end, a keyword of at least two bytes whose last byte is neither `F`
nor whitespace ends strictly before the end. -/
theorem keyword_end_lt {b : ByteArray} (hs : HasEnd b) {p : Nat} {k : List UInt8} {q : Nat}
    (h : Lex.next b p = .ok (some (.keyword k, q))) (hk : 2 ≤ k.length) {c : UInt8}
    (hc : k.getLast? = some c) (hc70 : c ≠ 70) (hcw : Lex.isWhite c = false) : q < b.size := by
  obtain ⟨start, hs⟩ := hs
  have := PrefixStable.next_keyword_last h hk
  rw [hc] at this
  exact PrefixStable.end_lt_of_last hs this hc70 hcw

/-- `endobj` ends strictly before the end of a file with an end. -/
theorem endobj_lt {b : ByteArray} (hs : HasEnd b) {p q : Nat}
    (h : Lex.next b p = .ok (some (.keyword ObjParse.kwEndobj, q))) : q < b.size :=
  keyword_end_lt hs h (by decide) (c := 106) rfl (by decide) (by decide)

/-- `stream` ends strictly before the end of a file with an end. -/
theorem stream_lt {b : ByteArray} (hs : HasEnd b) {p q : Nat}
    (h : Lex.next b p = .ok (some (.keyword ObjParse.kwStream, q))) : q < b.size :=
  keyword_end_lt hs h (by decide) (c := 109) rfl (by decide) (by decide)

/-- An `expectKeyword` success lexed that keyword. -/
theorem expectKeyword_next {b : ByteArray} {pos : Nat} {kw : List UInt8} {msg : String}
    {r : Nat} (h : ObjParse.expectKeyword b pos kw msg = .ok r) :
    Lex.next b pos = .ok (some (.keyword kw, r)) := by
  unfold ObjParse.expectKeyword at h
  split at h
  · simp at h
  · rename_i k q hq
    split at h
    · rename_i hk
      simp only [Except.ok.injEq] at h
      subst h hk
      exact hq
    · simp at h
  · simp at h

/-- A stream body ends with `endobj`. -/
theorem parseStreamBodyWith_last {len : ObjParse.LengthResolver} {b : ByteArray} {p : Nat}
    {d : Dict} {st : Stream} {r : Nat} (h : ObjParse.parseStreamBodyWith len b p d = .ok (st, r)) :
    ∃ q, Lex.next b q = .ok (some (.keyword ObjParse.kwEndobj, r)) := by
  unfold ObjParse.parseStreamBodyWith at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · dsimp only at h
        split at h
        · split at h
          · split at h
            · rename_i r5 h5
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨-, rfl⟩ := h
              exact ⟨_, expectKeyword_next h5⟩
            · simp at h
          · simp at h
        · simp at h
        · simp at h
      · simp at h

/-- An indirect-object body ends with `endobj`. -/
theorem parseIndirectBodyWith_last {len : ObjParse.LengthResolver} {limits : Limits}
    {b : ByteArray} {p : Nat} {body : IndirectBody} {r : Nat}
    (h : ObjParse.parseIndirectBodyWith len limits b p = .ok (body, r)) :
    ∃ q, Lex.next b q = .ok (some (.keyword ObjParse.kwEndobj, r)) := by
  unfold ObjParse.parseIndirectBodyWith at h
  split at h
  · simp at h
  · rename_i o r1 h1
    split at h
    · simp at h
    · rename_i k r2 h2
      split at h
      · rename_i hk
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact ⟨r1, hk ▸ h2⟩
      · split at h
        · split at h
          · split at h
            · rename_i s0 r3 h3
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨-, rfl⟩ := h
              exact parseStreamBodyWith_last h3
            · simp at h
          · simp at h
        · simp at h
    · simp at h

/-- `parseIndirectWith` ends with `endobj`. -/
theorem parseIndirectWith_last {lenF : Nat → ObjParse.LengthResolver} {limits : Limits}
    {b : ByteArray} {pos : Nat} {io : IndirectObject} {r : Nat}
    (h : Xref.Length.parseIndirectWith lenF limits b pos = .ok (io, r)) :
    ∃ q, Lex.next b q = .ok (some (.keyword ObjParse.kwEndobj, r)) := by
  unfold Xref.Length.parseIndirectWith at h
  split at h
  · simp at h
  · split at h
    · rename_i body r1 hb
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact parseIndirectBodyWith_last hb
    · simp at h

/-! ## Parsing in an extension, same length resolver -/

/-- `parseIndirectWith` (any resolver) is prefix-stable in a file with an end. -/
theorem parseIndirectWith_ext {b b' : ByteArray} (hE : Extends b b') (hs : HasEnd b)
    {lenF : Nat → ObjParse.LengthResolver} {limits : Limits} {pos : Nat} {io : IndirectObject}
    {r : Nat} (h : Xref.Length.parseIndirectWith lenF limits b pos = .ok (io, r)) :
    Xref.Length.parseIndirectWith lenF limits b' pos = .ok (io, r) := by
  obtain ⟨q0, hq0⟩ := parseIndirectWith_last h
  have hr := endobj_lt hs hq0
  unfold Xref.Length.parseIndirectWith at h ⊢
  split at h
  · simp at h
  · rename_i n g q hh
    split at h
    · rename_i body r1 hb
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have := (ObjParse.parseIndirectBodyWith_ok hb).1
      rw [PrefixStable.parseHeader_ext hE hh (by omega)]
      simp only
      rw [PrefixStable.parseIndirectBodyWith_ext hE hb hr]
    · simp at h

/-! ## Changing the length resolver -/

/-- A successful `parseIndirectWith` that reaches its call point called the resolver there
successfully. -/
theorem parseIndirectWith_called {lenF : Nat → ObjParse.LengthResolver} {limits : Limits}
    {b : ByteArray} {pos : Nat} {x : IndirectObject × Nat}
    (h : Xref.Length.parseIndirectWith lenF limits b pos = .ok x) {n : Nat} {d : Dict} {p : Nat}
    (hc : Xref.Length.callPoint limits b pos = some (n, d, p)) : ∃ l, lenF n d p = .ok l := by
  unfold Xref.Length.callPoint at hc
  unfold Xref.Length.parseIndirectWith at h
  split at hc
  · simp at hc
  · rename_i n0 g0 q hh
    rw [hh] at h
    simp only at h
    split at hc
    · simp at hc
    · rename_i o r ho
      split at hc
      · rename_i k r2 hk
        split at hc
        · simp at hc
        · rename_i hk1
          split at hc
          · rename_i hk2
            split at hc
            · rename_i dd
              split at hc
              · rename_i s hs
                simp only [Option.some.injEq, Prod.mk.injEq] at hc
                obtain ⟨rfl, rfl, rfl⟩ := hc
                unfold ObjParse.parseIndirectBodyWith at h
                rw [ho] at h
                simp only [hk, hk2, show ObjParse.kwStream ≠ ObjParse.kwEndobj by decide, ↓reduceIte] at h
                unfold ObjParse.parseStreamBodyWith at h
                rw [hs] at h
                simp only at h
                revert h
                cases hl : lenF n0.toNat dd r2 with
                | error e => simp
                | ok l => intro _; exact ⟨l, rfl⟩
              · simp at hc
            · simp at hc
          · simp at hc
      · simp at hc

/-- **Changing the resolver**: a successful `parseIndirectWith lenF` gives the same result
with any resolver `lenG` that returns every length `lenF` returns. -/
theorem parseIndirectWith_lift {lenF lenG : Nat → ObjParse.LengthResolver} {limits : Limits}
    {b : ByteArray} {pos : Nat} {x : IndirectObject × Nat}
    (h : Xref.Length.parseIndirectWith lenF limits b pos = .ok x)
    (hl : ∀ n d p l, lenF n d p = .ok l → lenG n d p = .ok l) :
    Xref.Length.parseIndirectWith lenG limits b pos = .ok x := by
  rw [← h]
  symm
  apply Xref.Length.parseIndirectWith_congr
  intro n d p hc
  obtain ⟨l, hlv⟩ := parseIndirectWith_called h hc
  rw [hlv, hl n d p l hlv]

/-! ## The pieces of `/Length` resolution in an extension -/

/-- An object followed by `endobj` (or `stream`) needs no more lookahead than that keyword. -/
theorem follow_keyword {b : ByteArray} {r : Nat} {k : List UInt8} {r2 : Nat}
    (h : Lex.next b r = .ok (some (.keyword k, r2))) (hr2 : r2 < b.size) :
    PrefixStable.Follow b r :=
  ⟨⟨_, _, h, hr2⟩, fun g q he => by rw [h] at he; simp at he⟩

/-- `parseLengthObj` is prefix-stable in a file with an end. -/
theorem parseLengthObj_ext {b b' : ByteArray} (hE : Extends b b') (hs : HasEnd b)
    {limits : Limits} {off n g : Nat} {o : PdfObject}
    (h : Xref.Length.parseLengthObj limits b off n g = .ok o) :
    Xref.Length.parseLengthObj limits b' off n g = .ok o := by
  unfold Xref.Length.parseLengthObj at h ⊢
  split at h
  · simp at h
  · rename_i n' g' q hh
    split at h
    · rename_i hng
      split at h
      · simp at h
      · rename_i o1 r ho
        split at h
        · rename_i r' hr'
          have hk := expectKeyword_next hr'
          have hlt := endobj_lt hs hk
          have p1 := ObjParse.parseObject_pos ho
          have p2 := Lex.next_pos _ _ _ _ hk
          rw [PrefixStable.parseHeader_ext hE hh (by omega)]
          simp only [hng, and_self, ↓reduceIte]
          unfold ObjParse.parseObject at ho ⊢
          rw [PrefixStable.parseObj_ext hE ho (follow_keyword hk hlt)]
          simp only
          rw [PrefixStable.expectKeyword_ext hE hr' hlt]
          exact h
        · simp at h
    · simp at h

/-- `parseContainerHead` is prefix-stable in a file with an end. -/
theorem parseContainerHead_ext {b b' : ByteArray} (hE : Extends b b') (hs : HasEnd b)
    {limits : Limits} {off c : Nat} {d : Dict} {p : Nat}
    (h : Xref.Length.parseContainerHead limits b off c = .ok (d, p)) :
    Xref.Length.parseContainerHead limits b' off c = .ok (d, p) := by
  unfold Xref.Length.parseContainerHead at h ⊢
  split at h
  · simp at h
  · rename_i n' g' q hh
    split at h
    · rename_i hng
      split at h
      · simp at h
      · rename_i o1 r ho
        split at h
        · simp at h
        · rename_i k r2 hk
          split at h
          · rename_i hks
            subst hks
            have hlt := stream_lt hs hk
            have p1 := ObjParse.parseObject_pos ho
            have p2 := Lex.next_pos _ _ _ _ hk
            rw [PrefixStable.parseHeader_ext hE hh (by omega)]
            simp only [hng, and_self, ↓reduceIte]
            unfold ObjParse.parseObject at ho ⊢
            rw [PrefixStable.parseObj_ext hE ho (follow_keyword hk hlt)]
            simp only
            rw [PrefixStable.next_ext hE r hk hlt]
            simp only [↓reduceIte]
            cases o1 <;> first | exact h | simp at h
          · simp at h
        · simp at h
    · simp at h

/-- `containerMember` is prefix-stable in a file with an end. -/
theorem containerMember_ext {b b' : ByteArray} (hE : Extends b b') (hs : HasEnd b)
    {pre : Xref.ObjStm.Pre} {limits : Limits} {off c num idx : Nat} {d : Dict} {p : Nat}
    {len : Except Error Nat} {o : PdfObject}
    (h : Xref.Length.containerMember pre limits b off c num idx d p len = .ok o) :
    Xref.Length.containerMember pre limits b' off c num idx d p len = .ok o := by
  unfold Xref.Length.containerMember at h ⊢
  split at h
  · simp at h
  · split at h
    · simp at h
    · rename_i st0 r3 h3
      obtain ⟨q, hq⟩ := parseStreamBodyWith_last h3
      rw [PrefixStable.parseStreamBodyWith_ext hE h3 (endobj_lt hs hq)]
      exact h

/-! ## `/Length` resolution under a changed cross-reference lookup -/

/-- The object at `off` is not a stream: its header, its object and `endobj` parse. -/
def RawPlain (limits : Limits) (b : ByteArray) (off : Nat) : Prop :=
  ∃ n g q o r r2, ObjParse.parseHeader b off = .ok (n, g, q) ∧
    ObjParse.parseObject limits b q = .ok (o, r) ∧
    Lex.next b r = .ok (some (.keyword ObjParse.kwEndobj, r2))

/-- Object number `m` can be dropped from a `/Length` resolution: no resolution of a
reference to `m` succeeds, and if `m` is in use its object is not a stream (so it is no
object-stream container). The numbers an update rewrites have this property in the original
(`notLen_of_dict`, `notLen_of_none`). -/
structure NotLen (pre : Xref.ObjStm.Pre) (L : Nat → Option XrefEntry) (limits : Limits)
    (b : ByteArray) (m : Nat) : Prop where
  /-- No resolution of a reference to `m` succeeds. -/
  res : ∀ fuel vis g c v, Xref.Length.resolveLengthAux pre L limits b fuel vis (m, g) ≠ (c, .ok v)
  /-- An in-use `m` is not a stream. -/
  plain : ∀ off g, L m = some (.inUse off g) → RawPlain limits b off

/-- A container head does not parse at a plain object. -/
theorem parseContainerHead_of_plain {limits : Limits} {b : ByteArray} {off c : Nat}
    (hp : RawPlain limits b off) {d : Dict} {p : Nat} :
    Xref.Length.parseContainerHead limits b off c ≠ .ok (d, p) := by
  obtain ⟨n, g, q, o, r, r2, hh, ho, hk⟩ := hp
  unfold Xref.Length.parseContainerHead
  rw [hh]
  simp only
  split
  · rw [ho]
    simp only
    rw [hk]
    simp only [show ObjParse.kwEndobj ≠ ObjParse.kwStream by decide, ↓reduceIte]
    simp
  · simp

/-- `containerLength` passes a successful resolution on to a resolver that returns every
result of the first. -/
theorem containerLength_transfer {res res' : List Nat → Nat × Nat → Nat × Except Error Nat}
    (hres : ∀ v r c x, res v r = (c, .ok x) → res' v r = (c, .ok x)) {vis : List Nat}
    {d : Dict} {p c1 : Nat} {e1 : Except Error Nat}
    (h : Xref.Length.containerLength res vis d p = (c1, e1)) :
    (∀ l, e1 = .ok l → Xref.Length.containerLength res' vis d p = (c1, e1)) := by
  intro l hl
  subst hl
  unfold Xref.Length.containerLength at h ⊢
  split at h
  · exact hres _ _ _ _ h
  · exact h

/-- Two successful `containerLength` runs with resolvers that agree on success agree. -/
theorem containerLength_det {res1 res2 : List Nat → Nat × Nat → Nat × Except Error Nat}
    {v1 v2 : List Nat} {d : Dict} {p c1 c2 l1 l2 : Nat}
    (hres : ∀ r a1 a2 x y, res1 v1 r = (a1, .ok x) → res2 v2 r = (a2, .ok y) → x = y)
    (h1 : Xref.Length.containerLength res1 v1 d p = (c1, .ok l1))
    (h2 : Xref.Length.containerLength res2 v2 d p = (c2, .ok l2)) : l1 = l2 := by
  unfold Xref.Length.containerLength at h1 h2
  split at h1
  · rename_i m g hm
    rw [hm] at h2
    exact hres _ _ _ _ _ h1 h2
  · rename_i hm
    split at h2
    · rename_i m g hm'
      exact absurd hm' (hm m g)
    · simp only [Prod.mk.injEq] at h1 h2
      rw [h1.2] at h2
      exact Except.ok.inj h2.2

/-- **`/Length` resolution is deterministic**: two successful resolutions of the same
reference (any fuel, any visiting lists) give the same length. -/
theorem resolveLengthAux_det {pre : Xref.ObjStm.Pre} {L : Nat → Option XrefEntry}
    {limits : Limits} {b : ByteArray} :
    ∀ f1 f2 v1 v2 ref c1 c2 x y,
      Xref.Length.resolveLengthAux pre L limits b f1 v1 ref = (c1, .ok x) →
      Xref.Length.resolveLengthAux pre L limits b f2 v2 ref = (c2, .ok y) → x = y := by
  intro f1
  induction f1 using Nat.strongRecOn with
  | _ f1 ih =>
  intro f2 v1 v2 ref c1 c2 x y h1 h2
  obtain ⟨m, g⟩ := ref
  rw [Xref.Length.resolveLengthAux.eq_def] at h1 h2
  by_cases hv1 : m ∈ v1
  · simp [hv1] at h1
  by_cases hv2 : m ∈ v2
  · simp [hv2] at h2
  simp only [hv1, hv2, ↓reduceIte] at h1 h2
  rcases f1 with _ | f1
  · simp at h1
  rcases f2 with _ | f2
  · simp at h2
  simp only at h1 h2
  rcases hlm : L m with _ | e
  · rw [hlm] at h1; simp at h1
  rw [hlm] at h1 h2
  rcases e with ⟨a0, b0⟩ | ⟨off, g'⟩ | ⟨cc, idx⟩
  · simp at h1
  · simp only at h1 h2
    by_cases hg : g' = g
    · simp only [hg, ↓reduceIte] at h1 h2
      rcases hp : Xref.Length.parseLengthObj limits b off m g with e | o
      · rw [hp] at h1; simp at h1
      rw [hp] at h1 h2
      cases o with
      | int l =>
        simp only [Prod.mk.injEq] at h1 h2
        rw [h1.2] at h2
        exact Except.ok.inj h2.2
      | ref m2 g2 =>
        simp only at h1 h2
        rcases hr1 : Xref.Length.resolveLengthAux pre L limits b f1 (m :: v1) (m2, g2)
          with ⟨a1, r1⟩
        rcases hr2 : Xref.Length.resolveLengthAux pre L limits b f2 (m :: v2) (m2, g2)
          with ⟨a2, r2⟩
        rw [hr1] at h1
        rw [hr2] at h2
        simp only [Prod.mk.injEq] at h1 h2
        rw [h1.2] at hr1
        rw [h2.2] at hr2
        exact ih f1 (by omega) f2 _ _ _ _ _ x y hr1 hr2
      | _ => simp at h1
    · simp [hg] at h1
  · simp only at h1 h2
    by_cases hc1 : cc = m ∨ cc ∈ v1
    · simp [hc1] at h1
    by_cases hc2 : cc = m ∨ cc ∈ v2
    · simp [hc2] at h2
    simp only [hc1, hc2, ↓reduceIte] at h1 h2
    rcases hlc : L cc with _ | e2
    · rw [hlc] at h1; simp at h1
    rw [hlc] at h1 h2
    rcases e2 with ⟨a0, b0⟩ | ⟨off, g2⟩ | ⟨c3, i3⟩
    · simp at h1
    · simp only at h1 h2
      by_cases hg2 : g2 = 0
      · simp only [hg2, ↓reduceIte] at h1 h2
        rcases hph : Xref.Length.parseContainerHead limits b off cc with e | ⟨d, p⟩
        · rw [hph] at h1; simp at h1
        rw [hph] at h1 h2
        simp only at h1 h2
        rcases hr1 : Xref.Length.containerLength
          (fun v r => Xref.Length.resolveLengthAux pre L limits b f1 v r) (cc :: m :: v1) d p
          with ⟨k1, e1⟩
        rcases hr2 : Xref.Length.containerLength
          (fun v r => Xref.Length.resolveLengthAux pre L limits b f2 v r) (cc :: m :: v2) d p
          with ⟨k2, e2⟩
        rw [hr1] at h1
        rw [hr2] at h2
        rcases e1 with e | l1
        · simp [Xref.Length.containerMember] at h1
        rcases e2 with e | l2
        · simp [Xref.Length.containerMember] at h2
        have hl : l1 = l2 := containerLength_det
          (fun r a1 a2 x' y' hx hy => ih f1 (by omega) f2 _ _ r a1 a2 x' y' hx hy) hr1 hr2
        subst hl
        simp only at h1 h2
        rcases hm : Xref.Length.containerMember pre limits b off cc m idx d p (.ok l1) with e | o
        · rw [hm] at h1; simp at h1
        rw [hm] at h1 h2
        cases o with
        | int l =>
          simp only [Prod.mk.injEq] at h1 h2
          rw [h1.2] at h2
          exact Except.ok.inj h2.2
        | ref m2 g3 =>
          simp only at h1 h2
          rcases hq1 : Xref.Length.resolveLengthAux pre L limits b (f1 - k1) (m :: v1) (m2, g3)
            with ⟨a1, r1⟩
          rcases hq2 : Xref.Length.resolveLengthAux pre L limits b (f2 - k2) (m :: v2) (m2, g3)
            with ⟨a2, r2⟩
          rw [hq1] at h1
          rw [hq2] at h2
          simp only [Prod.mk.injEq] at h1 h2
          rw [h1.2] at hq1
          rw [h2.2] at hq2
          exact ih (f1 - k1) (by omega) _ _ _ _ _ _ x y hq1 hq2
        | _ => simp at h1
      · simp [hg2] at h1
    · simp at h1

/-- **`/Length` resolution is stable** under appending bytes, adding fuel and changing the
lookup outside a set `K` of numbers that cannot take part in a resolution (`NotLen`): a
successful resolution gives the same value with the same number of parses. -/
theorem resolveLengthAux_transfer {pre : Xref.ObjStm.Pre} {L L' : Nat → Option XrefEntry}
    {limits : Limits} {b b' : ByteArray} (hE : Extends b b') (hs : HasEnd b) {K : List Nat}
    (hL : ∀ m, m ∉ K → L' m = L m) (hK : ∀ m ∈ K, NotLen pre L limits b m) :
    ∀ fuel fuel' vis ref c v,
      Xref.Length.resolveLengthAux pre L limits b fuel vis ref = (c, .ok v) → fuel ≤ fuel' →
      Xref.Length.resolveLengthAux pre L' limits b' fuel' vis ref = (c, .ok v) := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ fuel ih =>
  intro fuel' vis ref c v h hle
  obtain ⟨m, g⟩ := ref
  by_cases hmK : m ∈ K
  · exact absurd h ((hK m hmK).res fuel vis g c v)
  rw [Xref.Length.resolveLengthAux.eq_def] at h ⊢
  by_cases hvis : m ∈ vis
  · simp [hvis] at h
  simp only [hvis, ↓reduceIte] at h ⊢
  rcases fuel with _ | f
  · simp at h
  obtain ⟨f', rfl⟩ : ∃ f', fuel' = f' + 1 := ⟨fuel' - 1, by omega⟩
  have hff : f ≤ f' := by omega
  simp only at h ⊢
  rw [hL m hmK]
  rcases hlm : L m with _ | e
  · rw [hlm] at h
    simp at h
  rw [hlm] at h
  rcases e with ⟨a0, b0⟩ | ⟨off, g'⟩ | ⟨cc, idx⟩
  · simp at h
  · -- in use
    simp only at h ⊢
    by_cases hg : g' = g
    · simp only [hg, ↓reduceIte] at h ⊢
      rcases hp : Xref.Length.parseLengthObj limits b off m g with e | o
      · rw [hp] at h; simp at h
      rw [hp] at h
      rw [parseLengthObj_ext hE hs hp]
      cases o with
      | ref m2 h2 =>
        simp only at h ⊢
        rcases hr : Xref.Length.resolveLengthAux pre L limits b f (m :: vis) (m2, h2) with ⟨c1, r1⟩
        rw [hr] at h
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [ih f (by omega) f' (m :: vis) (m2, h2) c1 v hr hff]
      | _ => first | exact h | simp at h
    · simp [hg] at h
  · -- in an object stream
    simp only at h ⊢
    by_cases hc : cc = m ∨ cc ∈ vis
    · simp [hc] at h
    simp only [hc, ↓reduceIte] at h ⊢
    rcases hlc : L cc with _ | e2
    · rw [hlc] at h; simp at h
    rw [hlc] at h
    rcases e2 with ⟨a0, b0⟩ | ⟨off, g2⟩ | ⟨c2, i2⟩
    · simp at h
    · simp only at h
      by_cases hg2 : g2 = 0
      · simp only [hg2, ↓reduceIte] at h
        rcases hph : Xref.Length.parseContainerHead limits b off cc with e | ⟨d, p⟩
        · rw [hph] at h; simp at h
        have hcK : cc ∉ K := fun hcK =>
          parseContainerHead_of_plain ((hK cc hcK).plain off g2 hlc) hph
        rw [hL cc hcK, hlc]
        simp only [hg2, ↓reduceIte]
        rw [parseContainerHead_ext hE hs hph]
        rw [hph] at h
        simp only at h ⊢
        rcases hr1 : Xref.Length.containerLength
          (fun v r => Xref.Length.resolveLengthAux pre L limits b f v r) (cc :: m :: vis) d p
          with ⟨c1, e1⟩
        rw [hr1] at h
        rcases e1 with e | l
        · simp [Xref.Length.containerMember] at h
        have hr1' := containerLength_transfer (fun v r c x hx => ih f (by omega) f' v r c x hx hff)
          hr1 l rfl
        rw [hr1']
        simp only at h ⊢
        rcases hm : Xref.Length.containerMember pre limits b off cc m idx d p (.ok l) with e | o
        · rw [hm] at h; simp at h
        rw [hm] at h
        rw [containerMember_ext hE hs hm]
        cases o with
        | ref m2 h2 =>
          simp only at h ⊢
          rcases hr2 : Xref.Length.resolveLengthAux pre L limits b (f - c1) (m :: vis) (m2, h2)
            with ⟨c3, r3⟩
          rw [hr2] at h
          simp only [Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rw [ih (f - c1) (by omega) (f' - c1) (m :: vis) (m2, h2) c3 v hr2 (by omega)]
        | _ => first | exact h | simp at h
      · simp [hg2] at h
    · simp at h

/-- The length resolver of rule L5 is stable in the same sense (`resolveLengthAux_transfer`). -/
theorem lengthOf_transfer {pre : Xref.ObjStm.Pre} {L L' : Nat → Option XrefEntry}
    {limits : Limits} {b b' : ByteArray} (hE : Extends b b') (hs : HasEnd b) {K : List Nat}
    (hL : ∀ m, m ∉ K → L' m = L m) (hK : ∀ m ∈ K, NotLen pre L limits b m) {fuel fuel' : Nat}
    (hff : fuel ≤ fuel') :
    ∀ n d p l, Xref.Length.lengthOf pre L limits b fuel n d p = .ok l →
      Xref.Length.lengthOf pre L' limits b' fuel' n d p = .ok l := by
  intro n d p l h
  unfold Xref.Length.lengthOf at h ⊢
  rcases hd : Xref.Length.lengthDict pre L limits b fuel n d with e | d'
  · rw [hd] at h; simp at h
  rw [hd] at h
  have hd' : Xref.Length.lengthDict pre L' limits b' fuel' n d = .ok d' := by
    unfold Xref.Length.lengthDict Xref.Length.resolveLength at hd ⊢
    rcases hm : Dict.lookup d ObjParse.nameLength with _ | o
    · rw [hm] at hd; exact hd
    cases o with
    | ref m g =>
      rw [hm] at hd
      simp only at hd ⊢
      rcases hr : Xref.Length.resolveLengthAux pre L limits b fuel [n] (m, g) with ⟨c, e⟩
      rw [hr] at hd
      rcases e with e | v
      · simp at hd
      rw [resolveLengthAux_transfer hE hs hL hK fuel fuel' [n] (m, g) c v hr hff]
      exact hd
    | _ => rw [hm] at hd; exact hd
  rw [hd']
  exact h

/-- **Indirect objects with resolved `/Length` are stable** (rule L5): a successful
`parseIndirectResolved` gives the same object in an extension of a file with an end, with
more fuel and a lookup changed only on numbers that cannot take part in a `/Length`
resolution. -/
theorem parseIndirectResolved_transfer {pre : Xref.ObjStm.Pre} {L L' : Nat → Option XrefEntry}
    {limits : Limits} {b b' : ByteArray} (hE : Extends b b') (hs : HasEnd b) {K : List Nat}
    (hL : ∀ m, m ∉ K → L' m = L m) (hK : ∀ m ∈ K, NotLen pre L limits b m) {fuel fuel' : Nat}
    (hff : fuel ≤ fuel') {pos : Nat} {x : IndirectObject × Nat}
    (h : Xref.Length.parseIndirectResolved L limits b fuel pos pre = .ok x) :
    Xref.Length.parseIndirectResolved L' limits b' fuel' pos pre = .ok x := by
  rw [Xref.Length.parseIndirectResolved_eq_with] at h ⊢
  have h1 := parseIndirectWith_lift h (lengthOf_transfer hE hs hL hK hff)
  obtain ⟨io, r⟩ := x
  exact parseIndirectWith_ext hE hs h1

/-- At a plain object (`RawPlain`), `parseIndirectWith` returns a direct object. -/
theorem parseIndirectWith_plain {lenF : Nat → ObjParse.LengthResolver} {limits : Limits}
    {b : ByteArray} {off : Nat} (hp : RawPlain limits b off) {io : IndirectObject} {r : Nat}
    (h : Xref.Length.parseIndirectWith lenF limits b off = .ok (io, r)) :
    ∃ o, io.body = .obj o := by
  obtain ⟨n, g, q, o, r0, r2, hh, ho, hk⟩ := hp
  unfold Xref.Length.parseIndirectWith ObjParse.parseIndirectBodyWith at h
  rw [hh] at h
  simp only at h
  rw [ho] at h
  simp only at h
  rw [hk] at h
  simp only [↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  exact ⟨o, rfl⟩

/-- A direct object (not a stream) parses the same way with any length resolver. -/
theorem parseIndirectWith_obj {lenF lenG : Nat → ObjParse.LengthResolver} {limits : Limits}
    {b : ByteArray} {pos : Nat} {io : IndirectObject} {r : Nat} {o : PdfObject}
    (h : Xref.Length.parseIndirectWith lenF limits b pos = .ok (io, r)) (ho : io.body = .obj o) :
    Xref.Length.parseIndirectWith lenG limits b pos = .ok (io, r) := by
  rw [← h]
  symm
  apply Xref.Length.parseIndirectWith_congr
  intro n d p hc
  exfalso
  unfold Xref.Length.callPoint at hc
  unfold Xref.Length.parseIndirectWith ObjParse.parseIndirectBodyWith at h
  split at hc
  · simp at hc
  · rename_i n0 g0 q hh
    rw [hh] at h
    simp only at h
    split at hc
    · simp at hc
    · rename_i o1 r1 ho1
      rw [ho1] at h
      simp only at h
      split at hc
      · rename_i k r2 hk
        rw [hk] at h
        simp only at h
        split at hc
        · simp at hc
        · rename_i hk1
          split at hc
          · rename_i hk2
            subst hk2
            simp only [show ObjParse.kwStream ≠ ObjParse.kwEndobj by decide, ↓reduceIte] at h
            cases o1 with
            | dict dd =>
              simp only at h
              split at h
              · rename_i heq
                simp only [Except.ok.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, -⟩ := h
                simp only at ho
                subst ho
                split at heq <;> simp at heq
              · simp at h
            | _ => simp at h
          · simp at hc
      · simp at hc

/-- **Object-stream members are stable** (rule G3): a successful `fetchCompressed` of a number
outside `K` gives the same object in the extension, with more fuel and the changed lookup;
the container is not in `K` (a number of `K` in use is not a stream). -/
theorem fetchCompressed_transfer {pre : Xref.ObjStm.Pre} {L L' : Nat → Option XrefEntry}
    {limits : Limits} {b b' : ByteArray} (hE : Extends b b') (hs : HasEnd b) {K : List Nat}
    (hL : ∀ m, m ∉ K → L' m = L m) (hK : ∀ m ∈ K, NotLen pre L limits b m) {fuel fuel' : Nat}
    (hff : fuel ≤ fuel') {num : Nat} (hn : num ∉ K) {o : PdfObject}
    (h : (Xref.ObjStm.fetchCompressedTrace pre L limits b fuel num).result = .ok o) :
    (Xref.ObjStm.fetchCompressedTrace pre L' limits b' fuel' num).result = .ok o := by
  unfold Xref.ObjStm.fetchCompressedTrace at h ⊢
  rw [hL num hn]
  rcases hl : L num with _ | e
  · rw [hl] at h; simp at h
  rw [hl] at h
  rcases e with ⟨a0, b0⟩ | ⟨off0, g0⟩ | ⟨cc, idx⟩
  · simp at h
  · simp at h
  simp only at h ⊢
  by_cases hc : cc = num
  · simp [hc] at h
  simp only [hc, ↓reduceIte] at h ⊢
  rcases hlc : L cc with _ | e2
  · rw [hlc] at h; simp at h
  rw [hlc] at h
  rcases e2 with ⟨a0, b0⟩ | ⟨off, g2⟩ | ⟨c2, i2⟩
  · simp at h
  · simp only at h
    by_cases hg2 : g2 = 0
    · simp only [hg2, ↓reduceIte] at h
      rcases hpr : Xref.Length.parseIndirectResolved L limits b fuel off pre with e | ⟨io, r⟩
      · rw [hpr] at h; simp at h
      rw [hpr] at h
      have hcK : cc ∉ K := by
        intro hcK
        rw [Xref.Length.parseIndirectResolved_eq_with] at hpr
        obtain ⟨o1, ho1⟩ := parseIndirectWith_plain ((hK cc hcK).plain off g2 hlc) hpr
        simp only at h
        split at h
        · rename_i hio
          rw [ho1] at h
          simp at h
        · simp at h
      rw [hL cc hcK, hlc]
      simp only [hg2, ↓reduceIte]
      rw [parseIndirectResolved_transfer hE hs hL hK hff hpr]
      exact h
    · simp [hg2] at h
  · simp at h

/-! ## Object resolution of an opened document -/

/-- **`getObject` is stable** (rules G1–G5): if `d'` extends the bytes of `d` (a file with an
end), has at least its fuel, the same decryption state, and the same lookup outside `K`, and
the numbers of `K` cannot take part in a `/Length` resolution of `d` (`NotLen`), then every
successful fetch of a number outside `K` gives the same body in `d'`. -/
theorem getObject_transfer {d d' : Open.OpenDoc} {limits : Limits}
    (hE : Extends d.bytes d'.bytes) (hs : HasEnd d.bytes) {K : List Nat}
    (hL : ∀ m, m ∉ K → d'.lookup m = d.lookup m)
    (hK : ∀ m ∈ K, NotLen d.pre d.lookup limits d.bytes m)
    (hfuel : d.objectCount ≤ d'.objectCount) (hc : d'.crypt = d.crypt)
    {n g : Nat} (hn : n ∉ K) {v : IndirectBody} (h : d.getObject limits n g = .ok v) :
    d'.getObject limits n g = .ok v := by
  have hpre : d'.pre = d.pre := by unfold Open.OpenDoc.pre; rw [hc]
  have hdec : d'.decrypt = d.decrypt := by
    funext a b0 c0
    unfold Open.OpenDoc.decrypt
    rw [hc]
  unfold Open.OpenDoc.getObject Open.OpenDoc.getObjectTrace at h ⊢
  rw [hL n hn, hpre, hdec]
  rcases hl : d.lookup n with _ | e
  · rw [hl] at h; exact h
  rw [hl] at h
  rcases e with ⟨a, b0⟩ | ⟨off, g'⟩ | ⟨cc, idx⟩
  · exact h
  · simp only at h ⊢
    by_cases hg : g' = g
    · simp only [hg, ↓reduceIte] at h ⊢
      rcases hpr : Xref.Length.parseIndirectResolved d.lookup limits d.bytes d.objectCount off
        d.pre with e | ⟨io, r⟩
      · rw [hpr] at h; simp at h
      rw [hpr] at h
      rw [parseIndirectResolved_transfer hE hs hL hK hfuel hpr]
      exact h
    · simp only [hg, ↓reduceIte] at h ⊢
      exact h
  · simp only at h ⊢
    by_cases hg : g = 0
    · simp only [hg, ↓reduceIte] at h ⊢
      rcases hf : (Xref.ObjStm.fetchCompressedTrace d.pre d.lookup limits d.bytes d.objectCount
        n).result with e | o
      · rw [hf] at h; cases h
      rw [hf] at h
      rw [fetchCompressed_transfer hE hs hL hK hfuel hn hf]
      exact h
    · simp only [hg, ↓reduceIte] at h ⊢
      exact h

/-- **A direct object in use is stable without conditions on other numbers**: in a document
without decryption state, an in-use object that fetches as a direct object (no stream, so no
`/Length` is resolved) fetches the same way from any extension with the same entry. Used for
the encryption dictionary, which is fetched before the decryption state exists. -/
theorem getObject_transfer_obj {d d' : Open.OpenDoc} {limits : Limits}
    (hE : Extends d.bytes d'.bytes) (hs : HasEnd d.bytes) (hc : d.crypt = none)
    (hc' : d'.crypt = none) {n g : Nat} (hl : d'.lookup n = d.lookup n) {off g' : Nat}
    (hin : d.lookup n = some (.inUse off g')) {o : PdfObject}
    (h : d.getObject limits n g = .ok (.obj o)) : d'.getObject limits n g = .ok (.obj o) := by
  unfold Open.OpenDoc.getObject Open.OpenDoc.getObjectTrace at h ⊢
  rw [hl, hin]
  rw [hin] at h
  simp only at h ⊢
  by_cases hg : g' = g
  · simp only [hg, ↓reduceIte] at h ⊢
    rcases hpr : Xref.Length.parseIndirectResolved d.lookup limits d.bytes d.objectCount off
      d.pre with e | ⟨io, r⟩
    · rw [hpr] at h; simp at h
    rw [hpr] at h
    simp only [Open.decrypt_none hc, Open.decrypt_none hc'] at h ⊢
    by_cases hh : io.num = n ∧ io.gen = g
    · simp only [hh, and_self, ↓reduceIte, Except.ok.injEq] at h
      rw [Xref.Length.parseIndirectResolved_eq_with] at hpr
      have h1 := parseIndirectWith_obj
        (lenG := Xref.Length.lengthOf d'.pre d'.lookup limits d'.bytes d'.objectCount) hpr h
      rw [Xref.Length.parseIndirectResolved_eq_with, parseIndirectWith_ext hE hs h1]
      simp only [hh, and_self, ↓reduceIte, h]
    · simp [hh] at h
  · simp only [hg, ↓reduceIte] at h ⊢
    exact h

/-! ## Which numbers cannot take part in a `/Length` resolution -/

/-- A number without an entry cannot take part in a `/Length` resolution. -/
theorem notLen_of_none {pre : Xref.ObjStm.Pre} {L : Nat → Option XrefEntry} {limits : Limits}
    {b : ByteArray} {m : Nat} (h : L m = none) : NotLen pre L limits b m := by
  refine ⟨fun fuel vis g c v hres => ?_, fun off g hl => by rw [h] at hl; cases hl⟩
  rw [Xref.Length.resolveLengthAux.eq_def] at hres
  by_cases hv : m ∈ vis
  · simp [hv] at hres
  simp only [hv, ↓reduceIte] at hres
  rcases fuel with _ | f
  · simp at hres
  simp [h] at hres

/-- The object `o` is at `off`, followed by `endobj`. -/
def RawObj (limits : Limits) (b : ByteArray) (off : Nat) (o : PdfObject) : Prop :=
  ∃ n g q r r2, ObjParse.parseHeader b off = .ok (n, g, q) ∧
    ObjParse.parseObject limits b q = .ok (o, r) ∧
    Lex.next b r = .ok (some (.keyword ObjParse.kwEndobj, r2))

/-- A direct object parsed by `parseIndirectWith` is a `RawObj`. -/
theorem rawObj_of_parse {lenF : Nat → ObjParse.LengthResolver} {limits : Limits}
    {b : ByteArray} {off : Nat} {io : IndirectObject} {r : Nat} {o : PdfObject}
    (h : Xref.Length.parseIndirectWith lenF limits b off = .ok (io, r)) (ho : io.body = .obj o) :
    RawObj limits b off o := by
  unfold Xref.Length.parseIndirectWith ObjParse.parseIndirectBodyWith at h
  split at h
  · simp at h
  · rename_i n g q hh
    split at h
    · rename_i body r1 hb
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      simp only at ho
      subst ho
      split at hb
      · simp at hb
      · rename_i o1 r0 ho1
        split at hb
        · simp at hb
        · rename_i k r2 hk
          split at hb
          · rename_i hk1
            subst hk1
            simp only [Except.ok.injEq, Prod.mk.injEq, IndirectBody.obj.injEq] at hb
            obtain ⟨rfl, -⟩ := hb
            exact ⟨n, g, q, r0, r2, hh, ho1, hk⟩
          · split at hb
            · split at hb
              · split at hb
                · simp at hb
                · simp at hb
              · simp at hb
            · simp at hb
        · simp at hb
    · simp at h

/-- A `RawObj` is `RawPlain`. -/
theorem RawObj.plain {limits : Limits} {b : ByteArray} {off : Nat} {o : PdfObject}
    (h : RawObj limits b off o) : RawPlain limits b off := by
  obtain ⟨n, g, q, r, r2, h1, h2, h3⟩ := h
  exact ⟨n, g, q, o, r, r2, h1, h2, h3⟩

/-- `parseLengthObj` at a `RawObj` returns that object, or fails. -/
theorem parseLengthObj_raw {limits : Limits} {b : ByteArray} {off : Nat} {o : PdfObject}
    (h : RawObj limits b off o) (n g : Nat) {o' : PdfObject}
    (h' : Xref.Length.parseLengthObj limits b off n g = .ok o') : o' = o := by
  obtain ⟨n0, g0, q, r, r2, h1, h2, h3⟩ := h
  unfold Xref.Length.parseLengthObj at h'
  rw [h1] at h'
  simp only at h'
  split at h'
  · rw [h2] at h'
    simp only at h'
    unfold ObjParse.expectKeyword at h'
    rw [h3] at h'
    simp only [↓reduceIte, Except.ok.injEq] at h'
    exact h'.symm
  · simp at h'

/-- A body that decrypts to a dictionary is a direct object that is neither an integer nor a
reference (decryption keeps the object's kind). -/
theorem decrypt_dict {d : Open.OpenDoc} {m g : Nat} {body : IndirectBody} {dd : Dict}
    (h : d.decrypt m g body = .ok (.obj (.dict dd))) :
    ∃ o, body = .obj o ∧ (∀ i, o ≠ .int i) ∧ (∀ a c, o ≠ .ref a c) := by
  unfold Open.OpenDoc.decrypt at h
  split at h
  · cases h
    refine ⟨.dict dd, rfl, fun i hi => ?_, fun a c hi => ?_⟩ <;> cases hi
  · rename_i st _
    unfold Crypt.decryptBody at h
    split at h
    · cases h
      refine ⟨.dict dd, rfl, fun i hi => ?_, fun a c hi => ?_⟩ <;> cases hi
    · rcases body with o | s
      · refine ⟨o, rfl, fun i hi => ?_, fun a c hi => ?_⟩
        · subst hi
          simp [Crypt.decryptObj, Except.map] at h
        · subst hi
          simp [Crypt.decryptObj, Except.map] at h
      · simp only at h
        split at h
        · cases h
        · split at h
          · cases h
          · split at h
            · cases h
            · cases h

/-- Fetching an in-use object to a dictionary exposes it raw (rules G2, G5). -/
theorem getObject_inUse_dict {d : Open.OpenDoc} {limits : Limits} {m gk : Nat} {dd : Dict}
    (h : d.getObject limits m gk = .ok (.obj (.dict dd))) {off g : Nat}
    (hl : d.lookup m = some (.inUse off g)) :
    ∃ o, RawObj limits d.bytes off o ∧ (∀ i, o ≠ .int i) ∧ (∀ a c, o ≠ .ref a c) := by
  unfold Open.OpenDoc.getObject Open.OpenDoc.getObjectTrace at h
  rw [hl] at h
  simp only at h
  split at h
  · rcases hpr : Xref.Length.parseIndirectResolved d.lookup limits d.bytes d.objectCount off
      d.pre with e | ⟨io, r⟩
    · rw [hpr] at h; simp at h
    rw [hpr] at h
    simp only at h
    split at h
    · obtain ⟨o, ho, hi, hr⟩ := decrypt_dict h
      rw [Xref.Length.parseIndirectResolved_eq_with] at hpr
      exact ⟨o, rawObj_of_parse hpr ho, hi, hr⟩
    · simp at h
  · simp [Open.nullBody] at h

/-- A container's own `/Length` (rule L6) and the length resolver of rule L5 agree when both
succeed (`resolveLengthAux_det`). -/
theorem containerLength_lengthOf {pre : Xref.ObjStm.Pre} {L : Nat → Option XrefEntry}
    {limits : Limits} {b : ByteArray} {f : Nat} {vis : List Nat} {d : Dict} {p c1 l fuel n l1 : Nat}
    (h1 : Xref.Length.containerLength
      (fun v r => Xref.Length.resolveLengthAux pre L limits b f v r) vis d p = (c1, .ok l))
    (h2 : Xref.Length.lengthOf pre L limits b fuel n d p = .ok l1) : l = l1 := by
  unfold Xref.Length.containerLength at h1
  unfold Xref.Length.lengthOf Xref.Length.lengthDict Xref.Length.resolveLength at h2
  rcases hm : Dict.lookup d ObjParse.nameLength with _ | o
  · rw [hm] at h1 h2
    simp only [Prod.mk.injEq] at h1 h2
    rw [h1.2] at h2
    exact Except.ok.inj h2
  cases o with
  | ref m g =>
    rw [hm] at h1 h2
    simp only at h1 h2
    rcases hr : Xref.Length.resolveLengthAux pre L limits b fuel [n] (m, g) with ⟨c2, e⟩
    rw [hr] at h2
    rcases e with e | len
    · simp at h2
    simp only [ObjParse.streamLength, Dict.lookup, ↓reduceIte] at h2
    have hl1 : len = l1 := by
      simp only [Int.natCast_nonneg, ↓reduceIte, Int.toNat_natCast, Except.ok.injEq] at h2
      exact h2
    subst hl1
    exact resolveLengthAux_det _ _ _ _ _ _ _ _ _ h1 hr
  | _ =>
    rw [hm] at h1 h2
    simp only [Prod.mk.injEq] at h1 h2
    rw [h1.2] at h2
    exact Except.ok.inj h2

/-- A successful stream body called its resolver successfully, and parses the same way with
that constant length. -/
theorem parseStreamBodyWith_len {len : ObjParse.LengthResolver} {b : ByteArray} {p : Nat}
    {d : Dict} {x : Stream × Nat} (h : ObjParse.parseStreamBodyWith len b p d = .ok x) :
    ∃ l, len d p = .ok l ∧ ObjParse.parseStreamBodyWith (fun _ _ => .ok l) b p d = .ok x := by
  unfold ObjParse.parseStreamBodyWith at h ⊢
  rcases hs : ObjParse.streamDataStart b p with _ | s
  · rw [hs] at h; simp at h
  rw [hs] at h
  simp only at h ⊢
  rcases hl : len d p with e | l
  · rw [hl] at h; simp at h
  rw [hl] at h
  exact ⟨l, rfl, h⟩

/-- The stream body of a container parsed by `parseIndirectWith` at the offset where its head
parses (`parseContainerHead`). -/
theorem parseIndirectWith_container {lenF : Nat → ObjParse.LengthResolver} {limits : Limits}
    {b : ByteArray} {off c : Nat} {d : Dict} {p : Nat}
    (hh : Xref.Length.parseContainerHead limits b off c = .ok (d, p)) {io : IndirectObject}
    {r : Nat} (h : Xref.Length.parseIndirectWith lenF limits b off = .ok (io, r))
    {st : Stream} (hb : io.body = .stream st) :
    ∃ r', ObjParse.parseStreamBodyWith (lenF c) b p d = .ok (st, r') := by
  unfold Xref.Length.parseContainerHead at hh
  unfold Xref.Length.parseIndirectWith ObjParse.parseIndirectBodyWith at h
  split at hh
  · simp at hh
  · rename_i n' g' q hhd
    rw [hhd] at h
    simp only at h
    split at hh
    · rename_i hng
      split at hh
      · simp at hh
      · rename_i o1 r1 ho1
        rw [ho1] at h
        simp only at h
        split at hh
        · simp at hh
        · rename_i k r2 hk
          rw [hk] at h
          split at hh
          · rename_i hks
            subst hks
            simp only [show ObjParse.kwStream ≠ ObjParse.kwEndobj by decide, ↓reduceIte] at h
            cases o1 with
            | dict dd =>
              simp only [Except.ok.injEq, Prod.mk.injEq] at hh
              obtain ⟨rfl, rfl⟩ := hh
              simp only at h
              rcases hsb : ObjParse.parseStreamBodyWith (lenF n'.toNat) b r2 dd with e | ⟨s0, r3⟩
              · rw [hsb] at h; simp at h
              rw [hsb] at h
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, -⟩ := h
              simp only [IndirectBody.stream.injEq] at hb
              subst hb
              have hn : n'.toNat = c := by rw [hng.1]; simp
              rw [hn] at hsb
              exact ⟨r3, hsb⟩
            | _ => simp at hh
          · simp at hh
        · simp at hh
    · simp at hh

/-- A number whose object (any generation) fetches as a dictionary cannot take part in a
`/Length` resolution of the document (rules L4, L6 need an integer or a reference, and a
container needs a stream). -/
theorem notLen_of_dict {d : Open.OpenDoc} {limits : Limits} {m gk : Nat} {dd : Dict}
    (h : d.getObject limits m gk = .ok (.obj (.dict dd))) :
    NotLen d.pre d.lookup limits d.bytes m := by
  rcases hl : d.lookup m with _ | e
  · exact notLen_of_none hl
  rcases e with ⟨a0, b0⟩ | ⟨off, g⟩ | ⟨cc, idx⟩
  · unfold Open.OpenDoc.getObject Open.OpenDoc.getObjectTrace at h
    rw [hl] at h
    simp [Open.nullBody] at h
  · obtain ⟨o, hraw, hi, hr⟩ := getObject_inUse_dict h hl
    refine ⟨fun fuel vis g' c v hres => ?_, fun off' g'' hl' => ?_⟩
    · rw [Xref.Length.resolveLengthAux.eq_def] at hres
      by_cases hv : m ∈ vis
      · simp [hv] at hres
      simp only [hv, ↓reduceIte] at hres
      rcases fuel with _ | f
      · simp at hres
      simp only [hl] at hres
      by_cases hg : g = g'
      · simp only [hg, ↓reduceIte] at hres
        rcases hp : Xref.Length.parseLengthObj limits d.bytes off m g' with e | o'
        · rw [hp] at hres; simp at hres
        rw [hp] at hres
        have := parseLengthObj_raw hraw m g' hp
        subst this
        cases o' with
        | int i => exact hi i rfl
        | ref a c' => exact hr a c' rfl
        | _ => simp at hres
      · simp [hg] at hres
    · rw [hl] at hl'
      simp only [Option.some.injEq, XrefEntry.inUse.injEq] at hl'
      obtain ⟨rfl, -⟩ := hl'
      exact hraw.plain
  · refine ⟨fun fuel vis g' c v hres => ?_, fun off' g'' hl' => by rw [hl] at hl'; cases hl'⟩
    -- the fetch
    have hf := h
    unfold Open.OpenDoc.getObject Open.OpenDoc.getObjectTrace at hf
    rw [hl] at hf
    simp only at hf
    by_cases hg : gk = 0
    rotate_left
    · simp [hg, Open.nullBody] at hf
    simp only [hg, ↓reduceIte] at hf
    rcases hft : (Xref.ObjStm.fetchCompressedTrace d.pre d.lookup limits d.bytes d.objectCount
      m).result with e | o'
    · rw [hft] at hf; cases hf
    rw [hft] at hf
    simp only [Except.map, Except.ok.injEq, IndirectBody.obj.injEq] at hf
    subst hf
    -- the resolution
    rw [Xref.Length.resolveLengthAux.eq_def] at hres
    by_cases hv : m ∈ vis
    · simp [hv] at hres
    simp only [hv, ↓reduceIte] at hres
    rcases fuel with _ | f
    · simp at hres
    simp only [hl] at hres
    by_cases hc : cc = m ∨ cc ∈ vis
    · simp [hc] at hres
    simp only [hc, ↓reduceIte] at hres
    rcases hlc : d.lookup cc with _ | e2
    · rw [hlc] at hres; simp at hres
    rw [hlc] at hres
    rcases e2 with ⟨a0, b0⟩ | ⟨off, g2⟩ | ⟨c2, i2⟩
    · simp at hres
    rotate_left
    · simp at hres
    simp only at hres
    by_cases hg2 : g2 = 0
    rotate_left
    · simp [hg2] at hres
    simp only [hg2, ↓reduceIte] at hres
    rcases hph : Xref.Length.parseContainerHead limits d.bytes off cc with e | ⟨d1, p⟩
    · rw [hph] at hres; simp at hres
    rw [hph] at hres
    simp only at hres
    rcases hr1 : Xref.Length.containerLength
      (fun v r => Xref.Length.resolveLengthAux d.pre d.lookup limits d.bytes f v r)
      (cc :: m :: vis) d1 p with ⟨c1, e1⟩
    rw [hr1] at hres
    rcases e1 with e | l
    · simp [Xref.Length.containerMember] at hres
    rcases hcm : Xref.Length.containerMember d.pre limits d.bytes off cc m idx d1 p (.ok l)
      with e | o2
    · rw [hcm] at hres; simp at hres
    rw [hcm] at hres
    -- unfold the fetch to the same container
    unfold Xref.ObjStm.fetchCompressedTrace at hft
    rw [hl] at hft
    simp only at hft
    have hcm' : cc ≠ m := fun h' => hc (Or.inl h')
    simp only [hcm', ↓reduceIte, hlc, hg2] at hft
    rcases hpr : Xref.Length.parseIndirectResolved d.lookup limits d.bytes d.objectCount off
      d.pre with e | ⟨io, r⟩
    · rw [hpr] at hft; simp at hft
    rw [hpr] at hft
    simp only at hft
    by_cases hio : io.num = cc ∧ io.gen = 0
    rotate_left
    · simp [hio] at hft
    simp only [hio, and_self, ↓reduceIte] at hft
    rcases hbody : io.body with o0 | st0
    · rw [hbody] at hft; simp at hft
    rw [hbody] at hft
    simp only at hft
    rw [Xref.Length.parseIndirectResolved_eq_with] at hpr
    obtain ⟨r', hsb⟩ := parseIndirectWith_container hph hpr hbody
    obtain ⟨l1, hl1, hsb'⟩ := parseStreamBodyWith_len hsb
    have hll := containerLength_lengthOf hr1 hl1
    subst hll
    unfold Xref.Length.containerMember at hcm
    simp only at hcm
    rw [hsb'] at hcm
    simp only at hcm
    rcases hpre : d.pre.f cc st0 with e | st
    · rw [hpre] at hft; simp at hft
    rw [hpre] at hft hcm
    simp only at hft hcm
    rcases hdec : Xref.ObjStm.decodeObjStm limits st with e | os
    · rw [hdec] at hft; simp at hft
    rw [hdec] at hft hcm
    simp only at hft hcm
    by_cases hfo : Xref.ObjStm.findObject os m = some idx
    rotate_left
    · simp [hfo] at hft
    simp only [hfo, ↓reduceIte] at hft hcm
    rw [hft] at hcm
    cases hcm
    simp at hres

/-! ## The lookup of an opened document -/

open SafePdf.Core.Xref.Chain (Revision loadChain lookupEntry mergeChain)

/-- A binary-search hit is an entry of the array. -/
theorem bsearch_sound (a : Array (Nat × XrefEntry)) (n lo hi : Nat) {e : XrefEntry}
    (h : Open.bsearch a n lo hi = some e) : (n, e) ∈ a.toList := by
  rw [Open.bsearch.eq_def] at h
  split at h
  · split at h
    · cases h
    · rename_i k e' hm
      split at h
      · rename_i hk
        subst hk
        cases h
        rw [← Array.getElem?_toList] at hm
        exact List.mem_of_getElem? hm
      · split at h
        · exact bsearch_sound a n _ hi h
        · exact bsearch_sound a n lo _ h
  · cases h
termination_by hi - lo
decreasing_by all_goals omega

/-- **Binary search finds every entry** of an array with strictly ascending keys whose index
lies in the search range. -/
theorem bsearch_complete {a : Array (Nat × XrefEntry)}
    (hs : ∀ i j (hi : i < a.size) (hj : j < a.size), i < j → a[i].1 < a[j].1)
    {n : Nat} {e : XrefEntry} {i : Nat} (hi : i < a.size) (hai : a[i] = (n, e))
    (lo hi' : Nat) (h1 : lo ≤ i) (h2 : i < hi') (h3 : hi' ≤ a.size) :
    Open.bsearch a n lo hi' = some e := by
  rw [Open.bsearch.eq_def]
  have hlt : lo < hi' := by omega
  have hm : (lo + hi') / 2 < a.size := by omega
  simp only [hlt, ↓reduceIte, Array.getElem?_eq_getElem hm]
  have hlo : ∀ j (hj : j < a.size), j < i → a[j].1 < n := fun j hj hji => by
    have := hs j i hj hi hji
    rw [hai] at this
    exact this
  have hhi : ∀ j (hj : j < a.size), i < j → n < a[j].1 := fun j hj hji => by
    have := hs i j hi hj hji
    rw [hai] at this
    exact this
  have hlo' := hlo _ hm
  have hhi' := hhi _ hm
  rcases hmid : a[(lo + hi') / 2] with ⟨k, e'⟩
  rw [hmid] at hlo' hhi'
  simp only at hlo' hhi' ⊢
  by_cases hk : k = n
  · simp only [hk, ↓reduceIte]
    have hmi : (lo + hi') / 2 = i := by
      rcases Nat.lt_trichotomy ((lo + hi') / 2) i with h | h | h
      · have := hlo' h; omega
      · exact h
      · have := hhi' h; omega
    have : a[(lo + hi') / 2] = a[i] := by simp only [hmi]
    rw [hmid, hai] at this
    simp only [Prod.mk.injEq] at this
    rw [this.2]
  · simp only [hk, ↓reduceIte]
    by_cases hkn : k < n
    · simp only [hkn, ↓reduceIte]
      have : (lo + hi') / 2 < i := by
        rcases Nat.lt_trichotomy ((lo + hi') / 2) i with h | h | h
        · exact h
        · have : a[(lo + hi') / 2] = a[i] := by simp only [h]
          rw [hmid, hai] at this
          simp only [Prod.mk.injEq] at this
          exact absurd this.1 hk
        · have := hhi' h; omega
      exact bsearch_complete hs hi hai _ _ (by omega) h2 h3
    · simp only [hkn, ↓reduceIte]
      have : i < (lo + hi') / 2 := by
        rcases Nat.lt_trichotomy ((lo + hi') / 2) i with h | h | h
        · have := hlo' h; omega
        · have : a[(lo + hi') / 2] = a[i] := by simp only [h]
          rw [hmid, hai] at this
          simp only [Prod.mk.injEq] at this
          exact absurd this.1 hk
        · exact h
      exact bsearch_complete hs hi hai _ _ h1 this (by omega)
termination_by hi' - lo
decreasing_by all_goals omega

/-- **The lookup of an opened document is the entry of its section** (rule G1: the binary
search over the sorted index finds exactly `lookupEntry`). -/
theorem lookup_eq (d : Open.OpenDoc) (m : Nat) : d.lookup m = lookupEntry m d.xref.entries := by
  have hsorted : ∀ i j (hi : i < d.index.size) (hj : j < d.index.size), i < j →
      d.index[i].1 < d.index[j].1 := by
    intro i j hi hj hij
    have := List.pairwise_iff_getElem.mp d.xref.sorted i j
      (by have h := d.index_eq; rw [h] at hi; simpa using hi)
      (by have h := d.index_eq; rw [h] at hj; simpa using hj) hij
    simp only [d.index_eq, List.getElem_toArray]
    exact this
  have hnd := d.xref.keys_nodup
  rcases hl : lookupEntry m d.xref.entries with _ | e
  · rcases hb : d.lookup m with _ | e
    · rfl
    · exfalso
      unfold Open.OpenDoc.lookup at hb
      have := bsearch_sound _ _ _ _ hb
      rw [d.index_eq, List.toList_toArray] at this
      rw [(Unambiguous.lookupEntry_eq_some_iff hnd).mpr this] at hl
      cases hl
  · have hmem := (Unambiguous.lookupEntry_eq_some_iff hnd).mp hl
    obtain ⟨i, hi, hie⟩ := List.mem_iff_getElem.mp hmem
    have hi' : i < d.index.size := by rw [d.index_eq]; simpa using hi
    have hai : d.index[i] = (m, e) := by
      simp only [d.index_eq, List.getElem_toArray]
      exact hie
    exact bsearch_complete hsorted hi' hai 0 d.index.size (Nat.zero_le _) hi' (Nat.le_refl _)

/-- The fuel of an opened document is the number of its entries. -/
theorem objectCount_eq (d : Open.OpenDoc) : d.objectCount = d.xref.entries.length := by
  unfold Open.OpenDoc.objectCount
  rw [d.index_eq]
  simp

/-- A document opened strictly: the merged chain with the newest trailer, the input bytes,
and the decryption state of `withCrypt` (rules P1, E1). -/
theorem openFile_shape {limits : Limits} {bytes : ByteArray} {d : Open.OpenDoc}
    (h : Open.openFile limits bytes = .ok d) (hr : d.repaired = false) :
    ∃ revs sec tr off rest, loadChain limits bytes = .ok revs ∧ revs = (sec, tr, off) :: rest ∧
      (Open.OpenDoc.mk' bytes (mergeChain revs) tr revs.length false).withCrypt limits = .ok d := by
  unfold Open.openFile at h
  split at h
  · rename_i d0 hs
    cases h
    obtain ⟨revs, hl, -, hc, -⟩ := Open.strictOpen_ok hs
    unfold Open.ofChain at hc
    split at hc
    · cases hc
    · rename_i sec tr off rest
      exact ⟨_, sec, tr, off, rest, hl, rfl, hc⟩
  · split at h
    · cases h
    · split at h
      · cases h
        rename_i d1 hrep
        rw [Open.repairOpen_repaired hrep] at hr
        cases hr
      · cases h

/-- The fields of a document built by `withCrypt` from `mk'`. -/
theorem withCrypt_mk' {limits : Limits} {bytes : ByteArray} {sec : Xref.XrefSection}
    {tr : Xref.Trailer} {k : Nat} {d : Open.OpenDoc}
    (h : (Open.OpenDoc.mk' bytes sec tr k false).withCrypt limits = .ok d) :
    d.bytes = bytes ∧ d.xref = sec ∧ d.trailer = tr := by
  obtain ⟨c, rfl⟩ := Open.withCrypt_ok h
  exact ⟨rfl, rfl, rfl⟩

/-! ## The decryption state -/

/-- A decryption state set at open comes from the encryption dictionary and `Crypt.setup`
(rule E1). -/
theorem withCrypt_some {limits : Limits} {d0 d : Open.OpenDoc} (h0 : d0.crypt = none)
    (h : d0.withCrypt limits = .ok d) {st : Crypt.State} (hc : d.crypt = some st) :
    ∃ enc ref, d0.encryptDict limits = .ok (enc, ref) ∧
      Crypt.setup enc d0.trailer.dict ref = .ok st := by
  unfold Open.OpenDoc.withCrypt at h
  split at h
  · split at h
    · cases h
    · rename_i enc ref he
      split at h
      · cases h
      · rename_i st0 hst
        cases h
        simp only [Option.some.injEq] at hc
        subst hc
        exact ⟨enc, ref, he, hst⟩
  · cases h
    rw [h0] at hc
    cases hc

/-- `Crypt.setup` records the reference it is given. -/
theorem setup_encRef {enc t : Dict} {ref : Option (Nat × Nat)} {st : Crypt.State}
    (h : Crypt.setup enc t ref = .ok st) : st.encRef = ref := by
  unfold Crypt.setup at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h; rfl

/-- **The state is determined by the encryption dictionary and the file key**: two
`Crypt.setup` runs on the same encryption dictionary and reference that derive the same key
bytes (from possibly different trailers) give the same state. -/
theorem setup_eq {enc t1 t2 : Dict} {ref : Option (Nat × Nat)} {s1 s2 : Crypt.State}
    (h1 : Crypt.setup enc t1 ref = .ok s1) (h2 : Crypt.setup enc t2 ref = .ok s2)
    (hk : s1.fileKey.data = s2.fileKey.data) : s1 = s2 := by
  unfold Crypt.setup at h1 h2
  split at h1
  · cases h1
  · rename_i hd hh
    rw [hh] at h2
    simp only at h2
    split at h1
    · cases h1
    · split at h2
      · cases h2
      · cases h1
        cases h2
        simp only at hk
        have hk' : ∀ a b : ByteArray, a.data = b.data → a = b := fun a b h => by
          cases a; cases b; simp only at h; rw [h]
        rw [hk' _ _ hk]

/-- An indirect encryption dictionary: the trailer refers to it, it is not in an object
stream, and it fetches as a dictionary (rule E1). -/
theorem encryptDict_ref {limits : Limits} {d : Open.OpenDoc} {enc : Dict} {r : Nat × Nat}
    (h : d.encryptDict limits = .ok (enc, some r)) :
    (∀ c i, d.lookup r.1 ≠ some (.compressed c i)) ∧
      d.getObject limits r.1 r.2 = .ok (.obj (.dict enc)) := by
  unfold Open.OpenDoc.encryptDict at h
  split at h
  · cases h
  · rename_i n g _
    split at h
    · cases h
    · rename_i hnc
      split at h
      · rename_i e he
        cases h
        exact ⟨fun c i hc => hnc c i hc, he⟩
      · cases h
      · cases h
  · cases h

/-- A dictionary fetched from a number that is not in an object stream is in use. -/
theorem inUse_of_dict {limits : Limits} {d : Open.OpenDoc} {n g : Nat} {dd : Dict}
    (h : d.getObject limits n g = .ok (.obj (.dict dd)))
    (hnc : ∀ c i, d.lookup n ≠ some (.compressed c i)) :
    ∃ off g', d.lookup n = some (.inUse off g') := by
  unfold Open.OpenDoc.getObject Open.OpenDoc.getObjectTrace at h
  rcases hl : d.lookup n with _ | e
  · rw [hl] at h; simp [Open.nullBody] at h
  rcases e with ⟨a, b⟩ | ⟨off, g'⟩ | ⟨c, i⟩
  · rw [hl] at h; simp [Open.nullBody] at h
  · exact ⟨off, g', rfl⟩
  · exact absurd hl (hnc c i)

/-- **The decryption state survives an update that leaves the encryption dictionary alone**:
two strictly built documents, the second over an extension of the first's bytes (a file with
an end), whose states agree on the key bytes and name the same indirect encryption
dictionary `r`, whose entry is the same in both sections, have the same state. -/
theorem crypt_eq_of_ref {limits : Limits} {bytes out : ByteArray} {sec sec' : Xref.XrefSection}
    {tr tr' : Xref.Trailer} {k k' : Nat} {d d' : Open.OpenDoc}
    (hw : (Open.OpenDoc.mk' bytes sec tr k false).withCrypt limits = .ok d)
    (hw' : (Open.OpenDoc.mk' out sec' tr' k' false).withCrypt limits = .ok d')
    (hE : Extends bytes out) (hs : HasEnd bytes) {st st' : Crypt.State} {r : Nat × Nat}
    (hc : d.crypt = some st) (hc' : d'.crypt = some st') (hr : st.encRef = some r)
    (hr' : st'.encRef = some r) (hkey : st.fileKey.data = st'.fileKey.data)
    (hl : lookupEntry r.1 sec'.entries = lookupEntry r.1 sec.entries) : st' = st := by
  obtain ⟨enc, ref, he, hst⟩ := withCrypt_some rfl hw hc
  obtain ⟨enc', ref', he', hst'⟩ := withCrypt_some rfl hw' hc'
  have h1 := setup_encRef hst
  have h2 := setup_encRef hst'
  rw [hr] at h1
  rw [hr'] at h2
  subst h1 h2
  obtain ⟨hnc, hg⟩ := encryptDict_ref he
  obtain ⟨-, hg'⟩ := encryptDict_ref he'
  obtain ⟨off, g', hin⟩ := inUse_of_dict hg hnc
  have hl' : (Open.OpenDoc.mk' out sec' tr' k' false).lookup r.1 =
      (Open.OpenDoc.mk' bytes sec tr k false).lookup r.1 := by
    rw [lookup_eq, lookup_eq]
    exact hl
  have := getObject_transfer_obj (d := Open.OpenDoc.mk' bytes sec tr k false)
    (d' := Open.OpenDoc.mk' out sec' tr' k' false) hE hs rfl rfl hl' hin hg
  rw [hg'] at this
  simp only [Except.ok.injEq, IndirectBody.obj.injEq, PdfObject.dict.injEq] at this
  subst this
  exact (setup_eq hst hst' hkey).symm

/-! ## One more revision in front -/

/-- Lookup in a chain with one more (newest) revision: its entry, else the old one. -/
theorem mergeChain_cons_lookup (m : Nat) (r : Revision) (revs : List Revision) :
    lookupEntry m (mergeChain (r :: revs)).entries =
      (lookupEntry m r.1.entries).or (lookupEntry m (mergeChain revs).entries) := by
  rw [XrefTerm.mergeChain_lookup, XrefTerm.mergeChain_lookup, List.findSome?_cons]
  cases lookupEntry m r.1.entries <;> rfl

/-- A number the new revision does not list resolves as before. -/
theorem mergeChain_cons_lookup_none {m : Nat} {r : Revision} {revs : List Revision}
    (h : m ∉ r.1.entries.map Prod.fst) :
    lookupEntry m (mergeChain (r :: revs)).entries = lookupEntry m (mergeChain revs).entries := by
  rw [mergeChain_cons_lookup, (Unambiguous.lookupEntry_eq_none_iff).mpr h]
  rfl

/-- One more revision never loses an entry: the merged section only grows. -/
theorem mergeChain_cons_length (r : Revision) (revs : List Revision) :
    (mergeChain revs).entries.length ≤ (mergeChain (r :: revs)).entries.length := by
  have hnd := Unambiguous.mergeChain_keys_nodup revs
  have hsub : (mergeChain revs).entries.map Prod.fst ⊆
      (mergeChain (r :: revs)).entries.map Prod.fst := by
    intro k hk
    obtain ⟨⟨k', e⟩, he, rfl⟩ := List.mem_map.mp hk
    have h1 := Unambiguous.lookupEntry_mergeChain_iff.mpr he
    have h2 : ∃ e', lookupEntry k' (mergeChain (r :: revs)).entries = some e' := by
      rw [mergeChain_cons_lookup, h1]
      cases lookupEntry k' r.1.entries with
      | none => exact ⟨e, rfl⟩
      | some e' => exact ⟨e', rfl⟩
    obtain ⟨e', h2⟩ := h2
    exact List.mem_map.mpr ⟨(k', e'), Unambiguous.lookupEntry_mergeChain_iff.mp h2, rfl⟩
  have := hnd.length_le_of_subset hsub
  simpa using this

end SafePdf.Spec.WritePrefix
