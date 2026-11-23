import SafePdf.Core.Token

/-!
# Object grammar spec (Plan.md §5.1, §4 S6/C5, §6 Phase 1, task 1.4; ISO 32000-2 §7.3)

The denotational grammar of *direct* objects over tokens (Plan.md §5.1's
`ObjSpec : List Token → PdfObject → Prop`), an executable spec `parse`, and the facts later
tasks rely on: `parse` agrees with the grammar (`parse_eq_ok_iff`), the grammar is
unambiguous (S6, `Parses.unique`), results respect the depth bound (`Parses.depth_le`),
parsing consumes input (`Parses.length_lt`) and yields canonical objects from canonical
tokens (`Parses.canonical`). The efficient parser `SafePdf.Core.ObjParse` (task 1.5) is
proven equal to `parse` in task 1.8; the printer round-trip (task 1.7) is stated against
`Parses`/`parse`.

## Grammar (with nesting fuel `F`)

* G1. `int n, int g, keyword "R"` is the reference `n g R` (ISO 32000-2 §7.3.10), provided
  `1 ≤ n` and `0 ≤ g ≤ 65535`; if the three tokens are present but the range check fails it
  is an error (`badRef`). Otherwise `int n` alone is an integer, the rest left unconsumed.
* G2. `real d` → real; literal and hex strings → string; `name n` → name.
* G3. Keywords `true`, `false`, `null` → booleans / null; any other keyword is an error, as is
  `{`, `}`, `]` or `>>` where an object is expected.
* G4. `[` needs fuel `f + 1` (fuel `0` is `depthLimit`); then objects parsed with fuel `f`
  until `]`.
* G5. `<<` needs fuel `f + 1`; then (`name k`, object with fuel `f`) pairs until `>>`, in
  source order. A non-name key is an error; a key repeated in the same dictionary is an
  error (strict path rejects duplicates).
* G6. End of tokens where an object, `]` or `>>` is expected is an error.

Hence a parse with fuel `F` succeeds only on objects of `depth ≤ F` (scalars have depth 0).

## Shape

`Parses`, `ParsesItems`, `ParsesEntries` are mutually inductive relations
`fuel → input → result → rest`. The dictionary rule asks for distinct keys globally
(`(Dict.keys es).Nodup`), the most direct reading of G5.

`parse`/`parseItems`/`parseEntries` are mutually well-founded on the input length.
`parseItems`/`parseEntries` re-check that the element parse consumed input before looping
(`if _h : r.length < …`); that branch is dead (`Parses.length_lt`) and only serves
termination. `parseEntries` keeps the keys seen so far and rejects a repeat at the key,
as G5 says.
-/

namespace SafePdf.Spec.Object

/-! ## Errors and keywords -/

/-- What went wrong while parsing an object. Spec-side errors carry no offsets (tokens have
none); task 1.8 compares only "is an error" on failures. -/
inductive Err where
  /-- `n g R` with `n < 1` or `g ∉ [0, 65535]`. -/
  | badRef
  /-- A keyword other than `true`, `false`, `null` where an object is expected. -/
  | unexpectedKeyword
  /-- `{`, `}`, `]` or `>>` where an object is expected. -/
  | unexpectedToken
  /-- `[` or `<<` with no nesting fuel left. -/
  | depthLimit
  /-- End of tokens where an object, `]` or `>>` is expected. -/
  | unexpectedEnd
  /-- A dictionary key that is not a name. -/
  | nonNameKey
  /-- A dictionary key equal to an earlier key of the same dictionary. -/
  | duplicateKey
  deriving Repr, DecidableEq, Inhabited

/-- The bytes of the keyword `R` (indirect reference, ISO 32000-2 §7.3.10). -/
def kwR : List UInt8 := [82]
/-- The bytes of the keyword `true`. -/
def kwTrue : List UInt8 := [116, 114, 117, 101]
/-- The bytes of the keyword `false`. -/
def kwFalse : List UInt8 := [102, 97, 108, 115, 101]
/-- The bytes of the keyword `null`. -/
def kwNull : List UInt8 := [110, 117, 108, 108]

/-- Whether an `(n, g)` pair is a valid reference: `1 ≤ n`, `0 ≤ g ≤ 65535`. -/
def RefOk (n g : Int) : Prop := 1 ≤ n ∧ 0 ≤ g ∧ g ≤ 65535

instance (n g : Int) : Decidable (RefOk n g) := inferInstanceAs (Decidable (_ ∧ _))

/-! ## The grammar (relation) -/

mutual
/-- `Parses fuel ts o rest`: with nesting fuel `fuel`, the token list `ts` starts with a
direct object denoting `o`, followed by `rest`. -/
inductive Parses : Nat → List Token → PdfObject → List Token → Prop
  /-- G1: `n g R` with a valid object and generation number. -/
  | ref {fuel : Nat} {n g : Int} {rest : List Token} :
      RefOk n g →
      Parses fuel (.int n :: .int g :: .keyword kwR :: rest) (.ref n.toNat g.toNat) rest
  /-- G1: an integer not followed by `g R`. -/
  | int {fuel : Nat} {n : Int} {ts : List Token} :
      (¬ ∃ g rest, ts = .int g :: .keyword kwR :: rest) →
      Parses fuel (.int n :: ts) (.int n) ts
  /-- G2: a real. -/
  | real {fuel : Nat} {d : Decimal} {ts : List Token} :
      Parses fuel (.real d :: ts) (.real d) ts
  /-- G2: a literal string. -/
  | litString {fuel : Nat} {s : List UInt8} {ts : List Token} :
      Parses fuel (.litString s :: ts) (.string s) ts
  /-- G2: a hexadecimal string. -/
  | hexString {fuel : Nat} {s : List UInt8} {ts : List Token} :
      Parses fuel (.hexString s :: ts) (.string s) ts
  /-- G2: a name. -/
  | name {fuel : Nat} {k : Name} {ts : List Token} :
      Parses fuel (.name k :: ts) (.name k) ts
  /-- G3: `true`. -/
  | true_ {fuel : Nat} {ts : List Token} :
      Parses fuel (.keyword kwTrue :: ts) (.bool true) ts
  /-- G3: `false`. -/
  | false_ {fuel : Nat} {ts : List Token} :
      Parses fuel (.keyword kwFalse :: ts) (.bool false) ts
  /-- G3: `null`. -/
  | null {fuel : Nat} {ts : List Token} :
      Parses fuel (.keyword kwNull :: ts) .null ts
  /-- G4: an array, its items parsed with one less unit of fuel. -/
  | array {f : Nat} {ts : List Token} {items : List PdfObject} {rest : List Token} :
      ParsesItems f ts items rest →
      Parses (f + 1) (.arrayOpen :: ts) (.array items) rest
  /-- G5: a dictionary with distinct keys, its values parsed with one less unit of fuel. -/
  | dict {f : Nat} {ts : List Token} {es : List (Name × PdfObject)} {rest : List Token} :
      ParsesEntries f ts es rest → (Dict.keys es).Nodup →
      Parses (f + 1) (.dictOpen :: ts) (.dict es) rest

/-- `ParsesItems fuel ts items rest`: array items, each parsed with `fuel`, then `]`. -/
inductive ParsesItems : Nat → List Token → List PdfObject → List Token → Prop
  /-- The closing `]`. -/
  | nil {fuel : Nat} {rest : List Token} :
      ParsesItems fuel (.arrayClose :: rest) [] rest
  /-- One more item. -/
  | cons {fuel : Nat} {ts mid rest : List Token} {o : PdfObject} {os : List PdfObject} :
      Parses fuel ts o mid → ParsesItems fuel mid os rest →
      ParsesItems fuel ts (o :: os) rest

/-- `ParsesEntries fuel ts es rest`: dictionary entries `name value`, values parsed with
`fuel`, then `>>`. Key distinctness is imposed by `Parses.dict`. -/
inductive ParsesEntries : Nat → List Token → List (Name × PdfObject) → List Token → Prop
  /-- The closing `>>`. -/
  | nil {fuel : Nat} {rest : List Token} :
      ParsesEntries fuel (.dictClose :: rest) [] rest
  /-- One more entry. -/
  | cons {fuel : Nat} {k : Name} {ts mid rest : List Token} {v : PdfObject}
      {es : List (Name × PdfObject)} :
      Parses fuel ts v mid → ParsesEntries fuel mid es rest →
      ParsesEntries fuel (.name k :: ts) ((k, v) :: es) rest
end

/-! ## The executable spec -/

/-- G1: an integer `n` followed by `ts`: a reference if `ts` starts with `g R`, else the
integer itself. -/
def parseIntOrRef (n : Int) : List Token → Except Err (PdfObject × List Token)
  | .int g :: .keyword kw :: rest =>
    if kw = kwR then
      if RefOk n g then .ok (.ref n.toNat g.toNat, rest) else .error .badRef
    else .ok (.int n, .int g :: .keyword kw :: rest)
  | ts => .ok (.int n, ts)

/-- G3: the object a keyword denotes, if any. -/
def keywordObj (kw : List UInt8) : Option PdfObject :=
  if kw = kwTrue then some (.bool true)
  else if kw = kwFalse then some (.bool false)
  else if kw = kwNull then some .null
  else none

mutual
/-- Parse one direct object from the front of `ts` with nesting fuel `fuel`, returning the
object and the remaining tokens. -/
def parse (fuel : Nat) (ts : List Token) : Except Err (PdfObject × List Token) :=
  match ts with
  | [] => .error .unexpectedEnd
  | .int n :: rest => parseIntOrRef n rest
  | .real d :: rest => .ok (.real d, rest)
  | .litString s :: rest => .ok (.string s, rest)
  | .hexString s :: rest => .ok (.string s, rest)
  | .name k :: rest => .ok (.name k, rest)
  | .keyword kw :: rest =>
    match keywordObj kw with
    | some o => .ok (o, rest)
    | none => .error .unexpectedKeyword
  | .arrayOpen :: rest =>
    match fuel with
    | 0 => .error .depthLimit
    | f + 1 =>
      match parseItems f rest with
      | .ok (items, r) => .ok (.array items, r)
      | .error e => .error e
  | .dictOpen :: rest =>
    match fuel with
    | 0 => .error .depthLimit
    | f + 1 =>
      match parseEntries f [] rest with
      | .ok (es, r) => .ok (.dict es, r)
      | .error e => .error e
  | .arrayClose :: _ => .error .unexpectedToken
  | .dictClose :: _ => .error .unexpectedToken
  | .braceOpen :: _ => .error .unexpectedToken
  | .braceClose :: _ => .error .unexpectedToken
termination_by (ts.length, 0)

/-- Parse array items with fuel `fuel` up to and including the closing `]`. -/
def parseItems (fuel : Nat) (ts : List Token) : Except Err (List PdfObject × List Token) :=
  match ts with
  | [] => .error .unexpectedEnd
  | .arrayClose :: rest => .ok ([], rest)
  | t :: rest =>
    match parse fuel (t :: rest) with
    | .error e => .error e
    | .ok (o, r) =>
      if _h : r.length < rest.length + 1 then
        match parseItems fuel r with
        | .ok (os, r') => .ok (o :: os, r')
        | .error e => .error e
      else .error .unexpectedToken
termination_by (ts.length, 1)

/-- Parse dictionary entries with fuel `fuel` up to and including the closing `>>`;
`seen` holds the keys already read in this dictionary. -/
def parseEntries (fuel : Nat) (seen : List Name) (ts : List Token) :
    Except Err (List (Name × PdfObject) × List Token) :=
  match ts with
  | [] => .error .unexpectedEnd
  | .dictClose :: rest => .ok ([], rest)
  | .name k :: rest =>
    if k ∈ seen then .error .duplicateKey
    else
      match parse fuel rest with
      | .error e => .error e
      | .ok (v, r) =>
        if _h : r.length < rest.length then
          match parseEntries fuel (k :: seen) r with
          | .ok (es, r') => .ok ((k, v) :: es, r')
          | .error e => .error e
        else .error .unexpectedToken
  | _ :: _ => .error .nonNameKey
termination_by (ts.length, 1)
end

/-! ## Basic lemmas -/

/-- `Dict.keys` of a cons. -/
theorem keys_cons (k : Name) (v : PdfObject) (es : List (Name × PdfObject)) :
    Dict.keys ((k, v) :: es) = k :: Dict.keys es := rfl

/-- `keywordObj` succeeds exactly on `true`, `false`, `null`, and the grammar agrees. -/
theorem keywordObj_sound {fuel : Nat} {kw : List UInt8} {o : PdfObject} {ts : List Token}
    (h : keywordObj kw = some o) : Parses fuel (.keyword kw :: ts) o ts := by
  unfold keywordObj at h
  by_cases h1 : kw = kwTrue
  · subst h1; simp at h; subst h; exact .true_
  · by_cases h2 : kw = kwFalse
    · subst h2; simp [h1] at h; subst h; exact .false_
    · by_cases h3 : kw = kwNull
      · subst h3; simp [h1, h2] at h; subst h; exact .null
      · simp [h1, h2, h3] at h

/-- Soundness of `parseIntOrRef` (G1). -/
theorem parseIntOrRef_sound {fuel : Nat} {n : Int} {ts : List Token} {o : PdfObject}
    {r : List Token} (h : parseIntOrRef n ts = .ok (o, r)) : Parses fuel (.int n :: ts) o r := by
  unfold parseIntOrRef at h
  split at h
  · rename_i g kw rest
    by_cases hk : kw = kwR
    · subst hk
      by_cases hr : RefOk n g
      · simp [hr] at h; obtain ⟨rfl, rfl⟩ := h; exact .ref hr
      · simp [hr] at h
    · simp [hk] at h; obtain ⟨rfl, rfl⟩ := h
      exact .int (by rintro ⟨g', rest', he⟩; simp at he; exact hk he.2.1)
  · rename_i ts' hnot
    simp at h; obtain ⟨rfl, rfl⟩ := h
    exact .int (by rintro ⟨g, rest, rfl⟩; exact hnot g kwR rest rfl)

/-- `parseIntOrRef` on an integer not followed by `g R` (G1). -/
theorem parseIntOrRef_int {n : Int} {ts : List Token}
    (hnot : ¬ ∃ g rest, ts = .int g :: .keyword kwR :: rest) :
    parseIntOrRef n ts = .ok (.int n, ts) := by
  unfold parseIntOrRef
  split
  · rename_i g kw rest
    have hk : kw ≠ kwR := fun hk => hnot ⟨g, rest, by subst hk; rfl⟩
    simp [hk]
  · rfl

/-! ## Soundness of `parse` -/

/-- Soundness of the three executable functions for inputs of length at most `n`. -/
theorem sound_aux (n : Nat) : ∀ ts : List Token, ts.length ≤ n →
    (∀ f o r, parse f ts = .ok (o, r) → Parses f ts o r) ∧
    (∀ f os r, parseItems f ts = .ok (os, r) → ParsesItems f ts os r) ∧
    (∀ f seen es r, parseEntries f seen ts = .ok (es, r) →
      ParsesEntries f ts es r ∧ (Dict.keys es).Nodup ∧ ∀ k ∈ Dict.keys es, k ∉ seen) := by
  induction n with
  | zero =>
    intro ts hl
    rcases ts with _ | ⟨t, rest⟩
    · exact ⟨by simp [parse], by simp [parseItems], by simp [parseEntries]⟩
    · simp at hl
  | succ n ih =>
    intro ts hl
    have hp : ∀ f o r, parse f ts = .ok (o, r) → Parses f ts o r := by
      intro f o r h
      rcases ts with _ | ⟨t, rest⟩
      · simp [parse] at h
      have hrl : rest.length ≤ n := by simp at hl; omega
      cases t with
      | int i => simp only [parse] at h; exact parseIntOrRef_sound h
      | real d => simp [parse] at h; obtain ⟨rfl, rfl⟩ := h; exact .real
      | litString s => simp [parse] at h; obtain ⟨rfl, rfl⟩ := h; exact .litString
      | hexString s => simp [parse] at h; obtain ⟨rfl, rfl⟩ := h; exact .hexString
      | name k => simp [parse] at h; obtain ⟨rfl, rfl⟩ := h; exact .name
      | keyword kw =>
        simp only [parse] at h
        cases hk : keywordObj kw with
        | none => simp [hk] at h
        | some o' => simp [hk] at h; obtain ⟨rfl, rfl⟩ := h; exact keywordObj_sound hk
      | arrayOpen =>
        cases f with
        | zero => simp [parse] at h
        | succ f =>
          simp only [parse] at h
          cases hi : parseItems f rest with
          | error e => simp [hi] at h
          | ok p =>
            obtain ⟨items, r'⟩ := p
            simp [hi] at h; obtain ⟨rfl, rfl⟩ := h
            exact .array ((ih rest hrl).2.1 f items r' hi)
      | dictOpen =>
        cases f with
        | zero => simp [parse] at h
        | succ f =>
          simp only [parse] at h
          cases he : parseEntries f [] rest with
          | error e => simp [he] at h
          | ok p =>
            obtain ⟨es, r'⟩ := p
            simp [he] at h; obtain ⟨rfl, rfl⟩ := h
            obtain ⟨h1, h2, -⟩ := (ih rest hrl).2.2 f [] es r' he
            exact .dict h1 h2
      | arrayClose => simp [parse] at h
      | dictClose => simp [parse] at h
      | braceOpen => simp [parse] at h
      | braceClose => simp [parse] at h
    have hi : ∀ f os r, parseItems f ts = .ok (os, r) → ParsesItems f ts os r := by
      intro f os r h
      rcases ts with _ | ⟨t, rest⟩
      · simp [parseItems] at h
      by_cases ht : t = .arrayClose
      · subst ht; simp [parseItems] at h; obtain ⟨rfl, rfl⟩ := h; exact .nil
      · rw [parseItems] at h
        rotate_left
        · exact ht
        cases hpo : parse f (t :: rest) with
        | error e => simp [hpo] at h
        | ok p =>
          obtain ⟨o, mid⟩ := p
          simp only [hpo] at h
          by_cases hlt : mid.length < rest.length + 1
          · simp only [hlt, ↓reduceDIte] at h
            cases hit : parseItems f mid with
            | error e => simp [hit] at h
            | ok q =>
              obtain ⟨os', r'⟩ := q
              simp [hit] at h; obtain ⟨rfl, rfl⟩ := h
              exact .cons (hp f o mid hpo)
                ((ih mid (by simp at hl; omega)).2.1 f os' r' hit)
          · simp [hlt] at h
    have he : ∀ f seen es r, parseEntries f seen ts = .ok (es, r) →
        ParsesEntries f ts es r ∧ (Dict.keys es).Nodup ∧ ∀ k ∈ Dict.keys es, k ∉ seen := by
      intro f seen es r h
      rcases ts with _ | ⟨t, rest⟩
      · simp [parseEntries] at h
      have hrl : rest.length ≤ n := by simp at hl; omega
      cases t with
      | dictClose =>
        simp [parseEntries] at h; obtain ⟨rfl, rfl⟩ := h
        exact ⟨.nil, by simp [Dict.keys], by simp [Dict.keys]⟩
      | name k =>
        simp only [parseEntries] at h
        by_cases hk : k ∈ seen
        · simp [hk] at h
        · simp only [hk, ↓reduceIte] at h
          cases hpo : parse f rest with
          | error e => simp [hpo] at h
          | ok p =>
            obtain ⟨v, mid⟩ := p
            simp only [hpo] at h
            by_cases hlt : mid.length < rest.length
            · simp only [hlt, ↓reduceDIte] at h
              cases hit : parseEntries f (k :: seen) mid with
              | error e => simp [hit] at h
              | ok q =>
                obtain ⟨es', r'⟩ := q
                simp [hit] at h; obtain ⟨rfl, rfl⟩ := h
                obtain ⟨h1, h2, h3⟩ := (ih mid (by omega)).2.2 f (k :: seen) es' r' hit
                have hkn : k ∉ Dict.keys es' := fun hm => h3 k hm (by simp)
                refine ⟨.cons ((ih rest hrl).1 f v mid hpo) h1, ?_, ?_⟩
                · rw [keys_cons]; exact List.nodup_cons.mpr ⟨hkn, h2⟩
                · intro x hx
                  rw [keys_cons, List.mem_cons] at hx
                  rcases hx with rfl | hx
                  · exact hk
                  · exact fun hs => h3 x hx (List.mem_cons_of_mem _ hs)
            · simp [hlt] at h
      | int _ | real _ | litString _ | hexString _ | keyword _ | arrayOpen | arrayClose
      | dictOpen | braceOpen | braceClose => simp [parseEntries] at h
    exact ⟨hp, hi, he⟩

/-- Soundness: whatever `parse` returns is derivable in the grammar. -/
theorem parse_sound {fuel : Nat} {ts : List Token} {o : PdfObject} {r : List Token}
    (h : parse fuel ts = .ok (o, r)) : Parses fuel ts o r :=
  (sound_aux ts.length ts (Nat.le_refl _)).1 fuel o r h

/-! ## Facts about derivations -/

/-- A derivation starts with a token that can begin an object (not `]`, not `>>`). -/
theorem Parses.head {fuel : Nat} {ts : List Token} {o : PdfObject} {r : List Token}
    (h : Parses fuel ts o r) :
    ∃ t rest, ts = t :: rest ∧ t ≠ .arrayClose ∧ t ≠ .dictClose := by
  cases h <;> exact ⟨_, _, rfl, by simp, by simp⟩

mutual
/-- Consumption: an object derivation consumes at least one token. -/
theorem Parses.length_lt {fuel : Nat} {ts : List Token} {o : PdfObject} {r : List Token} :
    Parses fuel ts o r → r.length < ts.length
  | .ref _ => by simp; omega
  | .int _ | .real | .litString | .hexString | .name | .true_ | .false_ | .null => by simp
  | .array hi => by have := hi.length_lt; simp; omega
  | .dict he _ => by have := he.length_lt; simp; omega

/-- Consumption for array items (including the closing `]`). -/
theorem ParsesItems.length_lt {fuel : Nat} {ts : List Token} {os : List PdfObject}
    {r : List Token} : ParsesItems fuel ts os r → r.length < ts.length
  | .nil => by simp
  | .cons hp hi => by have := hp.length_lt; have := hi.length_lt; omega

/-- Consumption for dictionary entries (including the closing `>>`). -/
theorem ParsesEntries.length_lt {fuel : Nat} {ts : List Token}
    {es : List (Name × PdfObject)} {r : List Token} :
    ParsesEntries fuel ts es r → r.length < ts.length
  | .nil => by simp
  | .cons hp he => by have := hp.length_lt; have := he.length_lt; simp; omega
end

mutual
/-- The remaining tokens are a suffix of the input: every token of `r` occurs in `ts`. -/
theorem Parses.mem_of_mem_rest {fuel : Nat} {ts : List Token} {o : PdfObject}
    {r : List Token} : Parses fuel ts o r → ∀ t ∈ r, t ∈ ts
  | .ref _ => by intro t ht; simp [ht]
  | .int _ | .real | .litString | .hexString | .name | .true_ | .false_ | .null => by
    intro t ht; simp [ht]
  | .array hi => by intro t ht; exact List.mem_cons_of_mem _ (hi.mem_of_mem_rest t ht)
  | .dict he _ => by intro t ht; exact List.mem_cons_of_mem _ (he.mem_of_mem_rest t ht)

/-- `mem_of_mem_rest` for array items. -/
theorem ParsesItems.mem_of_mem_rest {fuel : Nat} {ts : List Token} {os : List PdfObject}
    {r : List Token} : ParsesItems fuel ts os r → ∀ t ∈ r, t ∈ ts
  | .nil => by intro t ht; simp [ht]
  | .cons hp hi => by intro t ht; exact hp.mem_of_mem_rest t (hi.mem_of_mem_rest t ht)

/-- `mem_of_mem_rest` for dictionary entries. -/
theorem ParsesEntries.mem_of_mem_rest {fuel : Nat} {ts : List Token}
    {es : List (Name × PdfObject)} {r : List Token} :
    ParsesEntries fuel ts es r → ∀ t ∈ r, t ∈ ts
  | .nil => by intro t ht; simp [ht]
  | .cons hp he => by
    intro t ht; exact List.mem_cons_of_mem _ (hp.mem_of_mem_rest t (he.mem_of_mem_rest t ht))
end

mutual
/-- Depth bound: with fuel `F` only objects of depth at most `F` are derived. -/
theorem Parses.depth_le {fuel : Nat} {ts : List Token} {o : PdfObject} {r : List Token} :
    Parses fuel ts o r → o.depth ≤ fuel
  | .ref _ | .int _ | .real | .litString | .hexString | .name | .true_ | .false_ | .null => by
    simp [PdfObject.depth]
  | .array hi => by have := hi.depth_le; simp [PdfObject.depth]; omega
  | .dict he _ => by have := he.depth_le; simp [PdfObject.depth]; omega

/-- Depth bound for array items. -/
theorem ParsesItems.depth_le {fuel : Nat} {ts : List Token} {os : List PdfObject}
    {r : List Token} : ParsesItems fuel ts os r → PdfObject.depthList os ≤ fuel
  | .nil => by simp [PdfObject.depthList]
  | .cons hp hi => by
    have := hp.depth_le; have := hi.depth_le; simp [PdfObject.depthList]; omega

/-- Depth bound for dictionary entries. -/
theorem ParsesEntries.depth_le {fuel : Nat} {ts : List Token}
    {es : List (Name × PdfObject)} {r : List Token} :
    ParsesEntries fuel ts es r → PdfObject.depthDict es ≤ fuel
  | .nil => by simp [PdfObject.depthDict]
  | .cons hp he => by
    have := hp.depth_le; have := he.depth_le; simp [PdfObject.depthDict]; omega
end

/-! ## Completeness of `parse` -/

mutual
/-- Completeness: every derivation is found by `parse`. -/
theorem Parses.parse_eq {fuel : Nat} {ts : List Token} {o : PdfObject} {r : List Token} :
    Parses fuel ts o r → parse fuel ts = .ok (o, r)
  | .ref h => by simp [parse, parseIntOrRef, h]
  | .int hnot => by simp only [parse]; exact parseIntOrRef_int hnot
  | .real | .litString | .hexString | .name => by simp [parse]
  | .true_ => by simp [parse, keywordObj]
  | .false_ => by simp [parse, keywordObj, kwTrue, kwFalse]
  | .null => by simp [parse, keywordObj, kwTrue, kwFalse, kwNull]
  | .array hi => by simp [parse, hi.parseItems_eq]
  | .dict he hnd => by simp [parse, he.parseEntries_eq (seen := []) hnd (by intro _ _ hm; cases hm)]

/-- Completeness for array items. -/
theorem ParsesItems.parseItems_eq {fuel : Nat} {ts : List Token} {os : List PdfObject}
    {r : List Token} : ParsesItems fuel ts os r → parseItems fuel ts = .ok (os, r)
  | .nil => by simp [parseItems]
  | .cons (mid := mid) hp hi => by
    obtain ⟨t, rest, rfl, ht, -⟩ := hp.head
    have hlt : mid.length < rest.length + 1 := by have := hp.length_lt; simpa using this
    rw [parseItems]
    rotate_left
    · exact ht
    rw [hp.parse_eq]
    simp only [hlt, ↓reduceDIte]
    rw [hi.parseItems_eq]

/-- Completeness for dictionary entries, given that the keys are distinct and not in
`seen`. -/
theorem ParsesEntries.parseEntries_eq {fuel : Nat} {ts : List Token}
    {es : List (Name × PdfObject)} {r : List Token} {seen : List Name} :
    ParsesEntries fuel ts es r → (Dict.keys es).Nodup → (∀ k ∈ Dict.keys es, k ∉ seen) →
    parseEntries fuel seen ts = .ok (es, r)
  | .nil, _, _ => by simp [parseEntries]
  | .cons (k := k) (ts := rest) (mid := mid) (es := es') hp he, hnd, hs => by
    rw [keys_cons, List.nodup_cons] at hnd
    have hk : k ∉ seen := hs k (by simp [keys_cons])
    have hs' : ∀ x ∈ Dict.keys es', x ∉ k :: seen := by
      intro x hx hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact hnd.1 hx
      · exact hs x (by rw [keys_cons]; exact List.mem_cons_of_mem _ hx) hm
    have hlt : mid.length < rest.length := hp.length_lt
    simp only [parseEntries, hk, ↓reduceIte]
    rw [hp.parse_eq]
    simp only [hlt, ↓reduceDIte]
    rw [he.parseEntries_eq hnd.2 hs']
end

/-! ## Canonical results -/

/-- Every real token of `ts` carries a canonical decimal. -/
def RealsCanonical (ts : List Token) : Prop := ∀ d, Token.real d ∈ ts → d.IsCanonical

/-- Every name token of `ts` is free of byte 0. -/
def NamesCanonical (ts : List Token) : Prop := ∀ n, Token.name n ∈ ts → n.isCanonical = true

/-- `RealsCanonical` passes to a list whose members all occur in `ts`. -/
theorem RealsCanonical.mono {ts ts' : List Token} (h : RealsCanonical ts)
    (hs : ∀ t ∈ ts', t ∈ ts) : RealsCanonical ts' := fun d hd => h d (hs _ hd)

/-- `NamesCanonical` passes to a list whose members all occur in `ts`. -/
theorem NamesCanonical.mono {ts ts' : List Token} (h : NamesCanonical ts)
    (hs : ∀ t ∈ ts', t ∈ ts) : NamesCanonical ts' := fun n hn => h n (hs _ hn)

mutual
/-- Derived objects are canonical when the input's real and name tokens are. -/
theorem Parses.isCanonical {fuel : Nat} {ts : List Token} {o : PdfObject} {r : List Token} :
    Parses fuel ts o r → RealsCanonical ts → NamesCanonical ts → o.isCanonical = true
  | .ref _, _, _ | .int _, _, _ | .litString, _, _ | .hexString, _, _ | .true_, _, _
  | .false_, _, _ | .null, _, _ => by simp [PdfObject.isCanonical]
  | .real, hr, _ => by simpa [PdfObject.isCanonical] using hr _ (by simp)
  | .name, _, hn => by simpa [PdfObject.isCanonical] using hn _ (by simp)
  | .array hi, hr, hn => by
    simp only [PdfObject.isCanonical]
    exact hi.isCanonical (hr.mono fun _ ht => List.mem_cons_of_mem _ ht)
      (hn.mono fun _ ht => List.mem_cons_of_mem _ ht)
  | .dict he hnd, hr, hn => by
    obtain ⟨h1, h2⟩ := he.isCanonical (hr.mono fun _ ht => List.mem_cons_of_mem _ ht)
      (hn.mono fun _ ht => List.mem_cons_of_mem _ ht)
    simp only [PdfObject.isCanonical, Dict.keysNodup, decide_eq_true hnd, h1, h2,
      Bool.and_self]

/-- Array items are canonical when the input's real and name tokens are. -/
theorem ParsesItems.isCanonical {fuel : Nat} {ts : List Token} {os : List PdfObject}
    {r : List Token} : ParsesItems fuel ts os r → RealsCanonical ts → NamesCanonical ts →
    PdfObject.isCanonicalList os = true
  | .nil, _, _ => by simp [PdfObject.isCanonicalList]
  | .cons hp hi, hr, hn => by
    simp only [PdfObject.isCanonicalList, Bool.and_eq_true]
    exact ⟨hp.isCanonical hr hn,
      hi.isCanonical (hr.mono hp.mem_of_mem_rest) (hn.mono hp.mem_of_mem_rest)⟩

/-- Dictionary entries have canonical values and keys when the input's real and name tokens
are canonical. -/
theorem ParsesEntries.isCanonical {fuel : Nat} {ts : List Token}
    {es : List (Name × PdfObject)} {r : List Token} :
    ParsesEntries fuel ts es r → RealsCanonical ts → NamesCanonical ts →
    PdfObject.isCanonicalDict es = true ∧ es.all (fun e => e.1.isCanonical) = true
  | .nil, _, _ => by simp [PdfObject.isCanonicalDict]
  | .cons (k := k) hp he, hr, hn => by
    have hr' := hr.mono fun _ ht => List.mem_cons_of_mem _ ht
    have hn' := hn.mono fun _ ht => List.mem_cons_of_mem _ ht
    obtain ⟨h1, h2⟩ := he.isCanonical (hr'.mono hp.mem_of_mem_rest)
      (hn'.mono hp.mem_of_mem_rest)
    have hk : k.isCanonical = true := hn k (by simp)
    simp only [PdfObject.isCanonicalDict, List.all_cons, hp.isCanonical hr' hn', h1, h2, hk,
      Bool.and_self, and_self]
end

/-- Canonical output: if every real token of the input is canonical and every name token is
free of byte 0, the derived object is `PdfObject.Canonical` (the hypothesis of task 1.7's
round-trip theorem). Dictionary keys are distinct by `Parses.dict`. -/
theorem Parses.canonical {F : Nat} {ts : List Token} {o : PdfObject} {r : List Token}
    (h : Parses F ts o r) (hr : ∀ d, Token.real d ∈ ts → d.IsCanonical)
    (hn : ∀ n, Token.name n ∈ ts → n.isCanonical = true) : o.Canonical :=
  h.isCanonical hr hn

/-! ## Main theorems -/

/-- `parse` is exactly the grammar: it succeeds with `(o, r)` iff `Parses F ts o r`. -/
theorem parse_eq_ok_iff {F : Nat} {ts : List Token} {o : PdfObject} {r : List Token} :
    parse F ts = .ok (o, r) ↔ Parses F ts o r :=
  ⟨parse_sound, Parses.parse_eq⟩

/-- `parse` fails iff the grammar derives nothing from `ts` (used by task 1.8, which compares
failures only as "is an error"). -/
theorem parse_isError_iff {F : Nat} {ts : List Token} :
    (∃ e, parse F ts = .error e) ↔ ¬ ∃ o r, Parses F ts o r := by
  constructor
  · rintro ⟨e, he⟩ ⟨o, r, h⟩
    rw [h.parse_eq] at he; cases he
  · intro hn
    cases hp : parse F ts with
    | error e => exact ⟨e, rfl⟩
    | ok p => exact absurd ⟨p.1, p.2, parse_sound hp⟩ hn

/-- Unambiguity (Plan.md §4 S6): a token list derives at most one object and one rest. -/
theorem Parses.unique {F : Nat} {ts : List Token} {o o' : PdfObject} {r r' : List Token}
    (h : Parses F ts o r) (h' : Parses F ts o' r') : o = o' ∧ r = r' := by
  have := h.parse_eq.symm.trans h'.parse_eq
  simp only [Except.ok.injEq, Prod.mk.injEq] at this
  exact this

/-- Depth bound for `parse`: a successful parse with fuel `F` has depth at most `F`. -/
theorem parse_depth_le {F : Nat} {ts : List Token} {o : PdfObject} {r : List Token}
    (h : parse F ts = .ok (o, r)) : o.depth ≤ F :=
  (parse_sound h).depth_le

/-- Consumption for `parse`: a successful parse consumes at least one token. -/
theorem parse_length_lt {F : Nat} {ts : List Token} {o : PdfObject} {r : List Token}
    (h : parse F ts = .ok (o, r)) : r.length < ts.length :=
  (parse_sound h).length_lt

/-! ## Compile-time checks -/

section Tests

private def kw (s : String) : Token := .keyword s.toUTF8.toList
private def nm (s : String) : Name := Name.ofString s
private def ok? (F : Nat) (ts : List Token) : Option (PdfObject × List Token) :=
  match parse F ts with
  | .ok p => some p
  | .error _ => none
private def err? (F : Nat) (ts : List Token) : Option Err :=
  match parse F ts with
  | .error e => some e
  | .ok _ => none

-- keyword constants are the ASCII spellings
#guard kwR == "R".toUTF8.toList && kwTrue == "true".toUTF8.toList &&
  kwFalse == "false".toUTF8.toList && kwNull == "null".toUTF8.toList
-- G1: references and integers
#guard ok? 0 [.int 1, .int 0, kw "R"] == some (.ref 1 0, [])
#guard ok? 0 [.int 12, .int 65535, kw "R", .int 7] == some (.ref 12 65535, [.int 7])
#guard err? 0 [.int 0, .int 0, kw "R"] == some .badRef
#guard err? 0 [.int 1, .int 70000, kw "R"] == some .badRef
#guard err? 0 [.int 1, .int (-1), kw "R"] == some .badRef
#guard ok? 0 [.int 1, .int 0, .name (nm "A")] == some (.int 1, [.int 0, .name (nm "A")])
#guard ok? 0 [.int 1, .int 0] == some (.int 1, [.int 0])
#guard ok? 0 [.int 1, .int 0, kw "obj"] == some (.int 1, [.int 0, kw "obj"])
#guard ok? 0 [.int (-5), kw "R"] == some (.int (-5), [kw "R"])
-- G2: scalars
#guard ok? 0 [.real ⟨15, 1⟩] == some (.real ⟨15, 1⟩, [])
#guard ok? 0 [.litString [65], .hexString [66]] == some (.string [65], [.hexString [66]])
#guard ok? 0 [.hexString [66]] == some (.string [66], [])
#guard ok? 0 [.name (nm "Type"), .arrayClose] == some (.name (nm "Type"), [.arrayClose])
-- G3: keywords and stray tokens
#guard ok? 0 [kw "true"] == some (.bool true, [])
#guard ok? 0 [kw "false"] == some (.bool false, [])
#guard ok? 0 [kw "null", kw "null"] == some (.null, [kw "null"])
#guard err? 5 [kw "obj"] == some .unexpectedKeyword
#guard err? 5 [kw "R"] == some .unexpectedKeyword
#guard err? 5 [.arrayClose] == some .unexpectedToken
#guard err? 5 [.dictClose] == some .unexpectedToken
#guard err? 5 [.braceOpen] == some .unexpectedToken
#guard err? 5 [.braceClose] == some .unexpectedToken
-- G6: empty input
#guard err? 5 [] == some .unexpectedEnd
-- G4/G5: nesting, depth limit at exactly F and F + 1
#guard ok? 2 [.arrayOpen, .int 1, .arrayOpen, .int 2, .arrayClose, .dictOpen, .name (nm "A"),
    .int 3, .int 0, kw "R", .dictClose, .arrayClose, .int 9] ==
  some (.array [.int 1, .array [.int 2], .dict [(nm "A", .ref 3 0)]], [.int 9])
#guard err? 1 [.arrayOpen, .arrayOpen, .arrayClose, .arrayClose] == some .depthLimit
#guard ok? 2 [.arrayOpen, .arrayOpen, .arrayClose, .arrayClose] ==
  some (.array [.array []], [])
#guard err? 0 [.arrayOpen, .arrayClose] == some .depthLimit
#guard err? 0 [.dictOpen, .dictClose] == some .depthLimit
#guard ok? 1 [.dictOpen, .dictClose] == some (.dict [], [])
#guard ok? 0 [.int 42] == some (.int 42, [])
#guard ok? 1 [.dictOpen, .name (nm "B"), .int 1, .name (nm "A"), .int 2, .dictClose] ==
  some (.dict [(nm "B", .int 1), (nm "A", .int 2)], [])
#guard ok? 1 [.arrayOpen, .int 1, .int 0, kw "R", .int 2, .arrayClose] ==
  some (.array [.ref 1 0, .int 2], [])
-- G5: dictionary errors
#guard err? 1 [.dictOpen, .name (nm "A"), .int 1, .name (nm "A"), .int 2, .dictClose] ==
  some .duplicateKey
#guard err? 1 [.dictOpen, .int 1, .int 2, .dictClose] == some .nonNameKey
#guard err? 1 [.dictOpen, .name (nm "A"), .dictClose] == some .unexpectedToken
#guard err? 1 [.dictOpen, .name (nm "A"), .int 1] == some .unexpectedEnd
-- G4: unterminated array, bad item
#guard err? 1 [.arrayOpen, .int 1, .int 2] == some .unexpectedEnd
#guard err? 1 [.arrayOpen, .dictClose] == some .unexpectedToken
#guard err? 1 [.arrayOpen, kw "foo", .arrayClose] == some .unexpectedKeyword

example : Parses 1 [.arrayOpen, .arrayClose] (.array []) [] := .array .nil
example : ¬ ∃ o r, Parses 0 [.arrayOpen, .arrayClose] o r := fun ⟨_, _, h⟩ => by cases h
example {ts : List Token} {o : PdfObject} {r : List Token} (h : Parses 3 ts o r) :
    o.depth ≤ 3 := h.depth_le

end Tests

end SafePdf.Spec.Object
