import SafePdf.Core.Filter

/-!
# Budgeted decoding of structural streams (task 3.13)

Plan.md §3 (S3: resource bounds per stream and per document), §5.2. Builds on the
document-wide accounting of task 3.10 (`Filter.decodeStreamB`, rules B1–B5 in
`Core.Filter`).

Cross-reference streams (`Core.Xref.Chain.loadChainB`) and object streams
(`Core.Xref.ObjStm.decodeObjStmB`) are decoded by the core itself. Their budgeted decodes go
through `decodeBytesB`, the budgeted twin of `Filter.decodeBytes` (rule F8): `decodeStreamB`,
with an image-codec result turned into the caller's error.

## Theorems

* `capped_of_le`: with at least `maxDecodedStreamBytes` left, the capped limits of a budgeted
  stage are the limits themselves.
* `applyStagesB_cost`, `decodeStreamB_cost`: **one decode costs at most
  `(maxFilters + 1) · (maxDecodedStreamBytes + raw.size)`** of the budget, whatever the budget.
* `applyStagesB_eq`, `decodeStreamB_eq`: **budget large enough ⇒ same result.** With at
  least that much budget left, `decodeStreamB` returns exactly what `decodeStream` returns.
  This needs no monotonicity of the decoders in their limit: while the remaining budget is at
  least the per-stream limit, every budgeted stage runs under exactly `limits`.
* `decodeBytesB_le`, `decodeBytesB_charge`, `decodeBytesB_size_le`, `decodeBytesB_cost`,
  `decodeBytesB_eq`: the same laws for the structural entry point.
-/

namespace SafePdf.Core.Filter

open SafePdf

/-- With at least the per-stream limit left, a budgeted stage runs under `limits` itself. -/
theorem capped_of_le {limits : Limits} {rem : Nat} (h : limits.maxDecodedStreamBytes ≤ rem) :
    capped limits rem = limits := by
  unfold capped
  rw [Nat.min_eq_left h]

/-- With at least the per-stream limit left, `budgetErr` keeps the error. -/
theorem budgetErr_of_le {limits : Limits} {rem : Nat} (h : limits.maxDecodedStreamBytes ≤ rem)
    (e : Error) : budgetErr limits rem e = e := by
  unfold budgetErr
  split
  · simp only [show ¬ rem < limits.maxDecodedStreamBytes by omega, ↓reduceIte]
  · rfl

/-- A failed stage is charged at most the per-stream limit. -/
theorem failCharge_le (limits : Limits) (rem : Nat) (f : ByteFilter) :
    failCharge limits rem f ≤ limits.maxDecodedStreamBytes := by
  unfold failCharge
  split
  · exact Nat.zero_le _
  · exact Nat.min_le_left _ _

/-- **Cost of a chain**: `applyStagesB` charges at most `M` per stage when its input and the
per-stream limit are at most `M`. -/
theorem applyStagesB_cost (limits : Limits) (strict : Bool) :
    (stages : List Stage) → (rem : Nat) → (b : ByteArray) → (M : Nat) → b.size ≤ M →
    limits.maxDecodedStreamBytes ≤ M →
    rem ≤ (applyStagesB limits strict stages rem b).2 + stages.length * M
  | [], rem, b, M, _, _ => by simp [applyStagesB]
  | ⟨.image _, _⟩ :: [], rem, b, M, _, _ => by simp [applyStagesB]
  | ⟨.image _, _⟩ :: _ :: _, rem, _, M, _, _ => by simp [applyStagesB]
  | ⟨.byte f, p⟩ :: rest, rem, b, M, hb, hM => by
    cases ho : decodeOne (capped limits rem) strict f p b with
    | error e =>
      simp only [applyStagesB, ho, List.length_cons]
      have := failCharge_le limits rem f
      have : failCharge limits rem f ≤ rem := by
        unfold failCharge; split
        · exact Nat.zero_le _
        · exact Nat.min_le_right _ _
      rw [Nat.succ_mul]
      omega
    | ok o =>
      simp only [applyStagesB, ho, List.length_cons]
      have ho' : o.size ≤ M := by
        rcases decodeOne_size_le ho with h | h
        · have : (capped limits rem).maxDecodedStreamBytes ≤ limits.maxDecodedStreamBytes :=
            Nat.min_le_left _ _
          omega
        · rw [h]; exact hb
      by_cases hs : o.size ≤ rem
      · simp only [hs, ↓reduceIte]
        have ih := applyStagesB_cost limits strict rest (rem - o.size) o M ho' hM
        rw [Nat.succ_mul]
        omega
      · simp only [hs, ↓reduceIte]
        exact Nat.le_add_right _ _

/-- **Cost of one decode** (S3): whatever the budget, `decodeStreamB` charges at most
`(maxFilters + 1) · (maxDecodedStreamBytes + raw.size)`. -/
theorem decodeStreamB_cost (limits : Limits) (budget : Budget) (d : Dict) (raw : ByteArray)
    (strict : Bool) :
    budget.remaining ≤ (decodeStreamB limits budget d raw strict).2.remaining +
      (limits.maxFilters + 1) * (limits.maxDecodedStreamBytes + raw.size) := by
  have hM : limits.maxDecodedStreamBytes ≤ limits.maxDecodedStreamBytes + raw.size :=
    Nat.le_add_right _ _
  have hb : raw.size ≤ limits.maxDecodedStreamBytes + raw.size := Nat.le_add_left _ _
  have hK : limits.maxDecodedStreamBytes + raw.size ≤
      (limits.maxFilters + 1) * (limits.maxDecodedStreamBytes + raw.size) := by
    rw [Nat.succ_mul]; exact Nat.le_add_left _ _
  cases hp : parseChain limits d with
  | error e => simp only [decodeStreamB, hp]; exact Nat.le_add_right _ _
  | ok stages =>
    have hlen := parseChain_length_le hp
    have hmul : stages.length * (limits.maxDecodedStreamBytes + raw.size) ≤
        (limits.maxFilters + 1) * (limits.maxDecodedStreamBytes + raw.size) :=
      Nat.mul_le_mul_right _ (by omega)
    cases hbyte : hasByte stages with
    | true =>
      simp only [decodeStreamB, hp, hbyte, ↓reduceIte]
      have := applyStagesB_cost limits strict stages budget.remaining raw
        (limits.maxDecodedStreamBytes + raw.size) hb hM
      omega
    | false =>
      cases hr : applyStages limits strict stages raw with
      | error e =>
        simp only [decodeStreamB, hp, hbyte, hr, Bool.false_eq_true, ↓reduceIte]
        exact Nat.le_add_right _ _
      | ok r =>
        have hrs := applyStages_size_le limits strict stages raw r hr
        by_cases hs : r.bytes.size ≤ budget.remaining
        · simp only [decodeStreamB, hp, hbyte, hr, hs, Bool.false_eq_true, ↓reduceIte]
          omega
        · simp only [decodeStreamB, hp, hbyte, hr, hs, Bool.false_eq_true, ↓reduceIte]
          exact Nat.le_add_right _ _

/-- **Budget large enough ⇒ same chain result.** If the input and the per-stream limit are at
most `M` and at least `M` per stage is left, `applyStagesB` returns what `applyStages`
returns. -/
theorem applyStagesB_eq (limits : Limits) (strict : Bool) :
    (stages : List Stage) → (rem : Nat) → (b : ByteArray) → (M : Nat) → b.size ≤ M →
    limits.maxDecodedStreamBytes ≤ M → stages.length * M ≤ rem →
    (applyStagesB limits strict stages rem b).1 = applyStages limits strict stages b
  | [], rem, b, M, _, _, _ => by simp [applyStagesB, applyStages]
  | ⟨.image _, _⟩ :: [], rem, b, M, _, _, _ => by simp [applyStagesB, applyStages]
  | ⟨.image _, _⟩ :: _ :: _, rem, _, M, _, _, _ => by simp [applyStagesB, applyStages]
  | ⟨.byte f, p⟩ :: rest, rem, b, M, hb, hM, hr => by
    simp only [List.length_cons, Nat.succ_mul] at hr
    have hcap : limits.maxDecodedStreamBytes ≤ rem := by omega
    cases ho : decodeOne limits strict f p b with
    | error e =>
      simp only [applyStagesB, applyStages, capped_of_le hcap, ho, budgetErr_of_le hcap]
    | ok o =>
      have ho' : o.size ≤ M := by
        rcases decodeOne_size_le ho with h | h
        · omega
        · rw [h]; exact hb
      have hs : o.size ≤ rem := by omega
      simp only [applyStagesB, applyStages, capped_of_le hcap, ho, hs, ↓reduceIte]
      exact applyStagesB_eq limits strict rest (rem - o.size) o M ho' hM (by omega)

/-- **Budget large enough ⇒ same result** (task 3.13). With at least
`(maxFilters + 1) · (maxDecodedStreamBytes + raw.size)` left, `decodeStreamB` returns exactly
what the unbudgeted `decodeStream` returns. -/
theorem decodeStreamB_eq {limits : Limits} {budget : Budget} {d : Dict} {raw : ByteArray}
    {strict : Bool}
    (h : (limits.maxFilters + 1) * (limits.maxDecodedStreamBytes + raw.size) ≤ budget.remaining) :
    (decodeStreamB limits budget d raw strict).1 = decodeStream limits d raw strict := by
  have hM : limits.maxDecodedStreamBytes ≤ limits.maxDecodedStreamBytes + raw.size :=
    Nat.le_add_right _ _
  have hb : raw.size ≤ limits.maxDecodedStreamBytes + raw.size := Nat.le_add_left _ _
  have hK : limits.maxDecodedStreamBytes + raw.size ≤
      (limits.maxFilters + 1) * (limits.maxDecodedStreamBytes + raw.size) := by
    rw [Nat.succ_mul]; exact Nat.le_add_left _ _
  cases hp : parseChain limits d with
  | error e => simp [decodeStreamB, decodeStream, hp]
  | ok stages =>
    have hlen := parseChain_length_le hp
    have hmul : stages.length * (limits.maxDecodedStreamBytes + raw.size) ≤
        (limits.maxFilters + 1) * (limits.maxDecodedStreamBytes + raw.size) :=
      Nat.mul_le_mul_right _ (by omega)
    cases hbyte : hasByte stages with
    | true =>
      simp only [decodeStreamB, decodeStream, hp, hbyte, ↓reduceIte]
      exact applyStagesB_eq limits strict stages budget.remaining raw _ hb hM (by omega)
    | false =>
      cases hr : applyStages limits strict stages raw with
      | error e => simp [decodeStreamB, decodeStream, hp, hbyte, hr]
      | ok r =>
        have hrs := applyStages_size_le limits strict stages raw r hr
        have hs : r.bytes.size ≤ budget.remaining := by omega
        simp [decodeStreamB, decodeStream, hp, hbyte, hr, hs]

/-! ## Structural streams -/

/-- **Budgeted structural decode** (rule F8 with the budget, task 3.13): `decodeStreamB`, an
image-codec result being the error `imageErr`. Returns the budget also on failure. -/
def decodeBytesB (limits : Limits) (budget : Budget) (d : Dict) (raw : ByteArray)
    (imageErr : Error) (strict : Bool := true) : (Except Error ByteArray) × Budget :=
  let p := decodeStreamB limits budget d raw strict
  (match p.1 with
   | .error e => .error e
   | .ok (.data b) => .ok b
   | .ok (.image _ _ _) => .error imageErr, p.2)

/-- `decodeBytesB` never increases the budget. -/
theorem decodeBytesB_le (limits : Limits) (budget : Budget) (d : Dict) (raw : ByteArray)
    (imageErr : Error) (strict : Bool) :
    (decodeBytesB limits budget d raw imageErr strict).2.remaining ≤ budget.remaining :=
  decodeStreamB_le limits budget d raw strict

/-- **Charge law**: a successful structural decode was charged its bytes. -/
theorem decodeBytesB_charge {limits : Limits} {budget : Budget} {d : Dict} {raw : ByteArray}
    {imageErr : Error} {strict : Bool} {out : ByteArray}
    (h : (decodeBytesB limits budget d raw imageErr strict).1 = .ok out) :
    out.size + (decodeBytesB limits budget d raw imageErr strict).2.remaining ≤
      budget.remaining := by
  unfold decodeBytesB at h ⊢
  simp only at h ⊢
  split at h
  · cases h
  · rename_i b hb
    simp only [Except.ok.injEq] at h; subst h
    exact decodeStreamB_charge (r := .data b) hb
  · cases h

/-- **Per-stream bound** of `decodeBytesB`. -/
theorem decodeBytesB_size_le {limits : Limits} {budget : Budget} {d : Dict} {raw : ByteArray}
    {imageErr : Error} {strict : Bool} {out : ByteArray}
    (h : (decodeBytesB limits budget d raw imageErr strict).1 = .ok out) :
    out.size ≤ limits.maxDecodedStreamBytes := by
  unfold decodeBytesB at h
  simp only at h
  split at h
  · cases h
  · rename_i b hb
    simp only [Except.ok.injEq] at h; subst h
    exact decodeStreamB_size_le (r := .data b) hb
  · cases h

/-- **Cost of one structural decode**: at most `(maxFilters + 1) · (maxDecodedStreamBytes +
raw.size)`. -/
theorem decodeBytesB_cost (limits : Limits) (budget : Budget) (d : Dict) (raw : ByteArray)
    (imageErr : Error) (strict : Bool) :
    budget.remaining ≤ (decodeBytesB limits budget d raw imageErr strict).2.remaining +
      (limits.maxFilters + 1) * (limits.maxDecodedStreamBytes + raw.size) :=
  decodeStreamB_cost limits budget d raw strict

/-- **Budget large enough ⇒ same result**: `decodeBytesB` returns what `decodeBytes`
returns. -/
theorem decodeBytesB_eq {limits : Limits} {budget : Budget} {d : Dict} {raw : ByteArray}
    {imageErr : Error} {strict : Bool}
    (h : (limits.maxFilters + 1) * (limits.maxDecodedStreamBytes + raw.size) ≤ budget.remaining) :
    (decodeBytesB limits budget d raw imageErr strict).1 = decodeBytes limits d raw imageErr strict := by
  unfold decodeBytesB decodeBytes
  simp only
  rw [decodeStreamB_eq h]
  rcases decodeStream limits d raw strict with _ | (_ | _) <;> rfl

end SafePdf.Core.Filter
