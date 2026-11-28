/-!
# PDF object model (Plan.md §3 rules 1–3, §4 S1/S2/S6/S7/C5, §5.1, §6 Phase 1)

The data types every later layer of Phase 1 is stated over: the lexer spec (1.2) and
tokenizer (1.3) produce tokens whose payloads are these types, the object grammar spec (1.4)
and parser (1.5) produce `PdfObject`s, and the printer (1.7) maps them back to bytes so that
the M1 exit theorem `parse (print o) = o` can be stated (over `PdfObject.Canonical o`).

ISO 32000-2 §7.3 defines nine basic object types plus the indirect reference `n g R`.

## Design decisions

* **Direct vs. indirect objects.** `PdfObject` holds the *direct* objects: null, boolean,
  integer, real, string, name, array, dictionary and indirect reference. Streams (§7.3.8) can
  only occur as the body of an indirect object (`n g obj … endobj`), so they live in
  `IndirectBody.stream`, not in `PdfObject`. Nesting is therefore stream-free by construction
  and the bulk stream bytes stay out of the recursive type.
* **Reals are exact decimals, never `Float`.** `Decimal` is `mantissa · 10^(-scale)` with
  `mantissa : Int`, `scale : Nat`. Its canonical form has no trailing zero in the mantissa when
  `scale > 0` (`Decimal.IsCanonical`); `Decimal.normalize` computes it and is proven to give a
  canonical value (`Decimal.normalize_isCanonical`) equal in value to its input
  (`Decimal.normalize_value`), and to be the identity on canonical values. So `1.50`, `1.5`
  and `+1.500` all parse to `⟨15, 1⟩`; `-0.0` and `0.` become `⟨0, 0⟩`. A real with scale `0`
  still differs from an integer (it is `real`, not `int`); the printer must spell it with a
  `.` (e.g. `5.0` or `5.`), which the parser normalizes back. The literal's original spelling
  is not kept: the model is the value, the printer chooses one canonical spelling.
* **Strings and names are `List UInt8`.** Proofs about lexing/printing (1.2–1.8) are
  structural over lists; `ByteArray` would force every lemma through `.data.toList`. Direct
  strings and names are short in practice; the large payloads (stream data) are `ByteArray`.
  Consequence for 1.3/1.5: the efficient tokenizer scans the input `ByteArray` by index but
  accumulates string/name payloads into a `List UInt8` (or an `Array` converted once at the
  end); the equivalence proof relates the two via `ByteArray.toList`/`.data.toList`.
  Strings are the *decoded* bytes (escapes and hex resolved); whether the source used a
  literal `( )` or hex `< >` string is not kept. Names are decoded too (after `#xx`), without
  the leading `/`.
* **Dictionaries are ordered association lists** `List (Name × PdfObject)` (`Dict`), keeping
  source order so printing is deterministic. Duplicate keys (undefined in ISO 32000-2 §7.3.7)
  get one rule (S6): the *strict* parser rejects a dictionary with a duplicate key with
  `Error.malformed`; canonical objects have distinct keys (`Dict.keys_nodup`). The repair path
  (Plan.md §5.4) may instead keep the last occurrence, which is what qpdf and pdf.js do.
  `Dict.lookup` returns the first match, which on a canonical dictionary is the only match.
  A key mapped to `null` is equivalent to an absent key (§7.3.7); `Dict.lookup` returns the
  raw entry and `Dict.get?` applies that equivalence.
* **Integers are `Int`, references are `Nat × Nat`.** Range checks (ISO 32000-2 Annex C
  integer range, object number `> 0`, generation `≤ 65535`, `Limits.maxObjects`) belong to the
  lexer/parser/limits, not to the model; any `Int`/`Nat` prints and re-parses exactly.
* **Names may not contain byte 0** (§7.3.5: `#00` is not allowed); that is part of
  `PdfObject.Canonical`, alongside canonical reals and duplicate-free dictionaries.
* **Measures.** `PdfObject.depth` (scalars `0`, containers `1 + max` over children; the
  quantity bounded by `Limits.maxObjectDepth`) and `PdfObject.size` (node count), with lemmas
  that members are strictly smaller, plus `sizeOf` lemmas for `termination_by` proofs.
  All are defined by structural (mutual, nested) recursion.
* **Equality.** `deriving DecidableEq` fails on this nested inductive in Lean v4.36 (even
  through `List` alone), so `PdfObject.instDecidableEq` is built from a structural Boolean
  `PdfObject.beq` with proofs `eq_of_beq` and `beq_self`. It reduces in the kernel, so
  `decide` works on closed objects. `Inhabited` is derived; `Repr` of `PdfObject` is hand-written
  (the derived one is `partial`); `Stream` has a hand-written `Repr` (core has none for
  `ByteArray`) that prints only the data length.

Everything is pure and total.
-/

namespace SafePdf

/-! ## Names -/

/-- A PDF name (ISO 32000-2 §7.3.5): its decoded bytes, after `#xx` processing, without the
leading `/`. -/
structure Name where
  /-- The decoded bytes of the name. -/
  bytes : List UInt8
  deriving DecidableEq, Repr, Inhabited, Hashable

namespace Name

/-- Build a name from an ASCII/UTF-8 string, e.g. `Name.ofString "Type"` for `/Type`. -/
def ofString (s : String) : Name := ⟨s.toUTF8.toList⟩

/-- A name is canonical when it contains no zero byte (ISO 32000-2 §7.3.5 forbids `#00`). -/
def isCanonical (n : Name) : Bool := !n.bytes.contains 0

end Name

/-! ## Exact decimal reals -/

/-- An exact real `mantissa · 10^(-scale)` (ISO 32000-2 §7.3.3 real objects). -/
structure Decimal where
  /-- The signed digits of the number. -/
  mantissa : Int
  /-- The number of digits after the decimal point. -/
  scale : Nat
  deriving DecidableEq, Repr, Inhabited, Hashable

namespace Decimal

/-- Canonical form: no trailing zero digit in the mantissa unless the scale is already `0`.
In particular zero is canonical only as `⟨0, 0⟩`. -/
def isCanonical (d : Decimal) : Bool := d.scale == 0 || d.mantissa % 10 != 0

/-- `IsCanonical d` is `isCanonical d = true`; decidable. -/
abbrev IsCanonical (d : Decimal) : Prop := d.isCanonical = true

/-- Strip trailing zero digits from `m · 10^(-s)`, by structural recursion on `s`. -/
def normalizeAux : Int → Nat → Decimal
  | m, 0 => ⟨m, 0⟩
  | m, s + 1 => if m % 10 = 0 then normalizeAux (m / 10) s else ⟨m, s + 1⟩

/-- The canonical decimal with the same value as `d`. -/
def normalize (d : Decimal) : Decimal := normalizeAux d.mantissa d.scale

/-- `normalizeAux` always yields a canonical decimal. -/
theorem normalizeAux_isCanonical (m : Int) (s : Nat) : (normalizeAux m s).IsCanonical := by
  induction s generalizing m with
  | zero => simp [normalizeAux, IsCanonical, isCanonical]
  | succ s ih =>
    unfold normalizeAux
    split
    · exact ih _
    · simp_all [IsCanonical, isCanonical]

/-- `normalize` always yields a canonical decimal. -/
theorem normalize_isCanonical (d : Decimal) : d.normalize.IsCanonical :=
  normalizeAux_isCanonical _ _

/-- `normalizeAux` preserves the value: `m · 10^(-s) = m' · 10^(-s')`, cross-multiplied. -/
theorem normalizeAux_value (m : Int) (s : Nat) :
    (normalizeAux m s).mantissa * 10 ^ s = m * 10 ^ (normalizeAux m s).scale := by
  induction s generalizing m with
  | zero => simp [normalizeAux]
  | succ s ih =>
    unfold normalizeAux
    split
    · rename_i h
      have hm : m / 10 * 10 = m := Int.ediv_mul_cancel (Int.dvd_of_emod_eq_zero h)
      rw [Int.pow_succ, ← Int.mul_assoc, ih (m / 10), Int.mul_assoc, Int.mul_comm _ 10,
        ← Int.mul_assoc, hm]
    · rfl

/-- `normalize` preserves the value: `d = d.normalize` as rationals, cross-multiplied. -/
theorem normalize_value (d : Decimal) :
    d.normalize.mantissa * 10 ^ d.scale = d.mantissa * 10 ^ d.normalize.scale :=
  normalizeAux_value _ _

/-- `normalizeAux` is the identity on canonical inputs. -/
theorem normalizeAux_of_isCanonical (m : Int) (s : Nat)
    (h : (Decimal.mk m s).IsCanonical) : normalizeAux m s = ⟨m, s⟩ := by
  cases s with
  | zero => rfl
  | succ s =>
    have hm : ¬ m % 10 = 0 := by simpa [IsCanonical, isCanonical] using h
    simp [normalizeAux, hm]

/-- `normalize` is the identity on canonical decimals. -/
theorem normalize_of_isCanonical (d : Decimal) (h : d.IsCanonical) : d.normalize = d := by
  cases d with
  | mk m s => exact normalizeAux_of_isCanonical m s h

/-- `normalize` is idempotent. -/
theorem normalize_normalize (d : Decimal) : d.normalize.normalize = d.normalize :=
  normalize_of_isCanonical _ (normalize_isCanonical d)

end Decimal

/-! ## Direct objects -/

/-- A direct PDF object (ISO 32000-2 §7.3). Streams are not direct objects; see
`IndirectBody`. -/
inductive PdfObject where
  /-- `null` (§7.3.9). -/
  | null
  /-- `true` / `false` (§7.3.2). -/
  | bool (b : Bool)
  /-- An integer (§7.3.3); range checks are the lexer's. -/
  | int (i : Int)
  /-- A real (§7.3.3) as an exact decimal. -/
  | real (r : Decimal)
  /-- A string (§7.3.4): its decoded bytes, literal or hex form forgotten. -/
  | string (s : List UInt8)
  /-- A name (§7.3.5). -/
  | name (n : Name)
  /-- An array (§7.3.6). -/
  | array (items : List PdfObject)
  /-- A dictionary (§7.3.7) as an ordered association list (see `Dict`). -/
  | dict (entries : List (Name × PdfObject))
  /-- An indirect reference `num gen R` (§7.3.10). -/
  | ref (num : Nat) (gen : Nat)
  deriving Inhabited

namespace PdfObject

/-! ### Representation

`deriving Repr` on this nested inductive would generate a `partial` definition (an opaque
constant, invisible to a grep for the keyword), so `Repr` is written by hand as a structural
(mutual, nested) recursion, reproducing the derived format exactly. -/

/-- Layout of a list from its elements' formats, as `List.repr`. -/
def reprListFmt : List Std.Format → Std.Format
  | [] => "[]"
  | fs => Std.Format.bracket "[" (Std.Format.joinSep fs ("," ++ Std.Format.line)) "]"

mutual
/-- `Repr` of an object at precedence `prec`, in the format `deriving Repr` produces. -/
def reprAux : PdfObject → Nat → Std.Format
  | .null, prec =>
    Repr.addAppParen (Std.Format.group (Std.Format.nest 2 "SafePdf.PdfObject.null")) prec
  | .bool b, prec =>
    Repr.addAppParen (Std.Format.group (Std.Format.nest (if prec >= 1024 then 1 else 2)
      ("SafePdf.PdfObject.bool" ++ Std.Format.line ++ reprArg b))) prec
  | .int i, prec =>
    Repr.addAppParen (Std.Format.group (Std.Format.nest (if prec >= 1024 then 1 else 2)
      ("SafePdf.PdfObject.int" ++ Std.Format.line ++ reprArg i))) prec
  | .real r, prec =>
    Repr.addAppParen (Std.Format.group (Std.Format.nest (if prec >= 1024 then 1 else 2)
      ("SafePdf.PdfObject.real" ++ Std.Format.line ++ reprArg r))) prec
  | .string s, prec =>
    Repr.addAppParen (Std.Format.group (Std.Format.nest (if prec >= 1024 then 1 else 2)
      ("SafePdf.PdfObject.string" ++ Std.Format.line ++ reprArg s))) prec
  | .name n, prec =>
    Repr.addAppParen (Std.Format.group (Std.Format.nest (if prec >= 1024 then 1 else 2)
      ("SafePdf.PdfObject.name" ++ Std.Format.line ++ reprArg n))) prec
  | .array xs, prec =>
    Repr.addAppParen (Std.Format.group (Std.Format.nest (if prec >= 1024 then 1 else 2)
      ("SafePdf.PdfObject.array" ++ Std.Format.line ++ reprListFmt (reprList xs)))) prec
  | .dict d, prec =>
    Repr.addAppParen (Std.Format.group (Std.Format.nest (if prec >= 1024 then 1 else 2)
      ("SafePdf.PdfObject.dict" ++ Std.Format.line ++ reprListFmt (reprDict d)))) prec
  | .ref n g, prec =>
    Repr.addAppParen (Std.Format.group (Std.Format.nest (if prec >= 1024 then 1 else 2)
      ("SafePdf.PdfObject.ref" ++ Std.Format.line ++ reprArg n ++ Std.Format.line ++
        reprArg g))) prec

/-- The `Repr` of each element of a list of objects. -/
def reprList : List PdfObject → List Std.Format
  | [] => []
  | x :: xs => reprAux x 0 :: reprList xs

/-- The `Repr` of each entry (a pair) of a dictionary. -/
def reprDict : List (Name × PdfObject) → List Std.Format
  | [] => []
  | (k, v) :: rest =>
    Std.Format.bracket "(" (repr k ++ "," ++ Std.Format.line ++ reprAux v 0) ")" ::
      reprDict rest
end

instance : Repr PdfObject := ⟨reprAux⟩

/-! ### Decidable equality

`deriving DecidableEq` does not apply to this nested inductive in Lean v4.36, so equality is
decided by a structural Boolean comparison `beq`, proven sound (`eq_of_beq`) and reflexive
(`beq_self`). -/

mutual
/-- Structural Boolean equality of objects. -/
def beq : PdfObject → PdfObject → Bool
  | .null, .null => true
  | .bool a, .bool b => a == b
  | .int a, .int b => a == b
  | .real a, .real b => a == b
  | .string a, .string b => a == b
  | .name a, .name b => a == b
  | .array a, .array b => beqList a b
  | .dict a, .dict b => beqDict a b
  | .ref n g, .ref n' g' => n == n' && g == g'
  | _, _ => false

/-- Structural Boolean equality of object lists. -/
def beqList : List PdfObject → List PdfObject → Bool
  | [], [] => true
  | x :: xs, y :: ys => beq x y && beqList xs ys
  | _, _ => false

/-- Structural Boolean equality of dictionary entry lists. -/
def beqDict : List (Name × PdfObject) → List (Name × PdfObject) → Bool
  | [], [] => true
  | (k, v) :: xs, (k', v') :: ys => k == k' && beq v v' && beqDict xs ys
  | _, _ => false
end

mutual
/-- `beq` is sound. -/
theorem eq_of_beq : (a b : PdfObject) → beq a b = true → a = b
  | .array xs, b, h => by
    cases b with
    | array ys =>
      simp only [beq] at h
      rw [eq_of_beqList xs ys h]
    | _ => simp [beq] at h
  | .dict xs, b, h => by
    cases b with
    | dict ys =>
      simp only [beq] at h
      rw [eq_of_beqDict xs ys h]
    | _ => simp [beq] at h
  | .null, b, h | .bool _, b, h | .int _, b, h | .real _, b, h | .string _, b, h
  | .name _, b, h | .ref _ _, b, h => by
    cases b <;> simp_all [beq]

/-- `beqList` is sound. -/
theorem eq_of_beqList : (xs ys : List PdfObject) → beqList xs ys = true → xs = ys
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    simp only [beqList, Bool.and_eq_true] at h
    rw [eq_of_beq x y h.1, eq_of_beqList xs ys h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [beqList] at h

/-- `beqDict` is sound. -/
theorem eq_of_beqDict : (xs ys : List (Name × PdfObject)) → beqDict xs ys = true → xs = ys
  | [], [], _ => rfl
  | (k, v) :: xs, (k', v') :: ys, h => by
    simp only [beqDict, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1.1, eq_of_beq v v' h.1.2, eq_of_beqDict xs ys h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [beqDict] at h
end

mutual
/-- `beq` is reflexive. -/
theorem beq_self : (a : PdfObject) → beq a a = true
  | .array xs => by simp only [beq]; exact beqList_self xs
  | .dict xs => by simp only [beq]; exact beqDict_self xs
  | .null | .bool _ | .int _ | .real _ | .string _ | .name _ | .ref _ _ => by simp [beq]

/-- `beqList` is reflexive. -/
theorem beqList_self : (xs : List PdfObject) → beqList xs xs = true
  | [] => rfl
  | x :: xs => by simp only [beqList, Bool.and_eq_true]; exact ⟨beq_self x, beqList_self xs⟩

/-- `beqDict` is reflexive. -/
theorem beqDict_self : (xs : List (Name × PdfObject)) → beqDict xs xs = true
  | [] => rfl
  | (k, v) :: xs => by
    simp only [beqDict, Bool.and_eq_true, beq_self_eq_true, true_and]
    exact ⟨beq_self v, beqDict_self xs⟩
end

/-- Decidable equality of objects, via `beq`. -/
instance instDecidableEq : DecidableEq PdfObject := fun a b =>
  if h : beq a b = true then isTrue (eq_of_beq a b h)
  else isFalse (fun e => h (e ▸ beq_self a))

end PdfObject

/-- A dictionary: keys in source order. Canonical dictionaries have distinct keys. -/
abbrev Dict := List (Name × PdfObject)

namespace Dict

/-- The keys of a dictionary, in order. -/
def keys (d : Dict) : List Name := d.map Prod.fst

/-- The raw value of the first entry with key `k`, if any. On a canonical dictionary this
is the only entry with key `k`. -/
def lookup (d : Dict) (k : Name) : Option PdfObject :=
  match d with
  | [] => none
  | (k', v) :: rest => if k' = k then some v else lookup rest k

/-- Value lookup with the §7.3.7 rule that an entry whose value is `null` is equivalent to
an absent entry. -/
def get? (d : Dict) (k : Name) : Option PdfObject :=
  match lookup d k with
  | some PdfObject.null => none
  | r => r

/-- Whether all keys are distinct. -/
def keysNodup (d : Dict) : Bool := decide (d.keys.Nodup)

/-- `lookup` finds exactly the members: a result is a member entry. -/
theorem lookup_mem {d : Dict} {k : Name} {v : PdfObject} (h : lookup d k = some v) :
    (k, v) ∈ d := by
  induction d with
  | nil => simp [lookup] at h
  | cons e rest ih =>
    obtain ⟨k', v'⟩ := e
    unfold lookup at h
    split at h
    · rename_i hk
      cases h; subst hk; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

/-- On a dictionary with distinct keys, every member entry is what `lookup` returns. -/
theorem lookup_of_mem {d : Dict} {k : Name} {v : PdfObject} (hnd : d.keys.Nodup)
    (h : (k, v) ∈ d) : lookup d k = some v := by
  induction d with
  | nil => simp at h
  | cons e rest ih =>
    obtain ⟨k', v'⟩ := e
    simp only [keys, List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hk', hnd'⟩ := hnd
    unfold lookup
    rcases List.mem_cons.mp h with he | hr
    · cases he; simp
    · have hne : k' ≠ k := by
        intro heq; subst heq
        exact hk' (List.mem_map.mpr ⟨(k', v), hr, rfl⟩)
      simp only [hne, ite_false]
      exact ih hnd' hr

end Dict

namespace PdfObject

/-- Build a name object from a string, e.g. `PdfObject.nameOf "Type"`. -/
def nameOf (s : String) : PdfObject := .name (Name.ofString s)

/-- A real object from mantissa and scale, normalized to canonical form. -/
def realOf (mantissa : Int) (scale : Nat) : PdfObject :=
  .real (Decimal.normalize ⟨mantissa, scale⟩)

/-! ### Depth and size -/

mutual
/-- Nesting depth: `0` for scalars, `1 + max` over the members for arrays and dictionaries
(`0` children count as depth `0`). This is the quantity `Limits.maxObjectDepth` bounds. -/
def depth : PdfObject → Nat
  | .array xs => depthList xs + 1
  | .dict d => depthDict d + 1
  | _ => 0

/-- Maximum `depth` over a list of objects (`0` if empty). -/
def depthList : List PdfObject → Nat
  | [] => 0
  | x :: xs => max (depth x) (depthList xs)

/-- Maximum `depth` over the values of a dictionary (`0` if empty). -/
def depthDict : List (Name × PdfObject) → Nat
  | [] => 0
  | (_, v) :: rest => max (depth v) (depthDict rest)
end

mutual
/-- Number of object nodes: `1` for scalars, `1 +` the sizes of the members otherwise. -/
def size : PdfObject → Nat
  | .array xs => sizeList xs + 1
  | .dict d => sizeDict d + 1
  | _ => 1

/-- Sum of `size` over a list of objects. -/
def sizeList : List PdfObject → Nat
  | [] => 0
  | x :: xs => size x + sizeList xs

/-- Sum of `size` over the values of a dictionary. -/
def sizeDict : List (Name × PdfObject) → Nat
  | [] => 0
  | (_, v) :: rest => size v + sizeDict rest
end

/-- A member of a list is no deeper than the list's maximum depth. -/
theorem depth_le_depthList {x : PdfObject} {xs : List PdfObject} (h : x ∈ xs) :
    depth x ≤ depthList xs := by
  induction xs with
  | nil => simp at h
  | cons y ys ih =>
    rcases List.mem_cons.mp h with he | hr
    · subst he; simp only [depthList]; exact Nat.le_max_left _ _
    · have := ih hr; simp [depthList]; omega

/-- A dictionary value is no deeper than the dictionary's maximum depth. -/
theorem depth_le_depthDict {k : Name} {v : PdfObject} {d : List (Name × PdfObject)}
    (h : (k, v) ∈ d) : depth v ≤ depthDict d := by
  induction d with
  | nil => simp at h
  | cons e rest ih =>
    obtain ⟨k', v'⟩ := e
    rcases List.mem_cons.mp h with he | hr
    · cases he; simp only [depthDict]; exact Nat.le_max_left _ _
    · have := ih hr; simp [depthDict]; omega

/-- An array member is strictly shallower than the array. -/
theorem depth_lt_array {x : PdfObject} {xs : List PdfObject} (h : x ∈ xs) :
    depth x < depth (.array xs) := by
  have := depth_le_depthList h; simp [depth]; omega

/-- A dictionary value is strictly shallower than the dictionary. -/
theorem depth_lt_dict {k : Name} {v : PdfObject} {d : List (Name × PdfObject)}
    (h : (k, v) ∈ d) : depth v < depth (.dict d) := by
  have := depth_le_depthDict h; simp [depth]; omega

/-- Every object has positive size. -/
theorem size_pos (o : PdfObject) : 0 < size o := by
  cases o <;> simp [size]

/-- A member's size is at most the list's total size. -/
theorem size_le_sizeList {x : PdfObject} {xs : List PdfObject} (h : x ∈ xs) :
    size x ≤ sizeList xs := by
  induction xs with
  | nil => simp at h
  | cons y ys ih =>
    rcases List.mem_cons.mp h with he | hr
    · subst he; simp [sizeList]
    · have := ih hr; simp [sizeList]; omega

/-- A dictionary value's size is at most the dictionary's total size. -/
theorem size_le_sizeDict {k : Name} {v : PdfObject} {d : List (Name × PdfObject)}
    (h : (k, v) ∈ d) : size v ≤ sizeDict d := by
  induction d with
  | nil => simp at h
  | cons e rest ih =>
    obtain ⟨k', v'⟩ := e
    rcases List.mem_cons.mp h with he | hr
    · cases he; simp [sizeDict]
    · have := ih hr; simp [sizeDict]; omega

/-- An array member is strictly smaller than the array. -/
theorem size_lt_array {x : PdfObject} {xs : List PdfObject} (h : x ∈ xs) :
    size x < size (.array xs) := by
  have := size_le_sizeList h; simp [size]; omega

/-- A dictionary value is strictly smaller than the dictionary. -/
theorem size_lt_dict {k : Name} {v : PdfObject} {d : List (Name × PdfObject)}
    (h : (k, v) ∈ d) : size v < size (.dict d) := by
  have := size_le_sizeDict h; simp [size]; omega

/-- `sizeOf` version of `size_lt_array`, for `termination_by` proofs. -/
theorem sizeOf_lt_array {x : PdfObject} {xs : List PdfObject} (h : x ∈ xs) :
    sizeOf x < sizeOf (PdfObject.array xs) := by
  have := List.sizeOf_lt_of_mem h; simp; omega

/-- `sizeOf` version of `size_lt_dict`, for `termination_by` proofs. -/
theorem sizeOf_lt_dict {k : Name} {v : PdfObject} {d : List (Name × PdfObject)}
    (h : (k, v) ∈ d) : sizeOf v < sizeOf (PdfObject.dict d) := by
  have := List.sizeOf_lt_of_mem h; simp at this ⊢; omega

/-! ### Canonical objects -/

mutual
/-- Boolean check of `Canonical`: reals canonical, names free of byte 0, dictionary keys
distinct, recursively. -/
def isCanonical : PdfObject → Bool
  | .real r => r.isCanonical
  | .name n => n.isCanonical
  | .array xs => isCanonicalList xs
  | .dict d => Dict.keysNodup d && d.all (fun e => e.1.isCanonical) && isCanonicalDict d
  | _ => true

/-- `isCanonical` for every member of a list. -/
def isCanonicalList : List PdfObject → Bool
  | [] => true
  | x :: xs => isCanonical x && isCanonicalList xs

/-- `isCanonical` for every value of a dictionary. -/
def isCanonicalDict : List (Name × PdfObject) → Bool
  | [] => true
  | (_, v) :: rest => isCanonical v && isCanonicalDict rest
end

/-- The objects the printer/parser round-trip (task 1.7) is stated over: those the strict
parser can produce. Decidable. -/
abbrev Canonical (o : PdfObject) : Prop := o.isCanonical = true

/-- Members of a canonical array are canonical. -/
theorem Canonical.of_mem_array {x : PdfObject} {xs : List PdfObject}
    (hc : Canonical (.array xs)) (h : x ∈ xs) : Canonical x := by
  simp only [Canonical, isCanonical] at hc
  induction xs with
  | nil => simp at h
  | cons y ys ih =>
    simp only [isCanonicalList, Bool.and_eq_true] at hc
    rcases List.mem_cons.mp h with he | hr
    · subst he; exact hc.1
    · exact ih hc.2 hr

/-- Values of a canonical dictionary are canonical. -/
theorem Canonical.of_mem_dict {k : Name} {v : PdfObject} {d : List (Name × PdfObject)}
    (hc : Canonical (.dict d)) (h : (k, v) ∈ d) : Canonical v := by
  simp only [Canonical, isCanonical, Bool.and_eq_true] at hc
  have hd := hc.2
  clear hc
  induction d with
  | nil => simp at h
  | cons e rest ih =>
    obtain ⟨k', v'⟩ := e
    simp only [isCanonicalDict, Bool.and_eq_true] at hd
    rcases List.mem_cons.mp h with he | hr
    · cases he; exact hd.1
    · exact ih hr hd.2

/-- A canonical dictionary has distinct keys. -/
theorem Canonical.keys_nodup {d : List (Name × PdfObject)} (hc : Canonical (.dict d)) :
    (Dict.keys d).Nodup := by
  simp only [Canonical, isCanonical, Bool.and_eq_true, Dict.keysNodup,
    decide_eq_true_eq] at hc
  exact hc.1.1

/-- `realOf` always builds a canonical object. -/
theorem realOf_canonical (m : Int) (s : Nat) : Canonical (realOf m s) :=
  Decimal.normalize_isCanonical _

end PdfObject

/-! ## Indirect objects and streams -/

/-- A stream (ISO 32000-2 §7.3.8): its dictionary and its raw, still-encoded data bytes
(between `stream` EOL and `endstream`, `/Length` bytes long). -/
structure Stream where
  /-- The stream dictionary. -/
  dict : Dict
  /-- The raw (still filtered) data. -/
  data : ByteArray
  deriving DecidableEq, Inhabited

instance : Repr Stream where
  reprPrec s _ :=
    "{ dict := " ++ repr s.dict ++ ", data := <" ++ repr s.data.size ++ " bytes> }"

/-- The body of an indirect object: a direct object or a stream. -/
inductive IndirectBody where
  /-- A direct object. -/
  | obj (o : PdfObject)
  /-- A stream. -/
  | stream (s : Stream)
  deriving DecidableEq, Repr, Inhabited

/-- An indirect object `num gen obj … endobj` (ISO 32000-2 §7.3.10). -/
structure IndirectObject where
  /-- Object number. -/
  num : Nat
  /-- Generation number. -/
  gen : Nat
  /-- The object's body. -/
  body : IndirectBody
  deriving DecidableEq, Repr, Inhabited

/-- Canonical indirect objects: canonical body (a stream's dictionary as a canonical
dictionary object). -/
def IndirectObject.isCanonical (io : IndirectObject) : Bool :=
  match io.body with
  | .obj o => o.isCanonical
  | .stream s => (PdfObject.dict s.dict).isCanonical

/-! ## Compile-time checks -/

section Tests
open PdfObject

private def sample : PdfObject :=
  .dict [(Name.ofString "Type", nameOf "Page"),
         (Name.ofString "MediaBox", .array [.int 0, .int 0, realOf 6120 1, .int 792]),
         (Name.ofString "Parent", .ref 3 0),
         (Name.ofString "Opt", .null)]

#guard sample == sample
#guard sample != .dict []
#guard Dict.lookup [(Name.ofString "A", .int 1), (Name.ofString "B", .int 2)]
  (Name.ofString "B") == some (.int 2)
#guard Dict.lookup [(Name.ofString "A", .int 1)] (Name.ofString "C") == none
#guard (match sample with | .dict d => Dict.get? d (Name.ofString "Opt") | _ => none) == none
#guard (match sample with
  | .dict d => Dict.lookup d (Name.ofString "Opt") | _ => none) == some .null
#guard sample.depth == 2
#guard sample.size == 9
#guard (PdfObject.array []).depth == 1
#guard realOf 6120 1 == .real ⟨612, 0⟩
#guard Decimal.normalize ⟨-1500, 3⟩ == ⟨-15, 1⟩
#guard Decimal.normalize ⟨0, 4⟩ == ⟨0, 0⟩
#guard !(Decimal.isCanonical ⟨10, 1⟩)
#guard Decimal.isCanonical ⟨10, 0⟩
#guard sample.isCanonical
#guard !(PdfObject.dict [(Name.ofString "A", .int 1), (Name.ofString "A", .int 2)]).isCanonical
#guard !(PdfObject.name ⟨[65, 0]⟩).isCanonical
#guard !(PdfObject.array [.real ⟨50, 1⟩]).isCanonical

example : Canonical (.dict [(⟨[84]⟩, .array [.int 1, .real ⟨15, 1⟩]), (⟨[80]⟩, .ref 3 0)]) := by
  decide
example : PdfObject.array [.int 1, .null] ≠ .array [.int 1] := by decide
example : (IndirectObject.mk 1 0 (.stream ⟨[], ByteArray.empty⟩)).isCanonical = true := by
  decide

end Tests

end SafePdf
