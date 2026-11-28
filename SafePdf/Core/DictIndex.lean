import Std.Data.TreeMap
import SafePdf.Core.Object

/-!
# Ordered index of a dictionary (task 13.24; Plan.md §6 Phase 13, §3 rule 2)

`Dict` is an association list and `Dict.lookup` a list scan, so `n` lookups into an `n`-entry
resource dictionary (`/Font`, `/XObject`, `/ExtGState`, `/ColorSpace`, …) or a catalog `/Dests`
are quadratic. This module gives a dictionary an `O(log n)` lookup:

* `Dict.indexWith f d` is a `Std.TreeMap` (a balanced tree: `O(log n)` per operation in the
  worst case, not a hash map whose unseeded hashes can be collided) keyed by the name bytes,
  built **once** by inserting the entries in order with `insertIfNew`, so the **first** entry
  of a key wins, exactly as in `Dict.lookup`.
* `Dict.indexWith_get?` : `(Dict.indexWith f d)[k.bytes]? = (Dict.lookup d k).map f` for
  **every** dictionary, with or without duplicate keys (the strict parser rejects duplicates;
  the repair path and constructed values may have them, and the first-match rule is preserved
  there). On a dictionary with distinct keys (`Dict.keys_nodup`) the match is unique anyway
  (`Dict.lookup_of_mem`).
* `ResIdx res` is the index of a resource dictionary `res` for the content runner: a lazily
  built (`Thunk`: built on the first lookup, once) top-level index whose entries carry, for a
  direct dictionary value, a lazily built index of that dictionary. The proof fields tie it to
  `Dict.lookup res` so every lookup through it equals the list scan.
-/

namespace SafePdf

open Std

namespace Dict

/-- The ordered index of a dictionary (values mapped by `f`): the first entry of each key. -/
def indexWith {β : Type} (f : PdfObject → β) (d : Dict) : TreeMap (List UInt8) β compare :=
  d.foldl (fun m e => m.insertIfNew e.1.bytes (f e.2)) ∅

/-- The ordered index of a dictionary. -/
def index (d : Dict) : TreeMap (List UInt8) PdfObject compare := indexWith id d

private theorem foldl_get? {β : Type} (f : PdfObject → β) (k : Name) :
    ∀ (d : Dict) (m : TreeMap (List UInt8) β compare),
      (d.foldl (fun m e => m.insertIfNew e.1.bytes (f e.2)) m)[k.bytes]? =
        (match m[k.bytes]? with | some v => some v | none => (lookup d k).map f)
  | [], m => by
      cases h : m[k.bytes]? <;> simp [lookup, h]
  | (k', v) :: rest, m => by
      simp only [List.foldl_cons]
      rw [foldl_get? f k rest]
      rw [TreeMap.getElem?_insertIfNew]
      by_cases hk : k'.bytes = k.bytes
      · have hkk : k' = k := by cases k'; cases k; simp_all
        subst hkk
        cases hm : m[k'.bytes]? with
        | some v0 =>
          have hmem : k'.bytes ∈ m := by
            have h1 : (m[k'.bytes]?).isSome = true := by simp [hm]
            rw [TreeMap.isSome_getElem?_eq_contains] at h1
            exact TreeMap.contains_iff_mem.mp h1
          simp [hmem]
        | none =>
          have hmem : ¬ k'.bytes ∈ m := by
            intro hin
            have h1 := TreeMap.contains_iff_mem.mpr hin
            rw [← TreeMap.isSome_getElem?_eq_contains] at h1
            simp [hm] at h1
          simp [hmem, lookup]
      · have hne : k' ≠ k := fun h => hk (by rw [h])
        have hc : ¬ compare k'.bytes k.bytes = Ordering.eq := fun h => hk (by simpa using h)
        simp [hc, lookup, hne]

/-- **Equality with `Dict.lookup`.** Looking a name up in the index of a dictionary is mapping
`f` over `Dict.lookup`: the first entry of the key, whether or not keys repeat. -/
theorem indexWith_get? {β : Type} (f : PdfObject → β) (d : Dict) (k : Name) :
    (indexWith f d)[k.bytes]? = (lookup d k).map f := by
  unfold indexWith
  rw [foldl_get? f k d ∅]
  simp

/-- The index of a dictionary finds exactly `Dict.lookup`. -/
theorem index_get? (d : Dict) (k : Name) : (index d)[k.bytes]? = lookup d k := by
  unfold index; rw [indexWith_get?]; simp

/-- On a dictionary with distinct keys, a member entry is what the index returns. -/
theorem index_get?_of_mem {d : Dict} {k : Name} {v : PdfObject} (hnd : d.keys.Nodup)
    (h : (k, v) ∈ d) : (index d)[k.bytes]? = some v := by
  rw [index_get?, lookup_of_mem hnd h]

/-- `Dict.get?` (a `null` entry is absent) through an index. -/
def getIdx (m : TreeMap (List UInt8) PdfObject compare) (k : Name) : Option PdfObject :=
  match m[k.bytes]? with
  | some PdfObject.null => none
  | r => r

/-- `Dict.get?` through the index of a dictionary. -/
theorem getIdx_index (d : Dict) (k : Name) : getIdx (index d) k = get? d k := by
  unfold getIdx get?
  rw [index_get?]
  rfl

end Dict

/-- One entry of the top level of a resource index: the raw value and, when it is a direct
dictionary, its lazily built index (empty for any other value). -/
structure ResEnt where
  /-- The raw value. -/
  val : PdfObject
  /-- Index of the value when it is a direct dictionary. -/
  sub : Thunk (TreeMap (List UInt8) PdfObject compare)
  /-- The index is the index of the dictionary. -/
  hsub : ∀ d, val = .dict d → sub.get = Dict.index d

/-- A thunk built from `f` has the value `f ()`. -/
theorem thunk_get_mk {α : Type} (f : Unit → α) : (Thunk.mk f).get = f () := rfl

/-- The entry of a value. -/
def ResEnt.of (v : PdfObject) : ResEnt :=
  ⟨v, Thunk.mk fun _ => match v with | .dict d => Dict.index d | _ => ∅, by
    intro d h; subst h; rw [thunk_get_mk]⟩

/-- The index of a resource dictionary `res`, built lazily on first use and then reused:
the top level maps each key to its first entry (`ResEnt`), and `htop` ties it to
`Dict.lookup res` for every dictionary, duplicates included. -/
structure ResIdx (res : Dict) where
  /-- The top-level index. -/
  top : Thunk (TreeMap (List UInt8) ResEnt compare)
  /-- Lookups agree with the list scan. -/
  htop : ∀ k : Name, (top.get[k.bytes]?).map ResEnt.val = Dict.lookup res k

/-- The index of `res`. -/
def ResIdx.of (res : Dict) : ResIdx res :=
  ⟨Thunk.mk fun _ => Dict.indexWith ResEnt.of res, by
    intro k
    rw [thunk_get_mk, Dict.indexWith_get?]
    cases Dict.lookup res k <;> rfl⟩

/-! ## Checks -/

private def sampleDict : Dict :=
  [(Name.ofString "A", .int 1), (Name.ofString "B", .null), (Name.ofString "A", .int 2),
   (Name.ofString "C", .int 3)]

-- Duplicate keys: the first entry wins, as in `Dict.lookup`.
#guard (Dict.index sampleDict)[(Name.ofString "A").bytes]? == some (.int 1)
#guard (Dict.index sampleDict)[(Name.ofString "C").bytes]? == some (.int 3)
#guard (Dict.index sampleDict)[(Name.ofString "Z").bytes]? == none
-- `null` is absent through `getIdx`, as for `Dict.get?`.
#guard Dict.getIdx (Dict.index sampleDict) (Name.ofString "B") == none
#guard Dict.getIdx (Dict.index sampleDict) (Name.ofString "A") == Dict.get? sampleDict (Name.ofString "A")

end SafePdf
