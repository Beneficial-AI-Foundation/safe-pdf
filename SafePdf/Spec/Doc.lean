import SafePdf.Core.Doc

/-!
# Page tree: end-to-end theorems (task 4.1b)

Plan.md §6 Phase 4 ("page tree with inheritance (`Resources`, `MediaBox`, `CropBox`,
`Rotate`); acyclicity proof"), §5.2 ("Page tree: depth bounded by node count; visited-set on
node ids; `/Kids` cycles rejected"). ISO 32000-2 §7.7.3.

Statements about `Core.Doc.walk` / `ofOpen` / `openDoc` in terms of a **tree view** of the
file, independent of the walk's stack machinery:

* `KidsOf d limits x ks`: node `x = (num, gen)` is an intermediate node (rule W4) whose
  resolved `/Kids` (rule W5) are the references `ks`. `Kid d limits x y`: `y ∈ ks`.
* `KidPath d limits x ys`: `x, ys₀, ys₁, …` is a descending path along `Kid`.
* `NodeAttrs d limits x a`: node `x` is a dictionary whose own attributes are `a` (A1, A2).
* `LeafNode d limits x a c`: node `x` is a leaf (W4) with own attributes `a` and `/Contents` `c`.
* `Descends d limits root anc x`: `x` is reached from `root` along `Kid`; `anc` lists its
  proper ancestors root-first, each with its own attributes.

Theorems:

1. **Acyclicity** (`walk_path_nodup`, `ofOpen_path_nodup`, `openDoc_path_nodup`): after a
   successful open, every descending path from the root `/Pages` node visits pairwise distinct
   object numbers. Hence a node whose `/Kids` contains an ancestor or itself makes the open
   fail (`walk_kid_not_ancestor`, `ofOpen_cycle_error`, `openDoc_cycle_error`). The error kind
   is not pinned: another node popped earlier may fail first (malformed, depth, fetch error).
   The walk itself reports such a cycle as `Error.cycle` (`Core.Doc.loop_cycle`).
2. **Inheritance** (`walk_page_inherit`, `ofOpen_page_inherit`, `openDoc_page_inherit`):
   every page of the document is a leaf reached from the root along `Kid`, and its MediaBox,
   CropBox, Rotate and Resources are those of the nearest node on that root-to-leaf path that
   has the attribute (`nearest`), else the default (Letter, the MediaBox, `0`, none); its
   `/Contents` is the leaf's own.
3. **Fuel** (`loop_fuel_irrelevant`, `walk_fuel_irrelevant`): the walk's fuel `objectCount`
   is never the binding limit: running the loop with any larger fuel gives the same result.
   Every visited node has a non-null object, so its number is a key of the xref index
   (`getObject_ne_null_key`), and visited numbers are distinct, so at most `objectCount`
   nodes can ever be visited. In particular the walk's own fuel-exhaustion branch
   (`limitExceeded .objects` in `loop 0`) is unreachable from the initial state
   (`popLive_exhausted`); a `limitExceeded .objects` result of `walk` can only come from
   `getObject` itself. No distinctness of index keys is needed.
-/

set_option autoImplicit false

namespace SafePdf.Spec.PageTree

open SafePdf
open SafePdf.Core.Open (OpenDoc)
open SafePdf.Core.Doc

/-! ## Tree view -/

/-- Node `x` is an intermediate node (rule W4) whose resolved `/Kids` are `ks` (rule W5). -/
def KidsOf (d : OpenDoc) (limits : Limits) (x : Nat × Nat) (ks : List (Nat × Nat)) : Prop :=
  ∃ nd ko, d.getObject limits x.1 x.2 = .ok (.obj (.dict nd)) ∧ kindOf nd = .inner ∧
    key d limits nd "Kids" = .ok ko ∧ kidsOf ko = some ks

/-- `y` is among the resolved `/Kids` of node `x`. -/
def Kid (d : OpenDoc) (limits : Limits) (x y : Nat × Nat) : Prop :=
  ∃ ks, KidsOf d limits x ks ∧ y ∈ ks

/-- `KidPath d limits x ys`: `x :: ys` is a descending path along `Kid`. -/
inductive KidPath (d : OpenDoc) (limits : Limits) : Nat × Nat → List (Nat × Nat) → Prop
  /-- The one-node path. -/
  | nil (x : Nat × Nat) : KidPath d limits x []
  /-- Step to a kid. -/
  | cons {x y : Nat × Nat} {ys : List (Nat × Nat)} :
      Kid d limits x y → KidPath d limits y ys → KidPath d limits x (y :: ys)

/-- Node `x` is a dictionary whose own inheritable attributes are `a` (rules A1, A2). -/
def NodeAttrs (d : OpenDoc) (limits : Limits) (x : Nat × Nat) (a : Attrs) : Prop :=
  ∃ nd, d.getObject limits x.1 x.2 = .ok (.obj (.dict nd)) ∧ attrsOf d limits nd = .ok a

/-- Node `x` is a leaf (rule W4) with own attributes `a` and own `/Contents` `c` (A7). -/
def LeafNode (d : OpenDoc) (limits : Limits) (x : Nat × Nat) (a : Attrs)
    (c : Option PdfObject) : Prop :=
  ∃ nd, d.getObject limits x.1 x.2 = .ok (.obj (.dict nd)) ∧ attrsOf d limits nd = .ok a ∧
    kindOf nd = .leaf ∧ Dict.get? nd (Name.ofString "Contents") = c

/-- `Descends d limits root anc x`: `x` is reached from `root` along `Kid`; `anc` lists the
proper ancestors of `x` on that path, root-first, each with its own attributes. -/
inductive Descends (d : OpenDoc) (limits : Limits) (root : Nat × Nat) :
    List ((Nat × Nat) × Attrs) → Nat × Nat → Prop
  /-- The root itself. -/
  | root : Descends d limits root [] root
  /-- A kid of a reached node. -/
  | kid {anc : List ((Nat × Nat) × Attrs)} {x y : Nat × Nat} {a : Attrs} :
      Descends d limits root anc x → NodeAttrs d limits x a → Kid d limits x y →
      Descends d limits root (anc ++ [(x, a)]) y

/-- The value of the nearest node that has the attribute, on a root-first path of own
attributes (§7.7.3.4). -/
def nearest {α : Type} (f : Attrs → Option α) (path : List Attrs) : Option α :=
  path.reverse.findSome? f

/-! ## Inheritance by folding -/

/-- **Inheritance law** for `/Resources`. -/
theorem foldl_merge_resources (path : List Attrs) (init : Attrs) :
    (path.foldl Attrs.merge init).resources =
      (path.reverse.findSome? (·.resources)).or init.resources := by
  induction path generalizing init with
  | nil => simp
  | cons a as ih =>
    simp only [List.foldl, ih, List.reverse_cons, List.findSome?_append, Attrs.merge]
    cases h1 : as.reverse.findSome? (·.resources) <;> cases h2 : a.resources <;> simp [h2]

/-- **Inheritance law** for `/CropBox`. -/
theorem foldl_merge_cropBox (path : List Attrs) (init : Attrs) :
    (path.foldl Attrs.merge init).cropBox =
      (path.reverse.findSome? (·.cropBox)).or init.cropBox := by
  induction path generalizing init with
  | nil => simp
  | cons a as ih =>
    simp only [List.foldl, ih, List.reverse_cons, List.findSome?_append, Attrs.merge]
    cases h1 : as.reverse.findSome? (·.cropBox) <;> cases h2 : a.cropBox <;> simp [h2]

/-! ## The walk, step by step -/

/-- A live pop: the stack splits into skipped `null` entries, the popped entry, and the
rest; nothing popped is visited. -/
theorem popLive_some {d : OpenDoc} {limits : Limits} {vis : List Nat} :
    ∀ {s : List Entry} {k k' : Nat} {e : Entry} {b : IndirectBody} {rest : List Entry},
      popLive d limits vis s k = .ok (some (e, b, rest), k') →
      ∃ pre, s = pre ++ e :: rest ∧
        (∀ x ∈ pre, x.num ∉ vis ∧ d.getObject limits x.num x.gen = .ok (.obj .null)) ∧
        e.num ∉ vis ∧ d.getObject limits e.num e.gen = .ok b ∧ b ≠ .obj .null
  | [], _, _, _, _, _, h => by simp [popLive] at h
  | e0 :: s, k, k', e, b, rest, h => by
    unfold popLive at h
    split at h
    · cases h
    · rename_i hn
      split at h
      · cases h
      · rename_i hg
        obtain ⟨pre, hs, hpre, he, hge, hb⟩ := popLive_some h
        refine ⟨e0 :: pre, by simp [hs], ?_, he, hge, hb⟩
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact ⟨hn, hg⟩
        · exact hpre x hx
      · rename_i b0 hnn hg
        cases h
        exact ⟨[], rfl, by simp, hn, hg, fun hb => hnn hb⟩

/-- An empty pop: every entry was skipped, `null` and not visited. -/
theorem popLive_none {d : OpenDoc} {limits : Limits} {vis : List Nat} :
    ∀ {s : List Entry} {k k' : Nat}, popLive d limits vis s k = .ok (none, k') →
      ∀ x ∈ s, x.num ∉ vis ∧ d.getObject limits x.num x.gen = .ok (.obj .null)
  | [], _, _, _ => by simp
  | e0 :: s, k, k', h => by
    unfold popLive at h
    split at h
    · cases h
    · rename_i hn
      split at h
      · cases h
      · rename_i hg
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact ⟨hn, hg⟩
        · exact popLive_none h x hx
      · cases h

/-- What a successful node visit does (rules W4–W6). -/
theorem visitNode_cases {d : OpenDoc} {limits : Limits} {e : Entry} {b : IndirectBody}
    {st st' : WalkState} (h : visitNode d limits e b st = .ok st') :
    ∃ nd own, b = .obj (.dict nd) ∧ attrsOf d limits nd = .ok own ∧
      st'.visited = e.num :: st.visited ∧
      ((∃ ko ks, kindOf nd = .inner ∧ key d limits nd "Kids" = .ok ko ∧ kidsOf ko = some ks ∧
          st'.stack = ks.map (fun r => (⟨r.1, r.2, e.depth + 1, e.inh.merge own⟩ : Entry)) ++
            st.stack ∧ st'.pages = st.pages) ∨
        (kindOf nd = .leaf ∧ st'.stack = st.stack ∧
          st'.pages = mkPage e.num e.gen (e.inh.merge own)
            (Dict.get? nd (Name.ofString "Contents")) :: st.pages)) := by
  unfold visitNode at h
  split at h
  · cases h
  · split at h
    · rename_i nd
      split at h
      · cases h
      · rename_i own ho
        split at h
        · rename_i hk
          split at h
          · cases h
          · rename_i ko hko
            split at h
            · cases h
            · rename_i ks hks
              cases h
              exact ⟨nd, own, rfl, ho, rfl, Or.inl ⟨ko, ks, hk, hko, hks, rfl, rfl⟩⟩
        · rename_i hk
          cases h
          exact ⟨nd, own, rfl, ho, rfl, Or.inr ⟨hk, rfl, rfl⟩⟩
        · cases h
    · cases h

/-- A property of walk states that every pop-and-visit step and the final empty pop
preserve is preserved by the loop. -/
theorem loop_preserves {d : OpenDoc} {limits : Limits} (P : WalkState → Prop)
    (hstep : ∀ (st st' : WalkState) (e : Entry) (b : IndirectBody) (rest : List Entry) (k : Nat),
      P st → popLive d limits st.visited st.stack st.skipped = .ok (some (e, b, rest), k) →
      visitNode d limits e b { st with stack := rest, skipped := k } = .ok st' → P st')
    (hend : ∀ (st : WalkState) (k : Nat), P st →
      popLive d limits st.visited st.stack st.skipped = .ok (none, k) →
      P { st with stack := [], skipped := k }) :
    ∀ {f : Nat} {st st' : WalkState}, P st → loop d limits f st = .ok st' → P st'
  | 0, st, st', hP, h => by
    unfold loop at h
    split at h
    · cases h
    · rename_i k hp
      cases h; exact hend st k hP hp
    · cases h
  | f + 1, st, st', hP, h => by
    unfold loop at h
    split at h
    · cases h
    · rename_i k hp
      cases h; exact hend st k hP hp
    · rename_i e b rest k hpop
      split at h
      · cases h
      · rename_i st1 hv
        exact loop_preserves P hstep hend (hstep _ _ _ _ _ _ hP hpop hv) h

/-! ## (1) Acyclicity -/

/-- A `null` node has no kids. -/
theorem kidPath_of_null {d : OpenDoc} {limits : Limits} {x : Nat × Nat} {ys : List (Nat × Nat)}
    (hx : d.getObject limits x.1 x.2 = .ok (.obj .null)) (hp : KidPath d limits x ys) :
    ys = [] := by
  cases hp with
  | nil => rfl
  | cons hk _ =>
    obtain ⟨_, ⟨nd, _, hg, _⟩, _⟩ := hk
    rw [hx] at hg
    cases hg

/-- **Paths below the stack** (the key lemma of acyclicity): if the loop succeeds, every
descending path from a stack entry has distinct object numbers, none of them visited yet. -/
theorem loop_paths {d : OpenDoc} {limits : Limits} :
    ∀ {f : Nat} {st fin : WalkState}, loop d limits f st = .ok fin →
      ∀ e ∈ st.stack, ∀ ys, KidPath d limits (e.num, e.gen) ys →
        (((e.num, e.gen) :: ys).map Prod.fst).Nodup ∧
          ∀ v ∈ st.visited, v ∉ ((e.num, e.gen) :: ys).map Prod.fst := by
  -- A skipped (null, unvisited) entry: its only path is itself.
  have single : ∀ {vis : List Nat} {e : Entry} {ys : List (Nat × Nat)},
      e.num ∉ vis → d.getObject limits e.num e.gen = .ok (.obj .null) →
      KidPath d limits (e.num, e.gen) ys →
      (((e.num, e.gen) :: ys).map Prod.fst).Nodup ∧
        ∀ v ∈ vis, v ∉ ((e.num, e.gen) :: ys).map Prod.fst := by
    intro vis e ys hn hg hp
    have := kidPath_of_null hg hp
    subst this
    refine ⟨by simp, ?_⟩
    intro v hv hm
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hm
    exact hn (hm ▸ hv)
  intro f
  induction f with
  | zero =>
    intro st fin h
    unfold loop at h
    split at h
    · cases h
    · rename_i k hp
      intro e he ys hpath
      obtain ⟨hn, hg⟩ := popLive_none hp e he
      exact single hn hg hpath
    · cases h
  | succ f ih =>
    intro st fin h
    unfold loop at h
    split at h
    · cases h
    · rename_i k hp
      intro e he ys hpath
      obtain ⟨hn, hg⟩ := popLive_none hp e he
      exact single hn hg hpath
    · rename_i e0 b rest k hpop
      split at h
      · cases h
      · rename_i st' hv
        have IH := ih h
        obtain ⟨pre, hs, hpre, hn0, hg0, -⟩ := popLive_some hpop
        obtain ⟨nd, own, hb, -, hvis, hcase⟩ := visitNode_cases hv
        subst hb
        dsimp only at hvis hcase
        have hrest : ∀ x ∈ rest, x ∈ st'.stack := by
          intro x hx
          rcases hcase with ⟨_, _, _, _, _, hst, _⟩ | ⟨_, hst, _⟩
          · rw [hst]; exact List.mem_append_right _ hx
          · rw [hst]; exact hx
        have hsub : ∀ v ∈ st.visited, v ∈ st'.visited := by
          intro v hv; rw [hvis]; exact List.mem_cons_of_mem _ hv
        intro e he ys hpath
        rw [hs] at he
        rcases List.mem_append.1 he with hep | he
        · obtain ⟨hn, hg⟩ := hpre e hep
          exact single hn hg hpath
        · rcases List.mem_cons.1 he with rfl | her
          · cases hpath with
            | nil =>
              refine ⟨by simp, ?_⟩
              intro v hv hm
              simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
                or_false] at hm
              exact hn0 (hm ▸ hv)
            | @cons _ y ys' hk hp' =>
              obtain ⟨ks, ⟨nd', ko, hg', hk', hko', hks'⟩, hy⟩ := hk
              rw [hg0] at hg'
              cases hg'
              rcases hcase with ⟨ko2, ks2, -, hko2, hks2, hst, -⟩ | ⟨hleaf, -, -⟩
              · rw [hko'] at hko2
                cases hko2
                rw [hks'] at hks2
                cases hks2
                have hmem : (⟨y.1, y.2, e.depth + 1, e.inh.merge own⟩ : Entry) ∈ st'.stack := by
                  rw [hst]
                  exact List.mem_append_left _ (List.mem_map.2 ⟨y, hy, rfl⟩)
                obtain ⟨hnd, hdis⟩ := IH _ hmem ys' hp'
                have h0 : e.num ∉ ((y.1, y.2) :: ys').map Prod.fst :=
                  hdis e.num (by rw [hvis]; exact List.mem_cons_self ..)
                refine ⟨?_, ?_⟩
                · rw [List.map_cons]
                  exact List.nodup_cons.2 ⟨h0, hnd⟩
                · intro v hv hm
                  rw [List.map_cons] at hm
                  rcases List.mem_cons.1 hm with hm | hm
                  · rw [hm] at hv; exact hn0 hv
                  · exact hdis v (hsub v hv) hm
              · rw [hleaf] at hk'
                cases hk'
          · obtain ⟨hnd, hdis⟩ := IH e (hrest e her) ys hpath
            exact ⟨hnd, fun v hv => hdis v (hsub v hv)⟩

/-- **Acyclicity** of a successful walk: every descending path from the root `/Pages` node
visits pairwise distinct object numbers. -/
theorem walk_path_nodup {d : OpenDoc} {limits : Limits} {n g : Nat} {st : WalkState}
    (h : walk d limits n g = .ok st) {ys : List (Nat × Nat)} (hp : KidPath d limits (n, g) ys) :
    (((n, g) :: ys).map Prod.fst).Nodup :=
  (loop_paths (st := initState n g) h ⟨n, g, 0, {}⟩ (List.mem_singleton_self _) ys hp).1

/-- Extend a descending path by a kid of its last node. -/
theorem KidPath.snoc {d : OpenDoc} {limits : Limits} {y : Nat × Nat} :
    ∀ {x : Nat × Nat} {ys : List (Nat × Nat)}, KidPath d limits x ys →
      Kid d limits ((x :: ys).getLast (List.cons_ne_nil _ _)) y →
      KidPath d limits x (ys ++ [y])
  | _, _, .nil _, hk => .cons hk (.nil _)
  | _, _, .cons hxz hz, hk => .cons hxz (KidPath.snoc hz (by simpa using hk))

/-- **Kids are never ancestors**: after a successful walk, no node on a descending path from
the root has a `/Kids` entry with the object number of itself or of one of its ancestors. -/
theorem walk_kid_not_ancestor {d : OpenDoc} {limits : Limits} {n g : Nat} {st : WalkState}
    (h : walk d limits n g = .ok st) {ys : List (Nat × Nat)} {y : Nat × Nat}
    (hp : KidPath d limits (n, g) ys)
    (hk : Kid d limits (((n, g) :: ys).getLast (List.cons_ne_nil _ _)) y) :
    y.1 ∉ ((n, g) :: ys).map Prod.fst := by
  have hnd := walk_path_nodup h (KidPath.snoc hp hk)
  rw [← List.cons_append, List.map_append, List.nodup_append] at hnd
  intro hm
  obtain ⟨-, -, hdis⟩ := hnd
  exact hdis _ hm _ (List.mem_singleton_self _) rfl

/-! ## (2) Inheritance -/

/-- A page as the walk builds it: a leaf reached from `root` along `Kid`, built by `mkPage`
from the fold of the own attributes along its root-to-leaf path. -/
def PageInh (d : OpenDoc) (limits : Limits) (root : Nat × Nat) (p : Page) : Prop :=
  ∃ anc own c, Descends d limits root anc (p.num, p.gen) ∧ LeafNode d limits (p.num, p.gen) own c ∧
    p = mkPage p.num p.gen ((anc.map (·.2) ++ [own]).foldl Attrs.merge {}) c

/-- The inheritance invariant of the walk: every stack entry is reached from `root` and
inherits the fold of its ancestors' attributes; every page satisfies `PageInh`. -/
def InhInv (d : OpenDoc) (limits : Limits) (root : Nat × Nat) (st : WalkState) : Prop :=
  (∀ e ∈ st.stack, ∃ anc, Descends d limits root anc (e.num, e.gen) ∧
      e.inh = (anc.map (·.2)).foldl Attrs.merge {}) ∧
    ∀ p ∈ st.pages, PageInh d limits root p

/-- The loop preserves the inheritance invariant. -/
theorem loop_inhInv {d : OpenDoc} {limits : Limits} {root : Nat × Nat} {f : Nat}
    {st st' : WalkState} (hi : InhInv d limits root st) (h : loop d limits f st = .ok st') :
    InhInv d limits root st' := by
  refine loop_preserves (InhInv d limits root) ?_ ?_ hi h
  · intro st st' e b rest k ⟨hstk, hpg⟩ hpop hv
    obtain ⟨pre, hs, -, -, hge, -⟩ := popLive_some hpop
    obtain ⟨nd, own, hb, ho, -, hcase⟩ := visitNode_cases hv
    subst hb
    dsimp only at hcase
    obtain ⟨anc, hd, hinh⟩ := hstk e (by rw [hs]; simp)
    have hrest : ∀ x ∈ rest, x ∈ st.stack := by intro x hx; rw [hs]; simp [hx]
    have hna : NodeAttrs d limits (e.num, e.gen) own := ⟨nd, hge, ho⟩
    have hmerge : e.inh.merge own =
        ((anc ++ [((e.num, e.gen), own)]).map (·.2)).foldl Attrs.merge {} := by
      simp [hinh, List.foldl_append]
    rcases hcase with ⟨ko, ks, hk, hko, hks, hst, hpp⟩ | ⟨hk, hst, hpp⟩
    · refine ⟨?_, ?_⟩
      · intro x hx
        rw [hst] at hx
        rcases List.mem_append.1 hx with hx | hx
        · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
          exact ⟨_, Descends.kid hd hna ⟨ks, ⟨nd, ko, hge, hk, hko, hks⟩, hr⟩, hmerge⟩
        · exact hstk x (hrest x hx)
      · rw [hpp]; exact hpg
    · refine ⟨?_, ?_⟩
      · intro x hx; rw [hst] at hx; exact hstk x (hrest x hx)
      · intro p hp
        rw [hpp] at hp
        rcases List.mem_cons.1 hp with rfl | hp
        · refine ⟨anc, own, _, hd, ⟨nd, hge, ho, hk, rfl⟩, ?_⟩
          show mkPage e.num e.gen (e.inh.merge own) _ = mkPage e.num e.gen _ _
          rw [hmerge]; simp
        · exact hpg p hp
  · intro st k ⟨_, hpg⟩ _
    exact ⟨by simp, hpg⟩

/-- Every page of a successful walk satisfies `PageInh` for the walk's root. -/
theorem walk_pageInh {d : OpenDoc} {limits : Limits} {n g : Nat} {st : WalkState}
    (h : walk d limits n g = .ok st) : ∀ p ∈ st.pages, PageInh d limits (n, g) p :=
  (loop_inhInv (st := initState n g)
    ⟨by
      intro e he
      simp only [initState, List.mem_singleton] at he
      subst he
      exact ⟨[], Descends.root, rfl⟩,
     by simp [initState]⟩ h).2

/-- **Inheritance law on pages** (§7.7.3.4): a page satisfying `PageInh` is a leaf at the end
of a root-to-leaf path, and each attribute is the nearest one on that path, else the
default. -/
theorem PageInh.fields {d : OpenDoc} {limits : Limits} {root : Nat × Nat} {p : Page}
    (h : PageInh d limits root p) :
    ∃ anc own c, Descends d limits root anc (p.num, p.gen) ∧
      LeafNode d limits (p.num, p.gen) own c ∧
      p.mediaBox = (nearest (·.mediaBox) (anc.map (·.2) ++ [own])).getD letter ∧
      p.mediaBoxDefaulted = (nearest (·.mediaBox) (anc.map (·.2) ++ [own])).isNone ∧
      p.cropBox = cropOf (nearest (·.cropBox) (anc.map (·.2) ++ [own]))
        ((nearest (·.mediaBox) (anc.map (·.2) ++ [own])).getD letter) ∧
      p.rotate = (nearest (·.rotate) (anc.map (·.2) ++ [own])).getD .r0 ∧
      p.resources = nearest (·.resources) (anc.map (·.2) ++ [own]) ∧
      p.contents = c := by
  obtain ⟨anc, own, c, hd, hl, hp⟩ := h
  refine ⟨anc, own, c, hd, hl, ?_⟩
  have hm := foldl_merge_mediaBox (anc.map (·.2) ++ [own]) {}
  have hc := foldl_merge_cropBox (anc.map (·.2) ++ [own]) {}
  have hr := foldl_merge_rotate (anc.map (·.2) ++ [own]) {}
  have hs := foldl_merge_resources (anc.map (·.2) ++ [own]) {}
  simp only [Option.or_none] at hm hc hr hs
  rw [hp]
  simp only [mkPage, nearest, hm, hc, hr, hs, and_self]

/-- **Inheritance law** for the pages of a successful walk. -/
theorem walk_page_inherit {d : OpenDoc} {limits : Limits} {n g : Nat} {st : WalkState}
    (h : walk d limits n g = .ok st) {p : Page} (hp : p ∈ st.pages) :
    ∃ anc own c, Descends d limits (n, g) anc (p.num, p.gen) ∧
      LeafNode d limits (p.num, p.gen) own c ∧
      p.mediaBox = (nearest (·.mediaBox) (anc.map (·.2) ++ [own])).getD letter ∧
      p.mediaBoxDefaulted = (nearest (·.mediaBox) (anc.map (·.2) ++ [own])).isNone ∧
      p.cropBox = cropOf (nearest (·.cropBox) (anc.map (·.2) ++ [own]))
        ((nearest (·.mediaBox) (anc.map (·.2) ++ [own])).getD letter) ∧
      p.rotate = (nearest (·.rotate) (anc.map (·.2) ++ [own])).getD .r0 ∧
      p.resources = nearest (·.resources) (anc.map (·.2) ++ [own]) ∧
      p.contents = c :=
  (walk_pageInh h p hp).fields

/-! ## (3) Fuel -/

/-- A key found by binary search is a key of the array. -/
theorem bsearch_key (a : Array (Nat × Core.Xref.XrefEntry)) (n lo hi : Nat)
    {e : Core.Xref.XrefEntry} (h : Core.Open.bsearch a n lo hi = some e) :
    n ∈ a.toList.map Prod.fst := by
  rw [Core.Open.bsearch.eq_def] at h
  split at h
  · split at h
    · cases h
    · rename_i k e' hm
      split at h
      · rename_i hk
        subst hk
        rw [← Array.getElem?_toList] at hm
        exact List.mem_map.2 ⟨(k, e'), List.mem_of_getElem? hm, rfl⟩
      · split at h
        · exact bsearch_key a n _ hi h
        · exact bsearch_key a n lo _ h
  · cases h
termination_by hi - lo
decreasing_by all_goals omega

/-- A non-null object has an xref entry: its number is a key of the index. -/
theorem getObject_ne_null_key {d : OpenDoc} {limits : Limits} {num gen : Nat}
    {b : IndirectBody} (h : d.getObject limits num gen = .ok b) (hb : b ≠ .obj .null) :
    num ∈ d.index.toList.map Prod.fst := by
  unfold OpenDoc.getObject OpenDoc.getObjectTrace at h
  cases hl : d.lookup num with
  | none =>
    simp only [hl, Except.ok.injEq] at h
    exact absurd h.symm (by simpa [Core.Open.nullBody] using hb)
  | some x =>
    unfold OpenDoc.lookup at hl
    exact bsearch_key _ _ _ _ hl

/-- At most `objectCount` distinct index keys. -/
theorem fresh_bound {d : OpenDoc} {vis : List Nat} {x : Nat} (hnd : vis.Nodup)
    (hk : ∀ v ∈ vis, v ∈ d.index.toList.map Prod.fst) (hx : x ∉ vis)
    (hxk : x ∈ d.index.toList.map Prod.fst) : vis.length + 1 ≤ d.objectCount := by
  have h := (List.nodup_cons.2 ⟨hx, hnd⟩).length_le_of_subset (l₂ := d.index.toList.map Prod.fst)
    (by
      intro v hv
      rcases List.mem_cons.1 hv with rfl | hv
      · exact hxk
      · exact hk v hv)
  simpa [OpenDoc.objectCount] using h

/-- **Fuel exhaustion is unreachable**: once `objectCount` distinct index keys are visited,
no live entry can be popped. -/
theorem popLive_exhausted {d : OpenDoc} {limits : Limits} {st : WalkState}
    (hnd : st.visited.Nodup) (hk : ∀ v ∈ st.visited, v ∈ d.index.toList.map Prod.fst)
    (hlen : d.objectCount ≤ st.visited.length) {k : Nat} {e : Entry} {b : IndirectBody}
    {rest : List Entry} :
    popLive d limits st.visited st.stack st.skipped ≠ .ok (some (e, b, rest), k) := by
  intro hp
  obtain ⟨-, -, -, hn, hg, hb⟩ := popLive_some hp
  have := fresh_bound hnd hk hn (getObject_ne_null_key hg hb)
  omega

/-- **Fuel is irrelevant** from any state whose visited numbers are distinct index keys and
whose fuel covers the keys not yet visited: more fuel gives the same result. -/
theorem loop_fuel_irrelevant {d : OpenDoc} {limits : Limits} :
    ∀ (f k : Nat) (st : WalkState), st.visited.Nodup →
      (∀ v ∈ st.visited, v ∈ d.index.toList.map Prod.fst) →
      d.objectCount ≤ st.visited.length + f →
      loop d limits f st = loop d limits (f + k) st
  | 0, 0, _, _, _, _ => rfl
  | 0, k + 1, st, hnd, hk, hlen => by
    rw [Nat.zero_add]
    simp only [loop]
    cases hp : popLive d limits st.visited st.stack st.skipped with
    | error x => rfl
    | ok r =>
      rcases r with ⟨_ | ⟨e, b, rest⟩, kk⟩
      · rfl
      · exact absurd hp (popLive_exhausted hnd hk (by omega))
  | f + 1, k, st, hnd, hk, hlen => by
    rw [show f + 1 + k = (f + k) + 1 by omega]
    simp only [loop]
    cases hp : popLive d limits st.visited st.stack st.skipped with
    | error x => rfl
    | ok r =>
      rcases r with ⟨_ | ⟨e, b, rest⟩, kk⟩
      · rfl
      · dsimp only
        cases hv : visitNode d limits e b { st with stack := rest, skipped := kk } with
        | error x => rfl
        | ok st' =>
          dsimp only
          obtain ⟨-, -, -, hn, hg, hb⟩ := popLive_some hp
          have hvis := (visitNode_ok hv).1
          dsimp only at hvis
          apply loop_fuel_irrelevant f k st'
          · rw [hvis]; exact List.nodup_cons.2 ⟨hn, hnd⟩
          · rw [hvis]
            intro v hv'
            rcases List.mem_cons.1 hv' with rfl | hv'
            · exact getObject_ne_null_key hg hb
            · exact hk v hv'
          · rw [hvis, List.length_cons]; omega

/-- **The walk never runs out of its own fuel**: `walk` equals the loop with any larger
fuel. So `limitExceeded .objects` from `walk` never comes from the fuel-exhaustion branch of
`loop` (`popLive_exhausted`), only from `getObject`. -/
theorem walk_fuel_irrelevant (d : OpenDoc) (limits : Limits) (n g k : Nat) :
    walk d limits n g = loop d limits (d.objectCount + k) (initState n g) :=
  loop_fuel_irrelevant _ k _ List.nodup_nil (by simp [initState]) (by simp [initState])

/-! ## The document: `ofOpen` and `openDoc` -/

/-- `ofOpen` on success: the catalog's `/Pages` reference is `doc.pagesRef`, and the pages
are those of the successful walk from it. -/
theorem ofOpen_ok_root {limits : Limits} {d : OpenDoc} {doc : Doc}
    (h : ofOpen limits d = .ok doc) :
    ∃ st, walk d limits doc.pagesRef.1 doc.pagesRef.2 = .ok st ∧
      doc.pages = st.pages.reverse.toArray ∧ doc.file = d ∧
      ∃ rn rg cat, d.trailer.root? = some (rn, rg) ∧
        d.getObject limits rn rg = .ok (.obj (.dict cat)) ∧
        Dict.get? cat (Name.ofString "Pages") = some (.ref doc.pagesRef.1 doc.pagesRef.2) := by
  unfold ofOpen at h
  split at h
  · cases h
  · rename_i rn rg hroot
    split at h
    · cases h
    · rename_i cat hcat
      split at h
      · rename_i pn pg hpg
        split at h
        · cases h
        · rename_i st hw
          cases h
          exact ⟨st, hw, rfl, rfl, rn, rg, cat, hroot, hcat, hpg⟩
      · cases h
    · cases h

/-- `openDoc` on success is `ofOpen` of the opened file. -/
theorem openDoc_ok {limits : Limits} {bytes : ByteArray} {doc : Doc}
    (h : openDoc limits bytes = .ok doc) :
    Core.Open.openFile limits bytes = .ok doc.file ∧ ofOpen limits doc.file = .ok doc := by
  unfold openDoc at h
  split at h
  · cases h
  · rename_i d hd
    obtain ⟨-, -, -, hf, -⟩ := ofOpen_ok_root h
    rw [hf]
    exact ⟨hd, h⟩

/-- **Acyclicity** (Plan.md §5.2): in a document opened by `ofOpen`, every descending path
from the root `/Pages` node has pairwise distinct object numbers. -/
theorem ofOpen_path_nodup {limits : Limits} {d : OpenDoc} {doc : Doc}
    (h : ofOpen limits d = .ok doc) {ys : List (Nat × Nat)}
    (hp : KidPath d limits doc.pagesRef ys) : ((doc.pagesRef :: ys).map Prod.fst).Nodup := by
  obtain ⟨st, hw, -⟩ := ofOpen_ok_root h
  exact walk_path_nodup hw hp

/-- **Acyclicity** for `openDoc`. -/
theorem openDoc_path_nodup {limits : Limits} {bytes : ByteArray} {doc : Doc}
    (h : openDoc limits bytes = .ok doc) {ys : List (Nat × Nat)}
    (hp : KidPath doc.file limits doc.pagesRef ys) :
    ((doc.pagesRef :: ys).map Prod.fst).Nodup :=
  ofOpen_path_nodup (openDoc_ok h).2 hp

/-- **A `/Kids` cycle makes `ofOpen` fail**: if the catalog's `/Pages` node `(pn, pg)` has a
descending path `ys` whose last node has a kid `y` with the object number of a node on the
path (itself or an ancestor), `ofOpen` returns an error. (The error is not necessarily
`Error.cycle`: another node may fail first.) -/
theorem ofOpen_cycle_error {limits : Limits} {d : OpenDoc} {rn rg pn pg : Nat} {cat : Dict}
    {ys : List (Nat × Nat)} {y : Nat × Nat}
    (hroot : d.trailer.root? = some (rn, rg))
    (hcat : d.getObject limits rn rg = .ok (.obj (.dict cat)))
    (hpages : Dict.get? cat (Name.ofString "Pages") = some (.ref pn pg))
    (hp : KidPath d limits (pn, pg) ys)
    (hk : Kid d limits (((pn, pg) :: ys).getLast (List.cons_ne_nil _ _)) y)
    (hy : y.1 ∈ ((pn, pg) :: ys).map Prod.fst) :
    ∃ e, ofOpen limits d = .error e := by
  cases hr : ofOpen limits d with
  | error e => exact ⟨e, rfl⟩
  | ok doc =>
    exfalso
    obtain ⟨st, hw, -, -, rn', rg', cat', hroot', hcat', hpg'⟩ := ofOpen_ok_root hr
    rw [hroot] at hroot'
    cases hroot'
    rw [hcat] at hcat'
    cases hcat'
    rw [hpages] at hpg'
    cases hpg'
    exact walk_kid_not_ancestor hw hp hk hy

/-- **A `/Kids` cycle makes `openDoc` fail** (the file opens, its catalog's `/Pages` node
reaches a node whose `/Kids` contains itself or an ancestor). -/
theorem openDoc_cycle_error {limits : Limits} {bytes : ByteArray} {d : OpenDoc}
    {rn rg pn pg : Nat} {cat : Dict} {ys : List (Nat × Nat)} {y : Nat × Nat}
    (hopen : Core.Open.openFile limits bytes = .ok d)
    (hroot : d.trailer.root? = some (rn, rg))
    (hcat : d.getObject limits rn rg = .ok (.obj (.dict cat)))
    (hpages : Dict.get? cat (Name.ofString "Pages") = some (.ref pn pg))
    (hp : KidPath d limits (pn, pg) ys)
    (hk : Kid d limits (((pn, pg) :: ys).getLast (List.cons_ne_nil _ _)) y)
    (hy : y.1 ∈ ((pn, pg) :: ys).map Prod.fst) :
    ∃ e, openDoc limits bytes = .error e := by
  obtain ⟨e, he⟩ := ofOpen_cycle_error hroot hcat hpages hp hk hy
  exact ⟨e, by simp [openDoc, hopen, he]⟩

/-- **Inheritance law on the pages of a document** (§7.7.3.4): every page of `doc` is a leaf
reached from the root `/Pages` node along `Kid`; its MediaBox, CropBox, Rotate and Resources
are those of the nearest node on that root-to-leaf path that has the attribute (Letter, the
MediaBox clipped as rule A6, `0`, none if no node has it), and its `/Contents` is the leaf's. -/
theorem ofOpen_page_inherit {limits : Limits} {d : OpenDoc} {doc : Doc}
    (h : ofOpen limits d = .ok doc) {p : Page} (hp : p ∈ doc.pages.toList) :
    ∃ anc own c, Descends d limits doc.pagesRef anc (p.num, p.gen) ∧
      LeafNode d limits (p.num, p.gen) own c ∧
      p.mediaBox = (nearest (·.mediaBox) (anc.map (·.2) ++ [own])).getD letter ∧
      p.mediaBoxDefaulted = (nearest (·.mediaBox) (anc.map (·.2) ++ [own])).isNone ∧
      p.cropBox = cropOf (nearest (·.cropBox) (anc.map (·.2) ++ [own]))
        ((nearest (·.mediaBox) (anc.map (·.2) ++ [own])).getD letter) ∧
      p.rotate = (nearest (·.rotate) (anc.map (·.2) ++ [own])).getD .r0 ∧
      p.resources = nearest (·.resources) (anc.map (·.2) ++ [own]) ∧
      p.contents = c := by
  obtain ⟨st, hw, hpg, -⟩ := ofOpen_ok_root h
  rw [hpg, List.toList_toArray, List.mem_reverse] at hp
  exact walk_page_inherit hw hp

/-- **Inheritance law** for `openDoc`. -/
theorem openDoc_page_inherit {limits : Limits} {bytes : ByteArray} {doc : Doc}
    (h : openDoc limits bytes = .ok doc) {p : Page} (hp : p ∈ doc.pages.toList) :
    ∃ anc own c, Descends doc.file limits doc.pagesRef anc (p.num, p.gen) ∧
      LeafNode doc.file limits (p.num, p.gen) own c ∧
      p.mediaBox = (nearest (·.mediaBox) (anc.map (·.2) ++ [own])).getD letter ∧
      p.mediaBoxDefaulted = (nearest (·.mediaBox) (anc.map (·.2) ++ [own])).isNone ∧
      p.cropBox = cropOf (nearest (·.cropBox) (anc.map (·.2) ++ [own]))
        ((nearest (·.mediaBox) (anc.map (·.2) ++ [own])).getD letter) ∧
      p.rotate = (nearest (·.rotate) (anc.map (·.2) ++ [own])).getD .r0 ∧
      p.resources = nearest (·.resources) (anc.map (·.2) ++ [own]) ∧
      p.contents = c :=
  ofOpen_page_inherit (openDoc_ok h).2 hp

end SafePdf.Spec.PageTree
