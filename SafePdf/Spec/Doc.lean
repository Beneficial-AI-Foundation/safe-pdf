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
   fail (`walk_kid_not_ancestor`, `ofOpen_cycle_error`, `openDoc_cycle_error`). Without
   further hypotheses the error kind is not pinned: another node popped earlier may fail first
   (malformed, depth, fetch error); theorem 5 pins it for well-formed trees.
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
4. **Unique paths** (task 4.1c; `loop_forest`, `walk_descends_unique`,
   `ofOpen_descends_unique`, `ofOpen_page_path_unique`, `openDoc_page_path_unique`): after a
   successful open, every live (non-`null`, `Live`) node, in particular every page, has
   exactly one `Descends` path from the root, so the "nearest node" of theorem 2 is well
   defined. Key invariant (`Forest`): if the loop succeeds, the stack entries have unique live
   paths below them and reach pairwise disjoint sets of live object numbers (`Separated`).
   Dangling (`null`) references may be shared: they are skipped, not visited (rule W3).
5. **The cycle error kind** (task 4.1c; `walk_ok_or_cycle`, `walk_cycle_error`,
   `walk_shared_error`, `ofOpen_cycle_error_kind`, `openDoc_cycle_error_kind`,
   `ofOpen_shared_error`, `openDoc_shared_error`): if the tree below the root is well formed
   (`WellFormedTree`: every node reached along a path of distinct object numbers is `null` or
   a dictionary within the depth limit whose attributes resolve and whose kind is a leaf or an
   intermediate node with valid `/Kids`; `NodeOK`), the walk fails only with `Error.cycle`.
   So a `/Kids` edge to the node itself or an ancestor, or a live node shared by two paths,
   makes `openDoc` fail with `Error.cycle` specifically.
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


/-! ## (4) Uniqueness of root-to-node paths (task 4.1c) -/

/-- `PathTo d limits x ys z`: `x :: ys` is a descending path along `Kid` that ends at `z`. -/
inductive PathTo (d : OpenDoc) (limits : Limits) :
    Nat × Nat → List (Nat × Nat) → Nat × Nat → Prop
  /-- The one-node path. -/
  | nil (x : Nat × Nat) : PathTo d limits x [] x
  /-- Step to a kid. -/
  | cons {x y z : Nat × Nat} {ys : List (Nat × Nat)} :
      Kid d limits x y → PathTo d limits y ys z → PathTo d limits x (y :: ys) z

/-- A `PathTo` is a `KidPath`. -/
theorem PathTo.kidPath {d : OpenDoc} {limits : Limits} :
    ∀ {x z : Nat × Nat} {ys : List (Nat × Nat)}, PathTo d limits x ys z → KidPath d limits x ys
  | _, _, _, .nil _ => .nil _
  | _, _, _, .cons hk hp => .cons hk hp.kidPath

/-- The end of a path is on the path. -/
theorem PathTo.mem {d : OpenDoc} {limits : Limits} :
    ∀ {x z : Nat × Nat} {ys : List (Nat × Nat)}, PathTo d limits x ys z → z ∈ x :: ys
  | _, _, _, .nil _ => List.mem_cons_self ..
  | _, _, _, .cons _ hp => List.mem_cons_of_mem _ hp.mem

/-- Extend a path by a kid of its end. -/
theorem PathTo.snoc {d : OpenDoc} {limits : Limits} {y : Nat × Nat} :
    ∀ {x z : Nat × Nat} {ys : List (Nat × Nat)}, PathTo d limits x ys z → Kid d limits z y →
      PathTo d limits x (ys ++ [y]) y
  | _, _, _, .nil _, hk => .cons hk (.nil _)
  | _, _, _, .cons hxz hp, hk => .cons hxz (hp.snoc hk)

/-- Node `x` is **live**: its object is not `null` (a dangling reference, rule W3, is not
live). -/
def Live (d : OpenDoc) (limits : Limits) (x : Nat × Nat) : Prop :=
  d.getObject limits x.1 x.2 ≠ .ok (.obj .null)

/-- From a `null` node the only path is the node itself. -/
theorem pathTo_of_null {d : OpenDoc} {limits : Limits} {x z : Nat × Nat}
    {ys : List (Nat × Nat)} (hx : d.getObject limits x.1 x.2 = .ok (.obj .null))
    (hp : PathTo d limits x ys z) : ys = [] ∧ z = x := by
  cases hp with
  | nil => exact ⟨rfl, rfl⟩
  | cons hk _ =>
    obtain ⟨_, ⟨nd, _, hg, _⟩, _⟩ := hk
    rw [hx] at hg
    cases hg

/-- The kids of a node are its resolved `/Kids`. -/
theorem kid_mem {d : OpenDoc} {limits : Limits} {x y : Nat × Nat} {nd : Dict} {ko : PdfObject}
    {ks : List (Nat × Nat)} (hg : d.getObject limits x.1 x.2 = .ok (.obj (.dict nd)))
    (hko : key d limits nd "Kids" = .ok ko) (hks : kidsOf ko = some ks) (hk : Kid d limits x y) :
    y ∈ ks := by
  obtain ⟨ks', ⟨nd', ko', hg', -, hko', hks'⟩, hy⟩ := hk
  rw [hg] at hg'
  cases hg'
  rw [hko] at hko'
  cases hko'
  rw [hks] at hks'
  cases hks'
  exact hy

/-- A leaf has no kids. -/
theorem pathTo_of_leaf {d : OpenDoc} {limits : Limits} {x z : Nat × Nat} {nd : Dict}
    {ys : List (Nat × Nat)} (hg : d.getObject limits x.1 x.2 = .ok (.obj (.dict nd)))
    (hl : kindOf nd = .leaf) (hp : PathTo d limits x ys z) : ys = [] ∧ z = x := by
  cases hp with
  | nil => exact ⟨rfl, rfl⟩
  | cons hk _ =>
    obtain ⟨_, ⟨nd', _, hg', hk', _⟩, _⟩ := hk
    rw [hg] at hg'
    cases hg'
    rw [hl] at hk'
    cases hk'

/-- All live paths from `x` ending at the same object number are the same path. -/
def UniquePaths (d : OpenDoc) (limits : Limits) (x : Nat × Nat) : Prop :=
  ∀ ys zs z z', PathTo d limits x ys z → PathTo d limits x zs z' → Live d limits z →
    Live d limits z' → z.1 = z'.1 → ys = zs

/-- No live node reachable from `x` has the object number of a live node reachable from
`y`. -/
def Apart (d : OpenDoc) (limits : Limits) (x y : Nat × Nat) : Prop :=
  ∀ ys zs z z', PathTo d limits x ys z → PathTo d limits y zs z' → Live d limits z →
    Live d limits z' → z.1 ≠ z'.1

/-- The nodes of a list (a walk stack) reach pairwise disjoint sets of live object numbers,
position by position. -/
def Separated (d : OpenDoc) (limits : Limits) : List (Nat × Nat) → Prop
  | [] => True
  | x :: l => (∀ y ∈ l, Apart d limits x y) ∧ Separated d limits l

/-- A **forest** of stack entries: unique live paths below each, disjoint live subtrees. -/
def Forest (d : OpenDoc) (limits : Limits) (l : List (Nat × Nat)) : Prop :=
  (∀ x ∈ l, UniquePaths d limits x) ∧ Separated d limits l

/-- `Apart` is symmetric. -/
theorem Apart.symm {d : OpenDoc} {limits : Limits} {x y : Nat × Nat} (h : Apart d limits x y) :
    Apart d limits y x :=
  fun ys zs z z' hy hx lz lz' he => h zs ys z' z hx hy lz' lz he.symm

/-- A `null` node is apart from everything. -/
theorem apart_of_null {d : OpenDoc} {limits : Limits} {x y : Nat × Nat}
    (hx : d.getObject limits x.1 x.2 = .ok (.obj .null)) : Apart d limits x y := by
  intro ys zs z z' hp _ lz _ _
  obtain ⟨-, rfl⟩ := pathTo_of_null hx hp
  exact lz hx

/-- A `null` node has unique paths. -/
theorem uniquePaths_of_null {d : OpenDoc} {limits : Limits} {x : Nat × Nat}
    (hx : d.getObject limits x.1 x.2 = .ok (.obj .null)) : UniquePaths d limits x := by
  intro ys zs z z' h1 h2 _ _ _
  rw [(pathTo_of_null hx h1).1, (pathTo_of_null hx h2).1]

/-- Prefixing `null` nodes keeps a forest. -/
theorem forest_append_null {d : OpenDoc} {limits : Limits} {b : List (Nat × Nat)}
    (hb : Forest d limits b) :
    ∀ {a : List (Nat × Nat)}, (∀ x ∈ a, d.getObject limits x.1 x.2 = .ok (.obj .null)) →
      Forest d limits (a ++ b)
  | [], _ => hb
  | x :: a, ha => by
    have ih := forest_append_null hb (a := a) (fun y hy => ha y (List.mem_cons_of_mem _ hy))
    have hx := ha x (List.mem_cons_self ..)
    refine ⟨?_, ?_⟩
    · intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact uniquePaths_of_null hx
      · exact ih.1 y hy
    · exact ⟨fun y _ => apart_of_null hx, ih.2⟩

/-- A forest built from a head and a forest. -/
theorem forest_cons {d : OpenDoc} {limits : Limits} {x : Nat × Nat} {l : List (Nat × Nat)}
    (hx : UniquePaths d limits x) (ha : ∀ y ∈ l, Apart d limits x y) (hl : Forest d limits l) :
    Forest d limits (x :: l) := by
  refine ⟨?_, ha, hl.2⟩
  intro y hy
  rcases List.mem_cons.1 hy with rfl | hy
  · exact hx
  · exact hl.1 y hy

/-- The right part of a separated list is separated. -/
theorem separated_append_right {d : OpenDoc} {limits : Limits} {b : List (Nat × Nat)} :
    ∀ {a : List (Nat × Nat)}, Separated d limits (a ++ b) → Separated d limits b
  | [], h => h
  | _ :: _, h => separated_append_right h.2

/-- In a separated list, a node of the left part is apart from a node of the right part. -/
theorem separated_append_apart {d : OpenDoc} {limits : Limits} {b : List (Nat × Nat)}
    {y : Nat × Nat} (hy : y ∈ b) :
    ∀ {a : List (Nat × Nat)} {x : Nat × Nat}, Separated d limits (a ++ b) → x ∈ a →
      Apart d limits x y
  | [], _, _, hx => by cases hx
  | c :: a, x, h, hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1 y (List.mem_append_right _ hy)
    · exact separated_append_apart hy h.2 hx

/-- In a separated list, two members reaching the same live object number are equal. -/
theorem separated_mem_eq {d : OpenDoc} {limits : Limits} {ys zs : List (Nat × Nat)}
    {z z' : Nat × Nat} (lz : Live d limits z) (lz' : Live d limits z') (he : z.1 = z'.1) :
    ∀ {l : List (Nat × Nat)} {x y : Nat × Nat}, Separated d limits l → x ∈ l → y ∈ l →
      PathTo d limits x ys z → PathTo d limits y zs z' → x = y
  | [], _, _, _, hx, _, _, _ => by cases hx
  | c :: l, x, y, h, hx, hy, hpx, hpy => by
    rcases List.mem_cons.1 hx with rfl | hx' <;> rcases List.mem_cons.1 hy with rfl | hy'
    · rfl
    · exact absurd he (h.1 y hy' ys zs z z' hpx hpy lz lz')
    · exact absurd he.symm (h.1 x hx' zs ys z' z hpy hpx lz' lz)
    · exact separated_mem_eq lz lz' he h.2 hx' hy' hpx hpy

/-- The stack as pairs. -/
theorem map_pair_kids (ks : List (Nat × Nat)) (dep : Nat) (inh : Attrs) :
    (ks.map (fun r => (⟨r.1, r.2, dep, inh⟩ : Entry))).map (fun e => (e.num, e.gen)) = ks := by
  induction ks with
  | nil => rfl
  | cons r ks ih => simp only [List.map_cons, ih]

/-- **The stack is a forest** (key lemma of path uniqueness): if the loop succeeds, the
entries of the stack have unique live paths below them and reach pairwise disjoint sets of
live object numbers. -/
theorem loop_forest {d : OpenDoc} {limits : Limits} :
    ∀ {f : Nat} {st fin : WalkState}, loop d limits f st = .ok fin →
      Forest d limits (st.stack.map fun e => (e.num, e.gen)) := by
  have allNull : ∀ {s : List Entry},
      (∀ x ∈ s, d.getObject limits x.num x.gen = .ok (.obj .null)) →
      Forest d limits (s.map fun e => (e.num, e.gen)) := by
    intro s hs
    have := forest_append_null (d := d) (limits := limits) (b := []) ⟨by simp, trivial⟩
      (a := s.map fun e => (e.num, e.gen)) (by
        intro x hx
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        exact hs y hy)
    simpa using this
  intro f
  induction f with
  | zero =>
    intro st fin h
    unfold loop at h
    split at h
    · cases h
    · rename_i k hp
      exact allNull fun x hx => (popLive_none hp x hx).2
    · cases h
  | succ f ih =>
    intro st fin h
    unfold loop at h
    split at h
    · cases h
    · rename_i k hp
      exact allNull fun x hx => (popLive_none hp x hx).2
    · rename_i e0 b rest k hpop
      split at h
      · cases h
      · rename_i st' hv
        have IH := ih h
        have hpaths := loop_paths h
        obtain ⟨pre, hs, hpre, -, hg0, -⟩ := popLive_some hpop
        obtain ⟨nd, own, hb, -, hvis, hcase⟩ := visitNode_cases hv
        subst hb
        dsimp only at hvis hcase
        have hev : e0.num ∈ st'.visited := by rw [hvis]; exact List.mem_cons_self ..
        -- No path below a stack entry of `st'` ends at `e0`'s number.
        have avoid : ∀ x ∈ st'.stack, ∀ ys z, PathTo d limits (x.num, x.gen) ys z →
            z.1 ≠ e0.num := by
          intro x hx ys z hp hz
          exact (hpaths x hx ys hp.kidPath).2 e0.num hev (hz ▸ List.mem_map_of_mem hp.mem)
        have prefNull : ∀ x ∈ pre.map (fun e => (e.num, e.gen)),
            d.getObject limits x.1 x.2 = .ok (.obj .null) := by
          intro x hx
          obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
          exact (hpre y hy).2
        rw [hs, List.map_append, List.map_cons]
        refine forest_append_null ?_ prefNull
        rcases hcase with ⟨ko, ks, hk, hko, hks, hst, -⟩ | ⟨hleaf, hst, -⟩
        · -- An intermediate node: its subtree is itself plus its kids' subtrees.
          have hF : Forest d limits (ks ++ rest.map fun e => (e.num, e.gen)) := by
            have := IH
            rw [hst, List.map_append, map_pair_kids] at this
            exact this
          have avoidK : ∀ y ∈ ks, ∀ ys z, PathTo d limits y ys z → z.1 ≠ e0.num := by
            intro y hy ys z hp
            exact avoid ⟨y.1, y.2, e0.depth + 1, e0.inh.merge own⟩
              (by rw [hst]; exact List.mem_append_left _ (List.mem_map.2 ⟨y, hy, rfl⟩)) ys z hp
          have avoidR : ∀ y ∈ rest.map (fun e => (e.num, e.gen)), ∀ ys z,
              PathTo d limits y ys z → z.1 ≠ e0.num := by
            intro y hy ys z hp
            obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
            exact avoid x (by rw [hst]; exact List.mem_append_right _ hx) ys z hp
          refine forest_cons ?_ ?_ (⟨fun x hx => hF.1 x (List.mem_append_right _ hx),
            separated_append_right hF.2⟩)
          · intro ys zs z z' h1 h2 lz lz' he
            cases h1 with
            | nil =>
              cases h2 with
              | nil => rfl
              | cons hk2 hp2 => exact absurd he.symm (avoidK _ (kid_mem hg0 hko hks hk2) _ _ hp2)
            | cons hk1 hp1 =>
              cases h2 with
              | nil => exact absurd he (avoidK _ (kid_mem hg0 hko hks hk1) _ _ hp1)
              | cons hk2 hp2 =>
                have m1 := List.mem_append_left (rest.map fun e => (e.num, e.gen))
                  (kid_mem hg0 hko hks hk1)
                have m2 := List.mem_append_left (rest.map fun e => (e.num, e.gen))
                  (kid_mem hg0 hko hks hk2)
                have hyy := separated_mem_eq lz lz' he hF.2 m1 m2 hp1 hp2
                subst hyy
                rw [hF.1 _ m1 _ _ _ _ hp1 hp2 lz lz' he]
          · intro y hy ys zs z z' h1 h2 lz lz' he
            cases h1 with
            | nil => exact avoidR y hy zs z' h2 he.symm
            | cons hk1 hp1 =>
              exact separated_append_apart hy hF.2 (kid_mem hg0 hko hks hk1) _ _ _ _ hp1 h2
                lz lz' he
        · -- A leaf: its subtree is itself.
          have hF : Forest d limits (rest.map fun e => (e.num, e.gen)) := by
            have := IH; rw [hst] at this; exact this
          refine forest_cons ?_ ?_ hF
          · intro ys zs z z' h1 h2 _ _ _
            rw [(pathTo_of_leaf hg0 hleaf h1).1, (pathTo_of_leaf hg0 hleaf h2).1]
          · intro y hy ys zs z z' h1 h2 _ _ he
            obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
            obtain ⟨-, rfl⟩ := pathTo_of_leaf hg0 hleaf h1
            exact avoid x (by rw [hst]; exact hx) zs z' h2 he.symm

/-- A `Descends` path is a `PathTo` path through the listed ancestors. -/
theorem Descends.pathTo {d : OpenDoc} {limits : Limits} {root : Nat × Nat} :
    ∀ {anc : List ((Nat × Nat) × Attrs)} {x : Nat × Nat}, Descends d limits root anc x →
      ∃ ys, PathTo d limits root ys x ∧ root :: ys = anc.map (·.1) ++ [x]
  | _, _, .root => ⟨[], .nil _, rfl⟩
  | _, _, .kid hd _ hk => by
    obtain ⟨ys, hp, he⟩ := Descends.pathTo hd
    refine ⟨ys ++ [_], hp.snoc hk, ?_⟩
    rw [← List.cons_append, he]
    simp

/-- The ancestors listed by `Descends` carry their own attributes. -/
theorem Descends.attrs {d : OpenDoc} {limits : Limits} {root : Nat × Nat} :
    ∀ {anc : List ((Nat × Nat) × Attrs)} {x : Nat × Nat}, Descends d limits root anc x →
      ∀ p ∈ anc, NodeAttrs d limits p.1 p.2
  | _, _, .root => by simp
  | _, _, .kid hd ha _ => by
    intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · exact Descends.attrs hd p hp
    · rw [List.mem_singleton] at hp
      subst hp
      exact ha

/-- A node's own attributes are unique. -/
theorem nodeAttrs_unique {d : OpenDoc} {limits : Limits} {x : Nat × Nat} {a a' : Attrs}
    (h : NodeAttrs d limits x a) (h' : NodeAttrs d limits x a') : a = a' := by
  obtain ⟨nd, hg, ha⟩ := h
  obtain ⟨nd', hg', ha'⟩ := h'
  rw [hg] at hg'
  cases hg'
  rw [ha] at ha'
  cases ha'
  rfl

/-- Ancestor lists with the same nodes are equal (the attributes are the nodes' own). -/
theorem anc_eq {d : OpenDoc} {limits : Limits} :
    ∀ {l1 l2 : List ((Nat × Nat) × Attrs)}, l1.map (·.1) = l2.map (·.1) →
      (∀ p ∈ l1, NodeAttrs d limits p.1 p.2) → (∀ p ∈ l2, NodeAttrs d limits p.1 p.2) →
      l1 = l2
  | [], [], _, _, _ => rfl
  | [], _ :: _, h, _, _ => by simp at h
  | _ :: _, [], h, _, _ => by simp at h
  | (x, a) :: l1, (x', a') :: l2, h, h1, h2 => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨hx, ht⟩ := h
    subst hx
    have ha := nodeAttrs_unique (h1 (x, a) (List.mem_cons_self ..))
      (h2 (x, a') (List.mem_cons_self ..))
    dsimp only at ha
    subst ha
    rw [anc_eq ht (fun p hp => h1 p (List.mem_cons_of_mem _ hp))
      (fun p hp => h2 p (List.mem_cons_of_mem _ hp))]

/-- **Unique paths from the root** of a successful walk: every live node is reached from
the root `/Pages` node along exactly one `Descends` path (the walk's tree is a tree, not a
DAG). -/
theorem walk_descends_unique {d : OpenDoc} {limits : Limits} {n g : Nat} {st : WalkState}
    (h : walk d limits n g = .ok st) {anc1 anc2 : List ((Nat × Nat) × Attrs)} {x : Nat × Nat}
    (h1 : Descends d limits (n, g) anc1 x) (h2 : Descends d limits (n, g) anc2 x)
    (hx : Live d limits x) : anc1 = anc2 := by
  have hU := (loop_forest (st := initState n g) h).1 (n, g) (by simp [initState])
  obtain ⟨ys1, hp1, he1⟩ := h1.pathTo
  obtain ⟨ys2, hp2, he2⟩ := h2.pathTo
  have hys := hU ys1 ys2 x x hp1 hp2 hx hx rfl
  subst hys
  rw [he1] at he2
  exact anc_eq (List.append_cancel_right he2) h1.attrs h2.attrs

/-- A leaf is live. -/
theorem LeafNode.live {d : OpenDoc} {limits : Limits} {x : Nat × Nat} {a : Attrs}
    {c : Option PdfObject} (h : LeafNode d limits x a c) : Live d limits x := by
  obtain ⟨nd, hg, -⟩ := h
  intro h'
  rw [hg] at h'
  cases h'

/-! ## (5) The error of a cyclic tree is `Error.cycle` (task 4.1c) -/

/-- Node `x`, at depth `k` below the root, is **well formed**: a dangling reference (`null`,
rule W3), or a dictionary within the depth limit whose attributes resolve (A1) and whose kind
is a leaf or an intermediate node with a valid `/Kids` (W4, W5, W6). Exactly the conditions
under which `visitNode` succeeds. -/
def NodeOK (d : OpenDoc) (limits : Limits) (k : Nat) (x : Nat × Nat) : Prop :=
  d.getObject limits x.1 x.2 = .ok (.obj .null) ∨
    ∃ nd own, d.getObject limits x.1 x.2 = .ok (.obj (.dict nd)) ∧
      attrsOf d limits nd = .ok own ∧ k ≤ limits.maxObjectDepth ∧
      (kindOf nd = .leaf ∨
        ∃ ko ks, kindOf nd = .inner ∧ key d limits nd "Kids" = .ok ko ∧ kidsOf ko = some ks)

/-- The tree below `root` is **well formed**: every node reached from `root` along a path of
pairwise distinct object numbers is well formed at its depth (`NodeOK`). Nothing is required
of paths that repeat a number, so a cyclic or shared `/Kids` graph can be well formed. -/
def WellFormedTree (d : OpenDoc) (limits : Limits) (root : Nat × Nat) : Prop :=
  ∀ anc x, Descends d limits root anc x → (anc.map (·.1.1) ++ [x.1]).Nodup →
    NodeOK d limits anc.length x

/-- Appending a new element keeps a list duplicate-free. -/
theorem nodup_snoc {a : Nat} : ∀ {l : List Nat}, l.Nodup → a ∉ l → (l ++ [a]).Nodup
  | [], _, _ => by simp
  | b :: l, h, ha => by
    rw [List.nodup_cons] at h
    rw [List.cons_append, List.nodup_cons]
    refine ⟨?_, nodup_snoc h.2 (fun hm => ha (List.mem_cons_of_mem _ hm))⟩
    intro hm
    rcases List.mem_append.1 hm with hm | hm
    · exact h.1 hm
    · rw [List.mem_singleton] at hm
      subst hm
      exact ha (List.mem_cons_self ..)

/-- `popLive` fails only with `Error.cycle` when every unvisited entry can be fetched. -/
theorem popLive_ok_or_cycle {d : OpenDoc} {limits : Limits} {vis : List Nat} :
    ∀ {s : List Entry} {k : Nat},
      (∀ x ∈ s, x.num ∉ vis → ∃ b, d.getObject limits x.num x.gen = .ok b) →
      (∃ r, popLive d limits vis s k = .ok r) ∨
        ∃ o m, popLive d limits vis s k = .error (.cycle o m)
  | [], _, _ => Or.inl ⟨_, rfl⟩
  | e :: s, k, h => by
    unfold popLive
    by_cases hv : e.num ∈ vis
    · exact Or.inr ⟨offsetOf d e.num, "page tree /Kids cycle", by simp only [hv, ↓reduceIte]⟩
    · obtain ⟨b, hb⟩ := h e (List.mem_cons_self ..) hv
      simp only [hv, ↓reduceIte, hb]
      split
      · rename_i x hx; cases hx
      · exact popLive_ok_or_cycle (fun x hx => h x (List.mem_cons_of_mem _ hx))
      · exact Or.inl ⟨_, rfl⟩

/-- `visitNode` succeeds on a well-formed dictionary node. -/
theorem visitNode_ok_of {d : OpenDoc} {limits : Limits} {e : Entry} {nd : Dict} {own : Attrs}
    {st : WalkState} (hdep : e.depth ≤ limits.maxObjectDepth) (ho : attrsOf d limits nd = .ok own)
    (hk : kindOf nd = .leaf ∨
      ∃ ko ks, kindOf nd = .inner ∧ key d limits nd "Kids" = .ok ko ∧ kidsOf ko = some ks) :
    ∃ st', visitNode d limits e (.obj (.dict nd)) st = .ok st' := by
  have hnl : ¬ limits.maxObjectDepth < e.depth := by omega
  unfold visitNode
  rcases hk with hk | ⟨ko, ks, hk, hko, hks⟩
  · simp [hnl, ho, hk]
  · simp [hnl, ho, hk, hko, hks]

/-- The invariant of a walk in a well-formed tree: visited numbers are distinct index keys,
the fuel covers the keys not yet visited, and every stack entry is reached from `root` along
a path of distinct, visited ancestors, at its depth. -/
def CInv (d : OpenDoc) (limits : Limits) (root : Nat × Nat) (f : Nat) (st : WalkState) : Prop :=
  st.visited.Nodup ∧ (∀ v ∈ st.visited, v ∈ d.index.toList.map Prod.fst) ∧
    d.objectCount ≤ st.visited.length + f ∧
    ∀ e ∈ st.stack, ∃ anc, Descends d limits root anc (e.num, e.gen) ∧ e.depth = anc.length ∧
      (anc.map (·.1.1)).Nodup ∧ ∀ v ∈ anc.map (·.1.1), v ∈ st.visited

/-- **In a well-formed tree the loop fails only with `Error.cycle`.** -/
theorem loop_ok_or_cycle {d : OpenDoc} {limits : Limits} {root : Nat × Nat}
    (hwf : WellFormedTree d limits root) :
    ∀ {f : Nat} {st : WalkState}, CInv d limits root f st →
      (∃ fin, loop d limits f st = .ok fin) ∨
        ∃ o m, loop d limits f st = .error (.cycle o m) := by
  -- Every unvisited stack entry is well formed, hence fetchable.
  have fetch : ∀ {f : Nat} {st : WalkState}, CInv d limits root f st →
      ∀ x ∈ st.stack, x.num ∉ st.visited →
        ∃ anc, Descends d limits root anc (x.num, x.gen) ∧ x.depth = anc.length ∧
          (anc.map (·.1.1)).Nodup ∧ (∀ v ∈ anc.map (·.1.1), v ∈ st.visited) ∧
          NodeOK d limits anc.length (x.num, x.gen) := by
    intro f st hi x hx hn
    obtain ⟨anc, hd, hdep, hand, hav⟩ := hi.2.2.2 x hx
    exact ⟨anc, hd, hdep, hand, hav,
      hwf anc _ hd (nodup_snoc hand (fun hm => hn (hav _ hm)))⟩
  have fetchB : ∀ {f : Nat} {st : WalkState}, CInv d limits root f st →
      ∀ x ∈ st.stack, x.num ∉ st.visited → ∃ b, d.getObject limits x.num x.gen = .ok b := by
    intro f st hi x hx hn
    obtain ⟨anc, -, -, -, -, hok⟩ := fetch hi x hx hn
    rcases hok with hok | ⟨nd, -, hok, -⟩
    · exact ⟨_, hok⟩
    · exact ⟨_, hok⟩
  intro f
  induction f with
  | zero =>
    intro st hi
    unfold loop
    rcases popLive_ok_or_cycle (k := st.skipped) (fetchB hi) with ⟨r, hr⟩ | ⟨o, m, hr⟩
    · rcases r with ⟨_ | ⟨e, b, rest⟩, kk⟩
      · rw [hr]; exact Or.inl ⟨_, rfl⟩
      · exact absurd hr (popLive_exhausted hi.1 hi.2.1 (by have := hi.2.2.1; omega))
    · rw [hr]; exact Or.inr ⟨o, m, rfl⟩
  | succ f ih =>
    intro st hi
    unfold loop
    rcases popLive_ok_or_cycle (k := st.skipped) (fetchB hi) with ⟨r, hr⟩ | ⟨o, m, hr⟩
    · rcases r with ⟨_ | ⟨e, b, rest⟩, kk⟩
      · rw [hr]; exact Or.inl ⟨_, rfl⟩
      · obtain ⟨pre, hs, -, hn, hg, hb⟩ := popLive_some hr
        have he : e ∈ st.stack := by rw [hs]; simp
        obtain ⟨anc, hd, hdep, hand, hav, hok⟩ := fetch hi e he hn
        rcases hok with hnull | ⟨nd, own0, hg', ho0, hdl, hkind⟩
        · exact absurd (Except.ok.inj (hg.symm.trans hnull)) hb
        · rw [hg] at hg'
          cases hg'
          obtain ⟨st', hv⟩ := visitNode_ok_of (st := { st with stack := rest, skipped := kk })
            (by rw [hdep]; exact hdl) ho0 hkind
          rw [hr]
          dsimp only
          rw [hv]
          dsimp only
          apply ih
          obtain ⟨hnd, hkey, hlen, hst⟩ := hi
          obtain ⟨nd', own, hb', ho, hvis, hcase⟩ := visitNode_cases hv
          cases hb'
          dsimp only at hvis hcase
          have hsub : ∀ v ∈ st.visited, v ∈ st'.visited := by
            intro v hv'; rw [hvis]; exact List.mem_cons_of_mem _ hv'
          have hrest : ∀ x ∈ rest, ∃ anc, Descends d limits root anc (x.num, x.gen) ∧
              x.depth = anc.length ∧ (anc.map (·.1.1)).Nodup ∧
              ∀ v ∈ anc.map (·.1.1), v ∈ st'.visited := by
            intro x hx
            obtain ⟨a, h1, h2, h3, h4⟩ := hst x (by rw [hs]; simp [hx])
            exact ⟨a, h1, h2, h3, fun v hv' => hsub v (h4 v hv')⟩
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [hvis]; exact List.nodup_cons.2 ⟨hn, hnd⟩
          · rw [hvis]
            intro v hv'
            rcases List.mem_cons.1 hv' with rfl | hv'
            · exact getObject_ne_null_key hg hb
            · exact hkey v hv'
          · rw [hvis, List.length_cons]; omega
          · rcases hcase with ⟨ko, ks, hk, hko, hks, hst', -⟩ | ⟨-, hst', -⟩
            · rw [hst']
              intro x hx
              rcases List.mem_append.1 hx with hx | hx
              · obtain ⟨r, hr', rfl⟩ := List.mem_map.1 hx
                refine ⟨anc ++ [((e.num, e.gen), own)],
                  Descends.kid hd ⟨_, hg, ho⟩ ⟨ks, ⟨_, ko, hg, hk, hko, hks⟩, hr'⟩, ?_, ?_, ?_⟩
                · simp [hdep]
                · rw [List.map_append]
                  exact nodup_snoc hand (fun hm => hn (hav _ hm))
                · intro v hv'
                  rw [List.map_append] at hv'
                  rcases List.mem_append.1 hv' with hv' | hv'
                  · exact hsub v (hav v hv')
                  · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hv'
                    rw [hv', hvis]
                    exact List.mem_cons_self ..
              · exact hrest x hx
            · rw [hst']; exact hrest
    · rw [hr]; exact Or.inr ⟨o, m, rfl⟩

/-- **In a well-formed tree the walk fails only with `Error.cycle`.** -/
theorem walk_ok_or_cycle {d : OpenDoc} {limits : Limits} {n g : Nat}
    (hwf : WellFormedTree d limits (n, g)) :
    (∃ st, walk d limits n g = .ok st) ∨ ∃ o m, walk d limits n g = .error (.cycle o m) :=
  loop_ok_or_cycle hwf (st := initState n g)
    ⟨List.nodup_nil, by simp [initState], by simp [initState], by
      intro e he
      simp only [initState, List.mem_singleton] at he
      subst he
      exact ⟨[], Descends.root, rfl, List.nodup_nil, by simp⟩⟩

/-- **A `/Kids` cycle is `Error.cycle`** (pinned error kind): in a well-formed tree, if a node
on a descending path from the root has a kid with the object number of itself or of one of
its ancestors, the walk fails with `Error.cycle`. -/
theorem walk_cycle_error {d : OpenDoc} {limits : Limits} {n g : Nat}
    (hwf : WellFormedTree d limits (n, g)) {ys : List (Nat × Nat)} {y : Nat × Nat}
    (hp : KidPath d limits (n, g) ys)
    (hk : Kid d limits (((n, g) :: ys).getLast (List.cons_ne_nil _ _)) y)
    (hy : y.1 ∈ ((n, g) :: ys).map Prod.fst) :
    ∃ o m, walk d limits n g = .error (.cycle o m) := by
  rcases walk_ok_or_cycle hwf with ⟨st, hw⟩ | h
  · exact absurd hy (walk_kid_not_ancestor hw hp hk)
  · exact h

/-- **A shared node is `Error.cycle`**: in a well-formed tree, a live node reached from the
root along two different `Descends` paths (two parents, or one parent listing it twice)
makes the walk fail with `Error.cycle`. -/
theorem walk_shared_error {d : OpenDoc} {limits : Limits} {n g : Nat}
    (hwf : WellFormedTree d limits (n, g)) {anc1 anc2 : List ((Nat × Nat) × Attrs)}
    {x : Nat × Nat} (h1 : Descends d limits (n, g) anc1 x) (h2 : Descends d limits (n, g) anc2 x)
    (hne : anc1 ≠ anc2) (hx : Live d limits x) :
    ∃ o m, walk d limits n g = .error (.cycle o m) := by
  rcases walk_ok_or_cycle hwf with ⟨st, hw⟩ | h
  · exact absurd (walk_descends_unique hw h1 h2 hx) hne
  · exact h

/-! ## The document: uniqueness and the cycle error kind -/

/-- `ofOpen` returns the walk's error. -/
theorem ofOpen_walk_error {limits : Limits} {d : OpenDoc} {rn rg pn pg : Nat} {cat : Dict}
    {e : Error} (hroot : d.trailer.root? = some (rn, rg))
    (hcat : d.getObject limits rn rg = .ok (.obj (.dict cat)))
    (hpages : Dict.get? cat (Name.ofString "Pages") = some (.ref pn pg))
    (hw : walk d limits pn pg = .error e) : ofOpen limits d = .error e := by
  simp [ofOpen, hroot, hcat, hpages, hw]

/-- **Unique root-to-node paths** in a document opened by `ofOpen`: a live node has exactly
one `Descends` path from the root `/Pages` node. -/
theorem ofOpen_descends_unique {limits : Limits} {d : OpenDoc} {doc : Doc}
    (h : ofOpen limits d = .ok doc) {anc1 anc2 : List ((Nat × Nat) × Attrs)} {x : Nat × Nat}
    (h1 : Descends d limits doc.pagesRef anc1 x) (h2 : Descends d limits doc.pagesRef anc2 x)
    (hx : Live d limits x) : anc1 = anc2 := by
  obtain ⟨st, hw, -⟩ := ofOpen_ok_root h
  exact walk_descends_unique hw h1 h2 hx

/-- **The root-to-leaf path of a page is unique**, so the "nearest node" of
`ofOpen_page_inherit` is well defined: any two `Descends` paths to a page of `doc` are
equal. -/
theorem ofOpen_page_path_unique {limits : Limits} {d : OpenDoc} {doc : Doc}
    (h : ofOpen limits d = .ok doc) {p : Page} (hp : p ∈ doc.pages.toList)
    {anc1 anc2 : List ((Nat × Nat) × Attrs)}
    (h1 : Descends d limits doc.pagesRef anc1 (p.num, p.gen))
    (h2 : Descends d limits doc.pagesRef anc2 (p.num, p.gen)) : anc1 = anc2 := by
  obtain ⟨_, _, _, _, hl, -⟩ := ofOpen_page_inherit h hp
  exact ofOpen_descends_unique h h1 h2 hl.live

/-- **Unique root-to-leaf paths** for `openDoc`. -/
theorem openDoc_page_path_unique {limits : Limits} {bytes : ByteArray} {doc : Doc}
    (h : openDoc limits bytes = .ok doc) {p : Page} (hp : p ∈ doc.pages.toList)
    {anc1 anc2 : List ((Nat × Nat) × Attrs)}
    (h1 : Descends doc.file limits doc.pagesRef anc1 (p.num, p.gen))
    (h2 : Descends doc.file limits doc.pagesRef anc2 (p.num, p.gen)) : anc1 = anc2 :=
  ofOpen_page_path_unique (openDoc_ok h).2 hp h1 h2

/-- **A `/Kids` cycle makes `ofOpen` fail with `Error.cycle`** when the tree below the
catalog's `/Pages` node is well formed (`WellFormedTree`). -/
theorem ofOpen_cycle_error_kind {limits : Limits} {d : OpenDoc} {rn rg pn pg : Nat} {cat : Dict}
    {ys : List (Nat × Nat)} {y : Nat × Nat}
    (hroot : d.trailer.root? = some (rn, rg))
    (hcat : d.getObject limits rn rg = .ok (.obj (.dict cat)))
    (hpages : Dict.get? cat (Name.ofString "Pages") = some (.ref pn pg))
    (hwf : WellFormedTree d limits (pn, pg))
    (hp : KidPath d limits (pn, pg) ys)
    (hk : Kid d limits (((pn, pg) :: ys).getLast (List.cons_ne_nil _ _)) y)
    (hy : y.1 ∈ ((pn, pg) :: ys).map Prod.fst) :
    ∃ o m, ofOpen limits d = .error (.cycle o m) := by
  obtain ⟨o, m, hw⟩ := walk_cycle_error hwf hp hk hy
  exact ⟨o, m, ofOpen_walk_error hroot hcat hpages hw⟩

/-- **A `/Kids` cycle makes `openDoc` fail with `Error.cycle`** (well-formed tree). -/
theorem openDoc_cycle_error_kind {limits : Limits} {bytes : ByteArray} {d : OpenDoc}
    {rn rg pn pg : Nat} {cat : Dict} {ys : List (Nat × Nat)} {y : Nat × Nat}
    (hopen : Core.Open.openFile limits bytes = .ok d)
    (hroot : d.trailer.root? = some (rn, rg))
    (hcat : d.getObject limits rn rg = .ok (.obj (.dict cat)))
    (hpages : Dict.get? cat (Name.ofString "Pages") = some (.ref pn pg))
    (hwf : WellFormedTree d limits (pn, pg))
    (hp : KidPath d limits (pn, pg) ys)
    (hk : Kid d limits (((pn, pg) :: ys).getLast (List.cons_ne_nil _ _)) y)
    (hy : y.1 ∈ ((pn, pg) :: ys).map Prod.fst) :
    ∃ o m, openDoc limits bytes = .error (.cycle o m) := by
  obtain ⟨o, m, he⟩ := ofOpen_cycle_error_kind hroot hcat hpages hwf hp hk hy
  exact ⟨o, m, by simp [openDoc, hopen, he]⟩

/-- **A shared node makes `ofOpen` fail with `Error.cycle`** (well-formed tree): a live node
reached from the catalog's `/Pages` node along two different paths. -/
theorem ofOpen_shared_error {limits : Limits} {d : OpenDoc} {rn rg pn pg : Nat} {cat : Dict}
    {anc1 anc2 : List ((Nat × Nat) × Attrs)} {x : Nat × Nat}
    (hroot : d.trailer.root? = some (rn, rg))
    (hcat : d.getObject limits rn rg = .ok (.obj (.dict cat)))
    (hpages : Dict.get? cat (Name.ofString "Pages") = some (.ref pn pg))
    (hwf : WellFormedTree d limits (pn, pg))
    (h1 : Descends d limits (pn, pg) anc1 x) (h2 : Descends d limits (pn, pg) anc2 x)
    (hne : anc1 ≠ anc2) (hx : Live d limits x) :
    ∃ o m, ofOpen limits d = .error (.cycle o m) := by
  obtain ⟨o, m, hw⟩ := walk_shared_error hwf h1 h2 hne hx
  exact ⟨o, m, ofOpen_walk_error hroot hcat hpages hw⟩

/-- **A shared node makes `openDoc` fail with `Error.cycle`** (well-formed tree). -/
theorem openDoc_shared_error {limits : Limits} {bytes : ByteArray} {d : OpenDoc}
    {rn rg pn pg : Nat} {cat : Dict} {anc1 anc2 : List ((Nat × Nat) × Attrs)} {x : Nat × Nat}
    (hopen : Core.Open.openFile limits bytes = .ok d)
    (hroot : d.trailer.root? = some (rn, rg))
    (hcat : d.getObject limits rn rg = .ok (.obj (.dict cat)))
    (hpages : Dict.get? cat (Name.ofString "Pages") = some (.ref pn pg))
    (hwf : WellFormedTree d limits (pn, pg))
    (h1 : Descends d limits (pn, pg) anc1 x) (h2 : Descends d limits (pn, pg) anc2 x)
    (hne : anc1 ≠ anc2) (hx : Live d limits x) :
    ∃ o m, openDoc limits bytes = .error (.cycle o m) := by
  obtain ⟨o, m, he⟩ := ofOpen_shared_error hroot hcat hpages hwf h1 h2 hne hx
  exact ⟨o, m, by simp [openDoc, hopen, he]⟩

end SafePdf.Spec.PageTree
