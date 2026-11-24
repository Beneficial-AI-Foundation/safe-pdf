/-!
# One budget per user operation (task 12.3)

Plan.md §6 Phase 12, "One budget per user operation": memory reserved for concurrent page
buffers, thumbnails and caches **before dispatch**; a **shared work allowance** through a
search, export or render; worker ceilings and deadlines enforced outside Lean's cost model
(`docs/safety.md` §5). This module is the pure, Tk-free accounting model the viewer
(`SafePdf.Shell.App.Viewer`) runs; the worker's ceilings are applied by
`SafePdf.Shell.Worker.Sandbox.fence`. The numbers are published in `docs/viewer.md`
("Budgets and ceilings").

* **Reservation pool** (`Pool`). Every render of a page, every thumbnail and every text or
  links request reserves its estimated bytes before it is dispatched (`Pool.admit`): an image
  `4 · w · h` (`imageBytes`), a text request a fixed overhead (`Ceilings.textBytes`). The
  pool's total never exceeds its ceiling — an invariant carried by the structure itself
  (`Pool.inv`), so no sequence of operations can break it (`Pool.used_le_ceiling`).
* **Decisions** (`Outcome`). When a reservation would cross the ceiling the operation
  **waits** (a page: it is asked for again when a reservation is released), **lowers its
  quality** (a thumbnail: rendered at half, quarter or eighth zoom, `Outcome.reserved` with a
  `scale` above 0) or is **refused** (an image larger than the whole pool; cannot happen for
  the viewer's pages, whose size is capped by `View.maxViewPixels`: `page_fits_pool`). Images
  leave `Ceilings.textReserve` of the pool to text requests, so text is never starved by
  images.
* **Release exactly once** (`Pool.release`). A reservation is a `Ticket` with a fresh id; the
  viewer keeps it in the job that made it and releases it where the job leaves its list.
  Releasing a ticket gives back exactly the pool before its reservation
  (`Pool.release_reserve`), and a second release of the same ticket changes nothing
  (`Pool.release_release`), so a reservation is released at most once in effect; the
  viewer's smoke run checks that an idle viewer holds no reservation (none leaks).
* **Shared work allowance** (`Allowance`). A search (one Find Next / Previous) gets one
  allowance of pages to index and of wall time, shared by all the pages it visits — not a
  fresh budget per page. Each page whose index is not cached spends one page
  (`Allowance.spend`); when the allowance is spent the search stops and says so. At most
  `Allowance.pages` pages are indexed per search (`Allowance.spendAll_le`). Each page request
  is still bounded by the worker's deadline and its own `Filter.Budget`.
-/

namespace SafePdf.Shell.App.Budget

/-- `n` mebibytes, in bytes. -/
def mib (n : Nat) : Nat := n * 1048576

/-- **The published ceilings** (`docs/viewer.md`, "Budgets and ceilings"). -/
structure Ceilings where
  /-- Bytes the viewer may have reserved for work in flight (page renders, thumbnails, text
  requests; their reply frames and decoded images): 512 MiB. -/
  poolBytes : Nat := mib 512
  /-- The part of the pool images leave to text and links requests: 32 MiB. -/
  textReserve : Nat := mib 32
  /-- The estimate of one text index or links request in flight: 2 MiB. -/
  textBytes : Nat := mib 2
  /-- Pages one search may index (its shared work allowance). -/
  searchPages : Nat := 400
  /-- Wall time one search may spend indexing pages (ms). -/
  searchMs : Nat := 60000
  /-- The document worker's memory ceiling (MiB; `--mem-limit-mib`). -/
  workerMemMiB : Nat := 2048
  /-- The CPU time one worker request may use (s; `--cpu-limit-s`); the client's wall-clock
  deadline is 20 s. -/
  workerCpuS : Nat := 60
  /-- Peak resident memory of the viewer process in the interleave scenario (MiB,
  `scripts/interleave.sh`). -/
  viewerRssMiB : Nat := 1024
  /-- Peak resident memory of one worker process in the interleave scenario (MiB). -/
  workerRssMiB : Nat := 512

/-- The viewer's ceilings. -/
def ceilings : Ceilings := {}

/-- Estimated bytes of a `w × h` RGBA image. -/
def imageBytes (w h : Nat) : Nat := 4 * w * h

/-! ## The reservation pool -/

/-- A reservation: its id (fresh in its pool) and its bytes. -/
structure Ticket where
  /-- Unique among the pool's reservations. -/
  id : Nat
  /-- Bytes reserved. -/
  bytes : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Sum of the bytes of a list of tickets. -/
def total : List Ticket → Nat
  | [] => 0
  | t :: ts => t.bytes + total ts

/-- Removing tickets never adds bytes. -/
theorem total_filter_le (p : Ticket → Bool) : ∀ ts : List Ticket, total (ts.filter p) ≤ total ts
  | [] => by simp [total]
  | t :: ts => by
    have ih := total_filter_le p ts
    by_cases h : p t = true
    · simp [h, total]; omega
    · simp [h, total]; omega

/-- **The reservation pool**: the reservations held, under a ceiling. The invariant `inv`
(total ≤ ceiling) is part of the structure, so every pool any code can build respects it;
`fresh` makes the next ticket id unused. -/
structure Pool where
  /-- Most bytes reserved at once. -/
  ceiling : Nat
  /-- Reservations held. -/
  held : List Ticket := []
  /-- The next ticket id. -/
  next : Nat := 0
  /-- **Reserved bytes never exceed the ceiling.** -/
  inv : total held ≤ ceiling
  /-- Every held id is below `next`. -/
  fresh : ∀ t ∈ held, t.id < next

/-- An empty pool with ceiling `c`. -/
def Pool.empty (c : Nat) : Pool where
  ceiling := c
  inv := by simp [total]
  fresh := by simp

instance : Inhabited Pool := ⟨Pool.empty 0⟩

/-- Bytes reserved now. -/
def Pool.used (p : Pool) : Nat := total p.held

/-- Bytes still free. -/
def Pool.free (p : Pool) : Nat := p.ceiling - p.used

/-- **Reserved bytes never exceed the ceiling**, for every pool. -/
theorem Pool.used_le_ceiling (p : Pool) : p.used ≤ p.ceiling := p.inv

/-- **Reserve** `bytes` if they fit under the ceiling: the ticket and the new pool. -/
def Pool.reserve (p : Pool) (bytes : Nat) : Option (Ticket × Pool) :=
  if h : p.used + bytes ≤ p.ceiling then
    let t : Ticket := ⟨p.next, bytes⟩
    some (t, { ceiling := p.ceiling, held := t :: p.held, next := p.next + 1,
               inv := by
                 show bytes + total p.held ≤ p.ceiling
                 simp only [Pool.used] at h; omega
               fresh := by
                 intro u hu
                 simp only [List.mem_cons] at hu
                 rcases hu with rfl | hu
                 · show p.next < p.next + 1; omega
                 · have := p.fresh u hu; omega })
  else none

/-- **Release** a reservation: the pool without the ticket's id. A ticket not held (already
released) changes nothing. -/
def Pool.release (p : Pool) (t : Ticket) : Pool where
  ceiling := p.ceiling
  held := p.held.filter (·.id != t.id)
  next := p.next
  inv := Nat.le_trans (total_filter_le _ _) p.inv
  fresh := fun u hu => p.fresh u (List.mem_filter.mp hu).1

/-- A successful reservation adds exactly its bytes. -/
theorem Pool.reserve_used {p : Pool} {b : Nat} {t : Ticket} {q : Pool}
    (h : p.reserve b = some (t, q)) : q.used = p.used + b ∧ t.bytes = b := by
  unfold Pool.reserve at h
  by_cases hc : p.used + b ≤ p.ceiling
  · simp only [hc, ↓reduceDIte, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by simp [Pool.used, total]; omega, rfl⟩
  · simp [hc] at h

/-- A reservation fails only when it would cross the ceiling. -/
theorem Pool.reserve_none {p : Pool} {b : Nat} (h : p.reserve b = none) :
    p.ceiling < p.used + b := by
  unfold Pool.reserve at h
  by_cases hc : p.used + b ≤ p.ceiling
  · simp [hc] at h
  · omega

/-- Filtering out an id no ticket has keeps the list. -/
theorem filter_absent (i : Nat) : ∀ ts : List Ticket, (∀ u ∈ ts, u.id < i) →
    ts.filter (·.id != i) = ts
  | [] => fun _ => rfl
  | u :: ts => fun h => by
    have hu : u.id < i := h u (by simp)
    have ih := filter_absent i ts (fun v hv => h v (by simp [hv]))
    have : (u.id != i) = true := by simp; omega
    simp [this, ih]

/-- **Releasing a reservation gives back the pool before it** (same reservations held). -/
theorem Pool.release_reserve {p : Pool} {b : Nat} {t : Ticket} {q : Pool}
    (h : p.reserve b = some (t, q)) : (q.release t).held = p.held := by
  unfold Pool.reserve at h
  by_cases hc : p.used + b ≤ p.ceiling
  · simp only [hc, ↓reduceDIte, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Pool.release, List.filter_cons, bne_self_eq_false, Bool.false_eq_true,
      ↓reduceIte]
    exact filter_absent p.next p.held p.fresh
  · simp [hc] at h

/-- **A second release of the same ticket changes nothing**: a reservation is released at
most once in effect. -/
theorem Pool.release_release (p : Pool) (t : Ticket) :
    ((p.release t).release t).held = (p.release t).held := by
  simp only [Pool.release, List.filter_filter, Bool.and_self]

/-- Releasing never adds reserved bytes. -/
theorem Pool.release_used_le (p : Pool) (t : Ticket) : (p.release t).used ≤ p.used :=
  total_filter_le _ _

/-! ## Admission: reserve, wait, lower the quality or refuse -/

/-- What a user operation asks the pool for. -/
inductive Op where
  /-- A page image of `w × h` pixels (the page in view, a neighbour, the prefetch). -/
  | page (w h : Nat)
  /-- A thumbnail of `w × h` pixels (may be rendered smaller). -/
  | thumb (w h : Nat)
  /-- A text index or links request. -/
  | text
  deriving DecidableEq, Repr

/-- The pool's answer. -/
inductive Outcome where
  /-- Dispatch now with this reservation; images at `1 / 2^scale` of the asked zoom (`scale`
  is above 0 only for a thumbnail). -/
  | reserved (t : Ticket) (p : Pool) (scale : Nat)
  /-- Not now: ask again after a release. -/
  | wait
  /-- Never: the operation is larger than the whole pool. -/
  | refuse

/-- The bytes an operation may use: images leave `textReserve` to text. -/
def room (c : Ceilings) (p : Pool) : Op → Nat
  | .text => p.ceiling
  | _ => p.ceiling - c.textReserve

/-- Reserve `bytes` within `limit` (≤ the ceiling). -/
def Pool.reserveWithin (p : Pool) (limit bytes : Nat) : Option (Ticket × Pool) :=
  if p.used + bytes ≤ limit then p.reserve bytes else none

/-- The first of the scales `ks` at which a thumbnail of `bytes` (at scale 0, `bytes / 4^k` at
scale `k`) fits. -/
def thumbScale (p : Pool) (limit bytes : Nat) : List Nat → Option (Nat × Ticket × Pool)
  | [] => none
  | k :: ks =>
    match p.reserveWithin limit (bytes / 4 ^ k) with
    | some (t, q) => some (k, t, q)
    | none => thumbScale p limit bytes ks

/-- The thumbnail scales tried: full, ½, ¼ and ⅛ zoom. -/
def thumbScales : List Nat := [0, 1, 2, 3]

/-- **Admission** of operation `o` to pool `p` under ceilings `c`: a page is reserved, or waits,
or is refused when it is larger than the images' room; a thumbnail is reserved at the first
scale (full, ½, ¼, ⅛ zoom) that fits, else waits; a text request is reserved or waits. -/
def Pool.admit (c : Ceilings) (p : Pool) (o : Op) : Outcome :=
  let limit := room c p o
  match o with
  | .page w h =>
    let b := imageBytes w h
    if b > limit then .refuse
    else match p.reserveWithin limit b with
      | some (t, q) => .reserved t q 0
      | none => .wait
  | .thumb w h =>
    match thumbScale p limit (imageBytes w h) thumbScales with
    | some (k, t, q) => .reserved t q k
    | none => if imageBytes w h / 4 ^ 3 > limit then .refuse else .wait
  | .text =>
    if c.textBytes > limit then .refuse
    else match p.reserveWithin limit c.textBytes with
      | some (t, q) => .reserved t q 0
      | none => .wait

/-- Every reservation the admission makes is a `Pool.reserve` of the same pool. -/
theorem Pool.reserveWithin_some {p : Pool} {l b : Nat} {t : Ticket} {q : Pool}
    (h : p.reserveWithin l b = some (t, q)) : p.reserve b = some (t, q) ∧ p.used + b ≤ l := by
  unfold Pool.reserveWithin at h
  split at h
  · exact ⟨h, by omega⟩
  · cases h

/-- **An admitted operation's reservation is an ordinary reservation of the pool** (so
`reserve_used`, `release_reserve`, the invariant apply), and images stay within their room. -/
theorem Pool.admit_reserved {c : Ceilings} {p : Pool} {o : Op} {t : Ticket} {q : Pool} {k : Nat}
    (h : p.admit c o = .reserved t q k) :
    p.reserve t.bytes = some (t, q) ∧ p.used + t.bytes ≤ room c p o := by
  have key : ∀ {l b : Nat}, p.reserveWithin l b = some (t, q) →
      p.reserve t.bytes = some (t, q) ∧ p.used + t.bytes ≤ l := by
    intro l b hw
    have ⟨hr, hl⟩ := Pool.reserveWithin_some hw
    have hb := (Pool.reserve_used hr).2
    subst hb
    exact ⟨hr, hl⟩
  have thumbKey : ∀ {l b : Nat} (js : List Nat), thumbScale p l b js = some (k, t, q) →
      p.reserve t.bytes = some (t, q) ∧ p.used + t.bytes ≤ l := by
    intro l b js
    induction js with
    | nil => intro hs; simp [thumbScale] at hs
    | cons j js ih =>
      intro hs
      simp only [thumbScale] at hs
      split at hs
      · next t' q' hw =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨-, rfl, rfl⟩ := hs
        exact key hw
      · exact ih hs
  unfold Pool.admit at h
  cases o with
  | page w h' =>
    simp only at h
    split at h
    · cases h
    · split at h
      · next hw => cases h; exact key hw
      · cases h
  | thumb w h' =>
    simp only at h
    split at h
    · next hs => cases h; exact thumbKey _ hs
    · split at h <;> cases h
  | text =>
    simp only at h
    split at h
    · cases h
    · split at h
      · next hw => cases h; exact key hw
      · cases h

/-- The viewer's largest page image (`View.maxViewPixels` = 2²⁶ pixels, 256 MiB) fits in the
images' room of an empty pool, so a page is never refused, only made to wait. -/
theorem page_fits_pool : imageBytes 8192 8192 ≤ ceilings.poolBytes - ceilings.textReserve := by
  decide

#guard (Pool.empty (mib 8)).used == 0
-- A page that fits is reserved, the next one waits, a release lets it in.
#guard
  let c : Ceilings := { poolBytes := 100, textReserve := 10, textBytes := 4 }
  let p := Pool.empty 100
  match p.admit c (.page 4 5) with
  | .reserved t1 p1 0 =>
    (match p1.admit c (.page 4 5) with
     | .wait =>
       (match (p1.release t1).admit c (.page 4 5) with
        | .reserved _ p2 0 => p2.used == 80 && (p1.release t1).used == 0
        | _ => false)
     | _ => false) && p1.used == 80
  | _ => false
-- Images leave the text reserve: text still fits next to a full image room.
#guard
  let c : Ceilings := { poolBytes := 100, textReserve := 10, textBytes := 4 }
  match (Pool.empty 100).admit c (.page 3 7) with
  | .reserved _ p1 _ =>
    (match p1.admit c .text with | .reserved _ p2 _ => p2.used == 88 | _ => false)
  | _ => false
-- A thumbnail lowers its quality instead of waiting: 400 bytes (and 100 at ½ zoom) do not fit
-- in the images' room of 90, 25 (¼ zoom) do.
#guard
  let c : Ceilings := { poolBytes := 100, textReserve := 10, textBytes := 4 }
  match (Pool.empty 100).admit c (.thumb 10 10) with
  | .reserved t _ 2 => t.bytes == 25
  | _ => false
-- Larger than the whole pool: refused.
#guard
  let c : Ceilings := { poolBytes := 100, textReserve := 10, textBytes := 4 }
  match (Pool.empty 100).admit c (.page 10 10) with | .refuse => true | _ => false
-- Releasing twice is releasing once.
#guard
  match (Pool.empty 100).reserve 30 with
  | some (t, p) =>
    match p.reserve 20 with
    | some (_, q) => ((q.release t).release t).used == 20 && (q.release t).used == 20
    | none => false
  | none => false

/-! ## Shared work allowance -/

/-- **The work allowance of one search**: pages it may still index and the time it ends
(`IO.monoMsNow` scale). -/
structure Allowance where
  /-- Pages that may still be indexed. -/
  pages : Nat
  /-- When the allowance ends (ms). -/
  endsAt : Nat
  deriving DecidableEq, Repr

/-- A fresh allowance at time `now`. -/
def Allowance.start (c : Ceilings) (now : Nat) : Allowance := ⟨c.searchPages, now + c.searchMs⟩

/-- Spend one page at time `now`: `none` when the allowance is used up (no page left, or its
time is over). -/
def Allowance.spend (a : Allowance) (now : Nat) : Option Allowance :=
  if a.pages = 0 ∨ a.endsAt ≤ now then none else some { a with pages := a.pages - 1 }

/-- Spends one page per time of `times` while it can: the number of pages indexed. -/
def Allowance.spendAll (a : Allowance) : List Nat → Nat
  | [] => 0
  | now :: rest =>
    match a.spend now with
    | some a' => 1 + a'.spendAll rest
    | none => 0

/-- **One search indexes at most `pages` pages**, however many it visits. -/
theorem Allowance.spendAll_le : ∀ (a : Allowance) (ts : List Nat), a.spendAll ts ≤ a.pages
  | _, [] => by simp [Allowance.spendAll]
  | a, now :: rest => by
    unfold Allowance.spendAll Allowance.spend
    split
    · next a' h =>
      split at h
      · cases h
      · cases h
        have := Allowance.spendAll_le { a with pages := a.pages - 1 } rest
        simp only at this
        omega
    · omega

#guard (Allowance.start ceilings 0).spendAll (List.replicate 1000 5) == ceilings.searchPages
#guard (Allowance.start ceilings 0).spendAll [1, 2, ceilings.searchMs, 3] == 2

end SafePdf.Shell.App.Budget
