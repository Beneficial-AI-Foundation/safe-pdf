/-!
# One budget per user operation (tasks 12.3, 12.3b)

Plan.md §6 Phase 12, "One budget per user operation": memory reserved for concurrent page
buffers, thumbnails and caches **before dispatch**; a **shared work allowance** through a
search, export or render; worker ceilings and deadlines enforced outside Lean's cost model
(`docs/safety.md` §5). This module is the pure, Tk-free accounting model the viewer
(`SafePdf.Shell.App.Viewer`) runs; the worker's ceilings are applied by
`SafePdf.Shell.Worker.Sandbox.fence`. The numbers are published in `docs/viewer.md`
("Budgets and ceilings").

* **Reservation pool** (`Pool`). Every render of a page, every thumbnail and every text or
  links request reserves its estimated bytes before it is dispatched (`Pool.admit`): an image
  its reply frame plus its decoded pixels, `8 · w · h` (`workBytes`, task 12.3b; `4 · w · h`
  before), a text request a fixed overhead (`Ceilings.textBytes`); since task 12.3b also Save
  and XFDF export, their output bytes (`Op.output`), refused when larger than the pool. The
  pool's total never exceeds its ceiling — an invariant carried by the structure itself
  (`Pool.inv`), so no sequence of operations can break it (`Pool.used_le_ceiling`).
* **Decisions** (`Outcome`). When a reservation would cross the ceiling the operation
  **waits** (a page: it is asked for again when a reservation is released), **lowers its
  quality** (a thumbnail: rendered at half, quarter or eighth zoom, `Outcome.reserved` with a
  `scale` above 0) or is **refused** (an image larger than the whole pool; cannot happen for
  the viewer's pages, whose size is capped by `Ceilings.pagePixels`: `page_fits_pool`). Images
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
  is still bounded by the worker's deadline and its own `Filter.Budget` (one per worker
  request, `Worker.Serve.answer`).
* **Live photos** (task 12.3b; a second `Pool`, the same invariant). Every Tk photo the viewer
  keeps — the page photos on the canvas and the thumbnails — holds a reservation
  (`photoBytes`, 16 bytes per pixel: Tk's copy and its display buffers, measured, plus the
  viewer's own copy) from its `put` to its deletion. A page photo that does not fit evicts the
  photos of pages not in view (`Pool.makeRoom`: afterwards it fits, `makeRoom_fits`; only a
  prefix of the candidates is released, `makeRoom_released`); a page in view that still does
  not fit is refused with a message, a neighbour waits. Page photos leave `thumbReserve` to the
  thumbnails, which always fit (`thumbs_fit_reserve`); two pages at the pixel cap always fit
  (`two_pages_fit_photos`). With the render cache (`cacheBytes`) and the base, the pools fit
  the viewer's published peak (`plan_fits`).
-/

namespace SafePdf.Shell.App.Budget

/-- `n` mebibytes, in bytes. -/
def mib (n : Nat) : Nat := n * 1048576

/-- **The published ceilings** (`docs/viewer.md`, "Budgets and ceilings"). -/
structure Ceilings where
  /-- Bytes the viewer may have reserved for work in flight (page renders, thumbnails, text
  requests, Save and XFDF export; their reply frames and decoded images, the output bytes):
  192 MiB (512 MiB until task 12.3b, when each image's estimate became its reply frame plus
  its decoded image, `workBytes`; one page at the `pagePixels` cap still fits:
  `page_fits_pool`). -/
  poolBytes : Nat := mib 192
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
  /-- Most pixels of one page image in the view (task 12.3b; `View.maxViewPixels`, 2²⁶, before):
  10 Mpx (40 MiB of RGBA). A zoom that would need more is lowered, with the note "zoom limited
  to 10 Mpx per page" in the status line. Chosen by measurement: with 16 Mpx (PDF.js's
  `maxCanvasPixels`) the interleave scenario's 600 % phase peaked at 1386 MiB on macOS, with
  12 Mpx at 1037 MiB, with 10 Mpx (and the 96 MiB cache) at 816–931 MiB over five runs. -/
  pagePixels : Nat := 10485760
  /-- Bytes the viewer's live Tk photos may hold (task 12.3b): the page photos on the canvas and
  the thumbnails, each estimated by `photoBytes`; 352 MiB, room for two page photos at the
  `pagePixels` cap next to the thumbnails (`two_pages_fit_photos`). -/
  photoPoolBytes : Nat := mib 352
  /-- The part of the photo pool page photos leave to the thumbnails: 32 MiB, more than the
  most thumbnails ever kept need (`thumbs_fit_reserve`). -/
  thumbReserve : Nat := mib 32
  /-- Most thumbnail photos kept (`Sidebar.thumbBudget`; checked in the viewer). -/
  thumbsKept : Nat := 40
  /-- The viewer's render cache (`View.Cache` budget; 256 MiB until task 12.3b): 96 MiB, two
  page images at the `pagePixels` cap. -/
  cacheBytes : Nat := mib 96
  /-- What the viewer holds besides the pools and the cache (Tcl/Tk, the open document and its
  parse, fonts, text indexes, code): measured 100 MiB after opening the Transformer paper on
  macOS 26 (`footprint`), budgeted 160 MiB. -/
  baseBytes : Nat := mib 160
  /-- Peak resident memory of the viewer process in the interleave scenario (MiB,
  `scripts/interleave.sh`). -/
  viewerRssMiB : Nat := 1024
  /-- Peak resident memory of one worker process in the interleave scenario (MiB). -/
  workerRssMiB : Nat := 512

/-- The viewer's ceilings. -/
def ceilings : Ceilings := {}

/-- Estimated bytes of a `w × h` RGBA image. -/
def imageBytes (w h : Nat) : Nat := 4 * w * h

/-- **The work estimate of a `w × h` render in flight** (task 12.3b): the worker's reply frame
and the decoded image, both `imageBytes` (the frame is read whole, then the pixels are copied
out of it). -/
def workBytes (w h : Nat) : Nat := 2 * imageBytes w h

/-- **The estimate of one live Tk photo of `w × h` pixels** (task 12.3b): 16 bytes per pixel —
Tk's own 32-bit copy plus what drawing it on the canvas allocates (measured on macOS 26 with
Tk 9: a displayed 3558 × 4604 photo raised the viewer's footprint by 172 MB, ≈ 10.5 bytes per
pixel), and the viewer's own copy of the image it keeps for repainting the marks (4). -/
def photoBytes (w h : Nat) : Nat := 16 * w * h

/-- **The viewer's memory plan**: the pools, the cache and the base fit in the published peak
of the viewer process. -/
theorem plan_fits :
    ceilings.baseBytes + ceilings.poolBytes + ceilings.photoPoolBytes + ceilings.cacheBytes ≤
      mib ceilings.viewerRssMiB := by decide

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
  /-- Task 12.3b: an output of `bytes` built in memory (Save: the original bytes plus the
  update, `Save.outputEstimate`; XFDF export: its text, `Xfdf.exportEstimate`). -/
  | output (bytes : Nat)
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

/-- The bytes an operation may use: images leave `textReserve` to text; an output (built while
the GUI waits, so no text request starts meanwhile) may use the whole pool. -/
def room (c : Ceilings) (p : Pool) : Op → Nat
  | .text => p.ceiling
  | .output _ => p.ceiling
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
scale (full, ½, ¼, ⅛ zoom) that fits, else waits; a text request is reserved or waits; an
output is reserved, waits, or is refused when it is larger than the whole pool. Images are
estimated by `workBytes` (reply frame and decoded image). -/
def Pool.admit (c : Ceilings) (p : Pool) (o : Op) : Outcome :=
  let limit := room c p o
  match o with
  | .page w h =>
    let b := workBytes w h
    if b > limit then .refuse
    else match p.reserveWithin limit b with
      | some (t, q) => .reserved t q 0
      | none => .wait
  | .thumb w h =>
    match thumbScale p limit (workBytes w h) thumbScales with
    | some (k, t, q) => .reserved t q k
    | none => if workBytes w h / 4 ^ 3 > limit then .refuse else .wait
  | .text =>
    if c.textBytes > limit then .refuse
    else match p.reserveWithin limit c.textBytes with
      | some (t, q) => .reserved t q 0
      | none => .wait
  | .output b =>
    if b > limit then .refuse
    else match p.reserveWithin limit b with
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
  | output b =>
    simp only at h
    split at h
    · cases h
    · split at h
      · next hw => cases h; exact key hw
      · cases h

/-- The viewer's largest page image (`pagePixels` = 2²⁴ pixels, its reply frame and decoded
image 128 MiB) fits in the images' room of an empty pool, so a page is never refused, only made
to wait. -/
theorem page_fits_pool (w h : Nat) (hp : w * h ≤ ceilings.pagePixels) :
    workBytes w h ≤ ceilings.poolBytes - ceilings.textReserve := by
  have : ceilings.pagePixels = 10485760 := rfl
  have e : workBytes w h = 8 * (w * h) := by simp only [workBytes, imageBytes]; rw [Nat.mul_assoc]; omega
  rw [e]
  simp only [ceilings, mib] at *
  omega

#guard (Pool.empty (mib 8)).used == 0
-- A page that fits is reserved (its reply frame and image: 2 · 4 · 4 · 5 = 160 bytes), the next
-- one waits, a release lets it in.
#guard
  let c : Ceilings := { poolBytes := 200, textReserve := 20, textBytes := 4 }
  let p := Pool.empty 200
  match p.admit c (.page 4 5) with
  | .reserved t1 p1 0 =>
    (match p1.admit c (.page 4 5) with
     | .wait =>
       (match (p1.release t1).admit c (.page 4 5) with
        | .reserved _ p2 0 => p2.used == 160 && (p1.release t1).used == 0
        | _ => false)
     | _ => false) && p1.used == 160
  | _ => false
-- Images leave the text reserve: text still fits next to a full image room.
#guard
  let c : Ceilings := { poolBytes := 200, textReserve := 20, textBytes := 4 }
  match (Pool.empty 200).admit c (.page 3 7) with
  | .reserved _ p1 _ =>
    (match p1.admit c .text with | .reserved _ p2 _ => p2.used == 172 | _ => false)
  | _ => false
-- A thumbnail lowers its quality instead of waiting: 800 bytes (and 200 at ½ zoom) do not fit
-- in the images' room of 180, 50 (¼ zoom) do.
#guard
  let c : Ceilings := { poolBytes := 200, textReserve := 20, textBytes := 4 }
  match (Pool.empty 200).admit c (.thumb 10 10) with
  | .reserved t _ 2 => t.bytes == 50
  | _ => false
-- Larger than the whole pool: refused.
#guard
  let c : Ceilings := { poolBytes := 200, textReserve := 20, textBytes := 4 }
  match (Pool.empty 200).admit c (.page 10 10) with | .refuse => true | _ => false
-- An output may use the whole pool (no text reserve); larger than the pool: refused; next to
-- work in flight that leaves too little: waits.
#guard
  let c : Ceilings := { poolBytes := 200, textReserve := 20, textBytes := 4 }
  (match (Pool.empty 200).admit c (.output 200) with | .reserved t _ 0 => t.bytes == 200 | _ => false) &&
  (match (Pool.empty 200).admit c (.output 201) with | .refuse => true | _ => false) &&
  (match (Pool.empty 200).admit c (.page 3 7) with
   | .reserved _ p1 _ => (match p1.admit c (.output 100) with | .wait => true | _ => false)
   | _ => false)
-- Releasing twice is releasing once.
#guard
  match (Pool.empty 100).reserve 30 with
  | some (t, p) =>
    match p.reserve 20 with
    | some (_, q) => ((q.release t).release t).used == 20 && (q.release t).used == 20
    | none => false
  | none => false

/-! ## Live photos (task 12.3b)

The viewer's Tk photos — the page photos on the canvas and the thumbnails — hold a reservation
each in a second `Pool` (ceiling `photoPoolBytes`, the same invariant), estimated by
`photoBytes`. A page photo that does not fit first **evicts** the photos of pages that are not
in view (`makeRoom`, farthest from the current page first); when even that is not enough it is
**refused** and the page shows a message instead (nothing is evicted then). Page photos leave
`thumbReserve` to the thumbnails, which therefore always fit. -/

/-- **Make room** for `bytes` within `limit`: releases the tickets of `cands`, in order, until
the pool's reservations and `bytes` fit; the tickets released and the pool after them, or `none`
(nothing released) when even all of `cands` are not enough. -/
def Pool.makeRoom (p : Pool) (limit bytes : Nat) : List Ticket → Option (List Ticket × Pool)
  | [] => if p.used + bytes ≤ limit then some ([], p) else none
  | t :: ts =>
    if p.used + bytes ≤ limit then some ([], p)
    else match (p.release t).makeRoom limit bytes ts with
      | some (es, q) => some (t :: es, q)
      | none => none

/-- **After `makeRoom` the bytes fit.** -/
theorem Pool.makeRoom_fits {limit bytes : Nat} :
    ∀ {p : Pool} {cands es : List Ticket} {q : Pool},
      p.makeRoom limit bytes cands = some (es, q) → q.used + bytes ≤ limit
  | p, [], es, q, h => by
    unfold Pool.makeRoom at h
    split at h
    · cases h; assumption
    · cases h
  | p, t :: ts, es, q, h => by
    unfold Pool.makeRoom at h
    split at h
    · cases h; assumption
    · split at h
      · next es' q' hr => cases h; exact Pool.makeRoom_fits hr
      · cases h

/-- **`makeRoom` releases a prefix of the candidates, and nothing else**: the pool after it is
the pool with exactly those tickets released. -/
theorem Pool.makeRoom_released {limit bytes : Nat} :
    ∀ {p : Pool} {cands es : List Ticket} {q : Pool},
      p.makeRoom limit bytes cands = some (es, q) →
        es <+: cands ∧ q.held = (es.foldl Pool.release p).held
  | p, [], es, q, h => by
    unfold Pool.makeRoom at h
    split at h
    · cases h; exact ⟨List.nil_prefix, rfl⟩
    · cases h
  | p, t :: ts, es, q, h => by
    unfold Pool.makeRoom at h
    split at h
    · cases h; exact ⟨List.nil_prefix, rfl⟩
    · split at h
      · next es' q' hr =>
        cases h
        have ⟨hp, hq⟩ := Pool.makeRoom_released hr
        exact ⟨List.cons_prefix_cons.mpr ⟨rfl, hp⟩, by simpa [List.foldl] using hq⟩
      · cases h

/-- **Admission of a photo** of `bytes` (a thumbnail when `thumb`) to the photo pool `p`, making
room by releasing `cands` (the photos of pages not in view, in eviction order; empty for a
thumbnail): the tickets to release, the new photo's ticket and the pool; `none` when it does
not fit even then (nothing is released). Page photos leave `thumbReserve` to thumbnails. -/
def Pool.admitPhoto (c : Ceilings) (p : Pool) (bytes : Nat) (thumb : Bool)
    (cands : List Ticket) : Option (List Ticket × Ticket × Pool) :=
  let limit := if thumb then p.ceiling else p.ceiling - c.thumbReserve
  match p.makeRoom limit bytes cands with
  | some (es, q) =>
    match q.reserveWithin limit bytes with
    | some (t, q') => some (es, t, q')
    | none => none
  | none => none

/-- Releasing keeps the ceiling. -/
theorem Pool.release_ceiling (p : Pool) (t : Ticket) : (p.release t).ceiling = p.ceiling := rfl

/-- `makeRoom` keeps the ceiling. -/
theorem Pool.makeRoom_ceiling {limit bytes : Nat} :
    ∀ {p : Pool} {cands es : List Ticket} {q : Pool},
      p.makeRoom limit bytes cands = some (es, q) → q.ceiling = p.ceiling
  | p, [], es, q, h => by
    unfold Pool.makeRoom at h
    split at h
    · cases h; rfl
    · cases h
  | p, t :: ts, es, q, h => by
    unfold Pool.makeRoom at h
    split at h
    · cases h; rfl
    · split at h
      · next es' q' hr =>
        cases h
        have := Pool.makeRoom_ceiling hr
        exact this
      · cases h

/-- **A photo is admitted whenever making room succeeds**, and then its ticket is an ordinary
reservation of the pool after the evictions, within the photo's limit (so a page photo never
takes the thumbnails' reserve). -/
theorem Pool.admitPhoto_iff {c : Ceilings} {p : Pool} {b : Nat} {thumb : Bool}
    {cands : List Ticket} {es : List Ticket} {q : Pool}
    (h : p.makeRoom (if thumb then p.ceiling else p.ceiling - c.thumbReserve) b cands =
      some (es, q)) :
    ∃ t q', p.admitPhoto c b thumb cands = some (es, t, q') ∧ q.reserve b = some (t, q') ∧
      q'.used ≤ (if thumb then p.ceiling else p.ceiling - c.thumbReserve) := by
  have hf := Pool.makeRoom_fits h
  have hc := Pool.makeRoom_ceiling h
  cases hr : q.reserve b with
  | none =>
    have := Pool.reserve_none hr
    rw [hc] at this
    split at hf <;> omega
  | some tq =>
    obtain ⟨t, q'⟩ := tq
    have hu := (Pool.reserve_used hr).1
    refine ⟨t, q', ?_, rfl, by omega⟩
    simp only [Pool.admitPhoto, h, Pool.reserveWithin, hf, ↓reduceIte, hr]

/-- A photo admission only ever releases a prefix of the candidates. -/
theorem Pool.admitPhoto_evicts {c : Ceilings} {p : Pool} {b : Nat} {thumb : Bool}
    {cands es : List Ticket} {t : Ticket} {q : Pool}
    (h : p.admitPhoto c b thumb cands = some (es, t, q)) : es <+: cands := by
  simp only [Pool.admitPhoto] at h
  cases hm : p.makeRoom (if thumb then p.ceiling else p.ceiling - c.thumbReserve) b cands with
  | none => simp [hm] at h
  | some eq =>
    obtain ⟨es', q'⟩ := eq
    simp only [hm] at h
    cases hw : q'.reserveWithin (if thumb then p.ceiling else p.ceiling - c.thumbReserve) b with
    | none => simp [hw] at h
    | some tq =>
      simp only [hw, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -, -⟩ := h
      exact (Pool.makeRoom_released hm).1

/-- Two page photos at the `pagePixels` cap fit in the page photos' room (two pages are in
view at once while scrolling). -/
theorem two_pages_fit_photos (w h : Nat) (hp : w * h ≤ ceilings.pagePixels) :
    2 * photoBytes w h ≤ ceilings.photoPoolBytes - ceilings.thumbReserve := by
  have : ceilings.pagePixels = 10485760 := rfl
  have e : photoBytes w h = 16 * (w * h) := by simp only [photoBytes]; rw [Nat.mul_assoc]
  rw [e]
  simp only [ceilings, mib] at *
  omega

/-- The most thumbnails ever kept (`thumbsKept`, each at most 98 × 392 pixels: `Sidebar.thumbW`
wide and at most four times as high) fit in the thumbnails' reserve, so a thumbnail is never
refused for page photos. -/
theorem thumbs_fit_reserve : ceilings.thumbsKept * photoBytes 98 392 ≤ ceilings.thumbReserve := by
  decide

-- Eviction: a 60-byte photo in a 100-byte pool holding 50 + 30 releases the 50 (first
-- candidate) and fits; with only the 30 as candidate it does not fit and nothing is released.
#guard
  match (Pool.empty 100).reserve 50 with
  | some (a, p1) =>
    match p1.reserve 30 with
    | some (b, p2) =>
      let c : Ceilings := { thumbReserve := 0 }
      (match p2.admitPhoto c 60 false [a, b] with
       | some (es, _, q) => es == [a] && q.used == 90
       | none => false) &&
      (p2.admitPhoto c 60 false [b]).isNone
    | none => false
  | none => false
-- Page photos leave the thumbnails' reserve: 95 bytes do not fit as a page in a 100-byte pool
-- with a 10-byte reserve, but do as a thumbnail.
#guard
  let c : Ceilings := { thumbReserve := 10 }
  ((Pool.empty 100).admitPhoto c 95 false []).isNone &&
  ((Pool.empty 100).admitPhoto c 95 true []).isSome

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
