import SafePdf.Core.Text

/-!
# Annotation appearance streams (task 8.3)

Plan.md §6 Phase 8: "Display existing annotations via appearance streams (`/AP`) — reuses the
interpreter." ISO 32000-2 §12.5 (annotations), §12.5.2 (annotation dictionaries: `/Rect`,
`/F`, `/AP`, `/AS`), §12.5.3 (flags), §12.5.5 (appearance streams, the algorithm that maps the
form's `/BBox` into `/Rect`), §12.7.4 (`/FT`, `/T` of fields, inheritable via `/Parent`).

The rules follow MuPDF 1.25.1 (`pdf_sync_annots`, `pdf_process_annot`, `pdf_annot_ap`,
`pdf_annot_transform`, `pdf_run_annot_with_usage`; usage "View", as `mutool draw`).

## Collection (`collect`)

* The page dictionary's own `/Annots` (not inherited), resolved one level; at most
  `maxAnnots` elements are looked at (the rest are recorded as `Skip.overCap`). An element is
  an annotation dictionary, direct or by reference; a reference already seen on this page is
  skipped (`Skip.duplicate`; MuPDF would draw it twice).
* `/Subtype /Link` and `/Subtype /Popup` are never drawn (`pdf_sync_annots` does not even load
  them).
* `/F` (§12.5.3): Invisible (bit 1) or Hidden (bit 2) → skipped; NoView (bit 6) → skipped
  (usage "View"). Print, NoZoom, NoRotate, ReadOnly, Locked … are ignored for display
  (MuPDF: "TODO: NoZoom and NoRotate"; NoRotate is handled by `pdf_run_annot_with_usage` but
  not here — a recorded gap). `/OC` (optional content) is ignored (Tier 2).
* `/Subtype /Widget` is drawn only if both `/FT` and `/T` are found on it or on its `/Parent`
  chain (at most `maxFieldDepth` levels), as MuPDF does.
* `/Rect` must be an array of four numbers (normalised); otherwise `Skip.badRect`.
* **Appearance** (`selectAP`, = `pdf_annot_ap` without interaction state): `/AP /N`; if it is a
  reference to a stream that stream is used, else it is resolved to a dictionary of
  appearance states and the entry named by `/AS` (which must be a reference to a stream) is
  used. No `/AS`, or no stream: `Skip.noAppearance`. Annotations without an appearance are
  **not** synthesised (MuPDF synthesises Square, Line, Highlight, FreeText … via
  `pdf_update_page`): recorded as `Skip.noAppearance`.
* **Order**: MuPDF runs the page's non-widget annotations, then its widgets, each in `/Annots`
  order; `collect` returns them in that order (`Collected.drawn`).

## The matrix A (§12.5.5, `pdf_annot_transform`)

The appearance's `/BBox` is transformed by its `/Matrix` and the bounding box `T` of the
result is taken; `A = [sx 0 0 sy tx ty]` with `sx = (R.x1 − R.x0)/(T.x1 − T.x0)` (0 when `T`
is degenerate in x, as MuPDF), `tx = R.x0 − T.x0 · sx`, likewise `y`. A missing `/BBox`
counts as the empty box `[0 0 0 0]`. Computed exactly over `ℚ` (`aOf`; `aOf_corners`: `A` maps
`T`'s corners to `R`'s), then rounded to `Fixed` (`annotMatrix`).

## Running (`runOne`, `runAppearances`)

Each appearance is run as a form invoked from the page (exactly the `Do` path of
`Run.stepR`): `Run.formJob` with the machine's CTM set to `A` (so the form's CTM is
`/Matrix × A`), the `/BBox` clip, a transparency `/Group` if any, the appearance's own
`/Resources` or else the **page's** (MuPDF pushes the page resources), and the appearance's
object number on the visited path; then `Run.runOps` at nesting fuel
`Limits.maxXObjectDepth − 1`. Each appearance counts as one operator and one form. All
appearances of a page run in one runner state under a shared `Budget` (operators and forms
left), so `runAppearances_ops_le` / `runAppearances_items_le`: at most `bud.ops` operators
and `Paint.maxItems · bud.ops` items in all, however the appearances nest.

## Fonts

Fonts of the appearance resources are collected like the page's (`Text.scanFonts`, worklist
of the appearances' own resource dictionaries, owner = appearance object number) and built on
top of the page's font table (`loadAnnotFonts`); the runner uses their advances, and the
renderer needs them (and glyph sources over `AnnotPage.roots`) to paint the glyph runs.

## Local caps (candidates for `Limits`)

`maxAnnots` 4096 annotations looked at per page, `maxFieldDepth` 32 `/Parent` levels.
-/

namespace SafePdf.Core.Annot

open SafePdf SafePdf.Core
open SafePdf.Core.Content
open SafePdf.Core.Content.Interp (pushAll size_pushAll pendBit)

/-! ## 1. Caps and small helpers -/

/-- Most `/Annots` elements looked at per page (local cap). -/
def maxAnnots : Nat := 4096

/-- Most `/Parent` levels searched for an inheritable field entry (local cap). -/
def maxFieldDepth : Nat := 32

/-- A name from a string. -/
def nm (s : String) : Name := Name.ofString s

/-- A fixed-point number as `ℚ`. -/
def ratOf (x : Fixed) : Rat := (x.raw : Rat) / 1000000

/-- A rational number rounded (half up) to `Fixed`, saturating. -/
def fixOfRat (q : Rat) : Fixed := Fixed.clamp ((q * 1000000 + 1 / 2).floor)

/-- Annotation flag bits (§12.5.3, Table 167). -/
def flagInvisible : Nat := 1
/-- Hidden. -/
def flagHidden : Nat := 2
/-- Print. -/
def flagPrint : Nat := 4
/-- NoView. -/
def flagNoView : Nat := 32

/-- Whether bit `b` (a power of two) is set in `f`. -/
def hasFlag (f b : Nat) : Bool := (f / b) % 2 == 1

/-- The `/F` value as an unsigned 32-bit integer (two's complement of a negative value, as a
C `int` bit test); 0 when absent or not an integer. -/
def flagsOf : Option PdfObject → Nat
  | some (.int i) => (i % 4294967296).toNat
  | _ => 0

/-! ## 2. The matrix A (§12.5.5) -/

/-- A rectangle over `ℚ` (corners `(x0, y0)`, `(x1, y1)`). -/
structure RBox where
  /-- Left. -/
  x0 : Rat
  /-- Bottom. -/
  y0 : Rat
  /-- Right. -/
  x1 : Rat
  /-- Top. -/
  y1 : Rat
  deriving Repr, DecidableEq

/-- A `Fixed` rectangle over `ℚ`. -/
def RBox.ofFixed (b : Fixed × Fixed × Fixed × Fixed) : RBox :=
  ⟨ratOf b.1, ratOf b.2.1, ratOf b.2.2.1, ratOf b.2.2.2⟩

/-- Minimum of four. -/
def min4 (a b c d : Rat) : Rat := min (min a b) (min c d)

/-- Maximum of four. -/
def max4 (a b c d : Rat) : Rat := max (max a b) (max c d)

/-- The bounding box of `b` transformed by `m` (exactly; `fz_transform_rect`). -/
def tBox (m : Matrix) (b : RBox) : RBox :=
  let a := ratOf m.a
  let bb := ratOf m.b
  let c := ratOf m.c
  let d := ratOf m.d
  let e := ratOf m.e
  let f := ratOf m.f
  let px := fun (x y : Rat) => a * x + c * y + e
  let py := fun (x y : Rat) => bb * x + d * y + f
  ⟨min4 (px b.x0 b.y0) (px b.x1 b.y0) (px b.x0 b.y1) (px b.x1 b.y1),
   min4 (py b.x0 b.y0) (py b.x1 b.y0) (py b.x0 b.y1) (py b.x1 b.y1),
   max4 (px b.x0 b.y0) (px b.x1 b.y0) (px b.x0 b.y1) (px b.x1 b.y1),
   max4 (py b.x0 b.y0) (py b.x1 b.y0) (py b.x0 b.y1) (py b.x1 b.y1)⟩

/-- The parameters of `A = [sx 0 0 sy tx ty]`. -/
structure AParams where
  /-- x scale. -/
  sx : Rat
  /-- y scale. -/
  sy : Rat
  /-- x translation. -/
  tx : Rat
  /-- y translation. -/
  ty : Rat
  deriving Repr, DecidableEq

/-- **Matrix A** mapping the transformed box `t` onto the annotation rectangle `r`
(`pdf_annot_transform`: a degenerate side scales by 0). -/
def aOf (r t : RBox) : AParams :=
  let sx := if t.x1 = t.x0 then 0 else (r.x1 - r.x0) / (t.x1 - t.x0)
  let sy := if t.y1 = t.y0 then 0 else (r.y1 - r.y0) / (t.y1 - t.y0)
  ⟨sx, sy, r.x0 - t.x0 * sx, r.y0 - t.y0 * sy⟩

/-- **§12.5.5 correctness**: for a non-degenerate transformed box `t`, `A` maps `t`'s lower-left
corner to `r`'s lower-left corner and its upper-right corner to `r`'s upper-right corner (so,
being a positive-or-negative axis scaling plus translation, it maps `t` onto `r`). -/
theorem aOf_corners (r t : RBox) (hx : t.x1 ≠ t.x0) (hy : t.y1 ≠ t.y0) :
    t.x0 * (aOf r t).sx + (aOf r t).tx = r.x0 ∧ t.x1 * (aOf r t).sx + (aOf r t).tx = r.x1 ∧
    t.y0 * (aOf r t).sy + (aOf r t).ty = r.y0 ∧ t.y1 * (aOf r t).sy + (aOf r t).ty = r.y1 := by
  have hx' : t.x1 - t.x0 ≠ 0 := fun h => hx (by grind)
  have hy' : t.y1 - t.y0 ≠ 0 := fun h => hy (by grind)
  simp only [aOf, hx, hy, ite_false]
  exact ⟨by grind, by grind, by grind, by grind⟩

/-- `A` as a `Fixed` matrix (entries rounded once). -/
def AParams.matrix (p : AParams) : Matrix :=
  ⟨fixOfRat p.sx, Fixed.zero, Fixed.zero, fixOfRat p.sy, fixOfRat p.tx, fixOfRat p.ty⟩

/-- **The annotation matrix** of rectangle `rect` and an appearance with `/BBox` `bbox`
(`none`: the empty box) and `/Matrix` `fm`. -/
def annotMatrix (rect : RBox) (bbox : Option (Fixed × Fixed × Fixed × Fixed)) (fm : Matrix) :
    Matrix :=
  let b := match bbox with
    | some bb => RBox.ofFixed bb
    | none => ⟨0, 0, 0, 0⟩
  (aOf rect (tBox fm b)).matrix

/-! ## 3. Collecting a page's annotations -/

/-- Why an annotation is not drawn. -/
inductive Skip where
  /-- Not a dictionary (or a reference to one). -/
  | notDict
  /-- A reference already listed earlier in `/Annots`. -/
  | duplicate
  /-- Beyond `maxAnnots`. -/
  | overCap
  /-- `/Subtype /Link` (never drawn). -/
  | link
  /-- `/Subtype /Popup` (never drawn). -/
  | popup
  /-- `/F` Invisible or Hidden. -/
  | hidden
  /-- `/F` NoView. -/
  | noView
  /-- A widget without inheritable `/FT` and `/T`. -/
  | noField
  /-- `/Rect` missing or malformed. -/
  | badRect
  /-- No usable normal appearance (`/AP /N` stream, or state entry chosen by `/AS`); MuPDF
  synthesises some of these (not done here). -/
  | noAppearance
  deriving DecidableEq, Repr, Inhabited

/-- An annotation to draw: what was parsed, the chosen appearance stream and matrix A. -/
structure Drawable where
  /-- Position in `/Annots`. -/
  index : Nat
  /-- Annotation object number (0 for a direct dictionary). -/
  num : Nat
  /-- `/Subtype` (empty name when absent). -/
  subtype : Name
  /-- `/Rect`, normalised. -/
  rect : RBox
  /-- `/F`. -/
  flags : Nat
  /-- `/AS`. -/
  state : Option Name
  /-- Appearance stream object number. -/
  apNum : Nat
  /-- Appearance stream generation. -/
  apGen : Nat
  /-- The appearance stream. -/
  ap : Stream
  /-- Matrix A (§12.5.5). -/
  matrix : Matrix
  /-- `/Subtype /Widget` (drawn after the other annotations). -/
  widget : Bool

/-- What one `/Annots` element gives. -/
inductive Outcome where
  /-- Drawn. -/
  | draw (d : Drawable)
  /-- Skipped, with the reason. -/
  | skip (r : Skip)

/-- The drawable of an outcome. -/
def Outcome.drawable? : Outcome → Option Drawable
  | .draw d => some d
  | .skip _ => none

/-- The skip reason of an outcome. -/
def Outcome.skip? : Outcome → Option Skip
  | .draw _ => none
  | .skip r => some r

/-- A name value (resolved one level). -/
def nameOf {σ : Type} (src : Source σ) (s : σ) (o : Option PdfObject) : Option Name × σ :=
  match o with
  | none => (none, s)
  | some o =>
    match Run.resolve src s o with
    | (.name n, s) => (some n, s)
    | (_, s) => (none, s)

/-- Whether key `k` is present (non-null) on `d` or on its `/Parent` chain, at most `fuel`
levels up (`pdf_dict_get_inheritable`). -/
def inheritable {σ : Type} (src : Source σ) (k : Name) : Nat → Dict → σ → Bool × σ
  | 0, d, s => ((Dict.get? d k).isSome, s)
  | f + 1, d, s =>
    if (Dict.get? d k).isSome then (true, s)
    else
      match Dict.get? d (nm "Parent") with
      | none => (false, s)
      | some p =>
        match Run.resolve src s p with
        | (.dict pd, s) => inheritable src k f pd s
        | (_, s) => (false, s)

/-- A normalised rectangle from four numbers. -/
def rectOf (o : PdfObject) : Option RBox :=
  match Run.numsOf o with
  | some [a, b, c, d] =>
    let (x0, x1) := (min (ratOf a) (ratOf c), max (ratOf a) (ratOf c))
    let (y0, y1) := (min (ratOf b) (ratOf d), max (ratOf b) (ratOf d))
    some ⟨x0, y0, x1, y1⟩
  | _ => none

/-- A reference to a stream: the stream. -/
def streamRef {σ : Type} (src : Source σ) (s : σ) : PdfObject → Option (Nat × Nat × Stream) × σ
  | .ref n g =>
    match src.fetch s n g with
    | (.ok (.stream st), s) => (some (n, g, st), s)
    | (_, s) => (none, s)
  | _ => (none, s)

/-- **The normal appearance** (`pdf_annot_ap` for a passive annotation): `/AP /N` if it is a
reference to a stream, else the entry of the state dictionary `/AP /N` named by `/AS`. -/
def selectAP {σ : Type} (src : Source σ) (s : σ) (ad : Dict) (state : Option Name) :
    Option (Nat × Nat × Stream) × σ :=
  match Dict.get? ad (nm "AP") with
  | none => (none, s)
  | some apo =>
    let (ap, s) := Run.dictOf src s apo
    match Dict.get? ap (nm "N") with
    | none => (none, s)
    | some n =>
      match streamRef src s n with
      | (some r, s) => (some r, s)
      | (none, s) =>
        match state with
        | none => (none, s)
        | some st =>
          let (sd, s) := Run.dictOf src s n
          match Dict.get? sd st with
          | some e => streamRef src s e
          | none => (none, s)

/-- Parse one annotation dictionary `ad` (object `num`, position `idx`). -/
def parseDict {σ : Type} (src : Source σ) (s : σ) (idx num : Nat) (ad : Dict) : Outcome × σ :=
  let (sub, s) := nameOf src s (Dict.get? ad (nm "Subtype"))
  let subtype := sub.getD (nm "")
  if subtype = nm "Link" then (.skip .link, s)
  else if subtype = nm "Popup" then (.skip .popup, s)
  else
    let (fo, s) := match Dict.get? ad (nm "F") with
      | some o => let r := Run.resolve src s o; (some r.1, r.2)
      | none => (none, s)
    let flags := flagsOf fo
    if hasFlag flags flagInvisible || hasFlag flags flagHidden then (.skip .hidden, s)
    else if hasFlag flags flagNoView then (.skip .noView, s)
    else
      let widget := subtype = nm "Widget"
      let (hasFT, s) := inheritable src (nm "FT") maxFieldDepth ad s
      let (hasT, s) := inheritable src (nm "T") maxFieldDepth ad s
      if widget && !(hasFT && hasT) then (.skip .noField, s)
      else
        let (ro, s) := match Dict.get? ad (nm "Rect") with
          | some o => Run.resolve src s o
          | none => (.null, s)
        match rectOf ro with
        | none => (.skip .badRect, s)
        | some rect =>
          let (state, s) := nameOf src s (Dict.get? ad (nm "AS"))
          match selectAP src s ad state with
          | (none, s) => (.skip .noAppearance, s)
          | (some (n, g, st), s) =>
            let m := annotMatrix rect (Run.bboxOf st.dict) (Run.formMatrix st.dict)
            (.draw ⟨idx, num, subtype, rect, flags, state, n, g, st, m, widget⟩, s)

/-- Parse one `/Annots` element (`seen`: annotation object numbers already listed). -/
def parseOne {σ : Type} (src : Source σ) (s : σ) (idx : Nat) (seen : List Nat) (o : PdfObject) :
    Outcome × σ :=
  match o with
  | .ref n g =>
    if seen.contains n then (.skip .duplicate, s)
    else
      match src.fetch s n g with
      | (.ok (.obj (.dict ad)), s) => parseDict src s idx n ad
      | (_, s) => (.skip .notDict, s)
  | .dict ad => parseDict src s idx 0 ad
  | _ => (.skip .notDict, s)

/-- Object number of a reference (0 otherwise). -/
def refNum : PdfObject → Nat
  | .ref n _ => n
  | _ => 0

/-- Parse the elements in order: one outcome per element. -/
def parseAll {σ : Type} (src : Source σ) :
    Nat → List Nat → List PdfObject → σ → List (Nat × Outcome) × σ
  | _, _, [], s => ([], s)
  | idx, seen, o :: os, s =>
    let (r, s) := parseOne src s idx seen o
    let (rs, s) := parseAll src (idx + 1) (refNum o :: seen) os s
    ((idx, r) :: rs, s)

/-- `parseAll` gives exactly one outcome per element. -/
theorem parseAll_length {σ : Type} (src : Source σ) :
    ∀ (idx : Nat) (seen : List Nat) (os : List PdfObject) (s : σ),
      (parseAll src idx seen os s).1.length = os.length
  | _, _, [], _ => rfl
  | idx, seen, o :: os, s => by
    simp only [parseAll, List.length_cons]
    rw [parseAll_length src (idx + 1) (refNum o :: seen) os]

/-- The annotations of a page. -/
structure Collected where
  /-- To draw, in MuPDF's order: non-widgets, then widgets, each in `/Annots` order. -/
  drawn : List Drawable
  /-- Skipped elements with their positions. -/
  skipped : List (Nat × Skip)

/-- Stable split: non-widgets first, then widgets. -/
def widgetsLast (ds : List Drawable) : List Drawable :=
  ds.filter (fun d => !d.widget) ++ ds.filter (·.widget)

/-- `widgetsLast` keeps the count. -/
theorem widgetsLast_length (ds : List Drawable) : (widgetsLast ds).length = ds.length := by
  unfold widgetsLast
  rw [List.length_append]
  induction ds with
  | nil => rfl
  | cons x xs ih => cases h : x.widget <;> simp [h] <;> omega

/-- **Collect the annotations** of a page dictionary `pd` (§12.5; see the module doc). -/
def collect {σ : Type} (src : Source σ) (s : σ) (pd : Dict) : Collected × σ :=
  let (arr, s) := match Dict.get? pd (nm "Annots") with
    | some o => Run.resolve src s o
    | none => (.null, s)
  let xs := match arr with
    | .array xs => xs
    | _ => []
  let (rs, s) := parseAll src 0 [] (xs.take maxAnnots) s
  let over := (List.range (xs.length - maxAnnots)).map fun i => (maxAnnots + i, Skip.overCap)
  ({ drawn := widgetsLast (rs.filterMap (·.2.drawable?)),
     skipped := rs.filterMap (fun (i, r) => r.skip?.map (i, ·)) ++ over }, s)

/-- **Annotation count bound**: at most `maxAnnots` annotations are drawn per page. -/
theorem collect_drawn_le {σ : Type} (src : Source σ) (s : σ) (pd : Dict) :
    (collect src s pd).1.drawn.length ≤ maxAnnots := by
  simp only [collect]
  generalize (match Dict.get? pd (nm "Annots") with
    | some o => Run.resolve src s o
    | none => (PdfObject.null, s)) = a
  obtain ⟨arr, s1⟩ := a
  generalize (match arr with
    | .array xs => xs
    | _ => []) = xs
  have hl := parseAll_length src 0 [] (xs.take maxAnnots) s1
  generalize parseAll src 0 [] (xs.take maxAnnots) s1 = p at hl
  obtain ⟨rs, s2⟩ := p
  simp only at hl ⊢
  rw [widgetsLast_length]
  have h1 := List.length_filterMap_le (fun (x : Nat × Outcome) => x.2.drawable?) rs
  have h2 := List.length_take_le maxAnnots xs
  omega

/-! ## 4. Running the appearances -/

open Run (Good)

/-- **Run one appearance** as a form invoked from the page frame `fr` (the `Do` path of
`Run.stepR`, with CTM `A`): one operator and one form charged; skipped (with a warning) when
the operator cap is reached, the form budget is spent, or the stream does not decode. The
runner's machine is restored afterwards. -/
def runOne {σ ω : Type} (env : Env σ ω) (fuel : Nat) (fr : Frame) (st : St σ ω) (d : Drawable) :
    St σ ω :=
  match st with
  | ⟨m, items, warnings, unsupported, ops, forms, truncated, s, obs⟩ =>
    if env.cfg.limits.maxOpsPerPage ≤ ops then
      ⟨m, items, if truncated then warnings else warnings + 1, unsupported, ops, forms, true,
        s, obs⟩
    else if env.maxForms ≤ forms then
      ⟨m, items, warnings + 1, unsupported, ops, forms, truncated, s, obs⟩
    else
      match env.src.decode s d.apNum d.ap with
      | (.error _, s) => ⟨m, items, warnings + 1, unsupported, ops, forms, truncated, s, obs⟩
      | (.ok bytes, s) =>
        match Run.formJob env fr (Run.formMachine { ctm := d.matrix }) d.apNum d.apGen d.ap.dict
            bytes s with
        | .done _ w s' => ⟨m, items, warnings + w, unsupported, ops, forms, truncated, s', obs⟩
        | .form job s' =>
          let w := job.w + job.tokW
          match Run.runOps env fuel (job.frame fr)
              ⟨job.machine, pushAll items job.pre, warnings + w, unsupported, ops + 1,
                forms + 1, truncated, s', obs⟩ job.ops with
          | ⟨_, items2, w2, u2, ops2, forms2, tr2, s2, obs2⟩ =>
            ⟨m, pushAll items2 job.post, w2, u2, ops2, forms2, tr2, s2, obs2⟩

/-- `runOne` keeps the runner's bound invariant (`Run.Good`: items per operator, operator
cap). -/
theorem runOne_good {σ ω : Type} (env : Env σ ω) (fuel : Nat) (fr : Frame) (k : Nat)
    (st : St σ ω) (d : Drawable) (h : Good env.cfg.limits k st) :
    Good env.cfg.limits k (runOne env fuel fr st d) := by
  obtain ⟨m, items, warnings, unsupported, ops, forms, truncated, s, obs⟩ := st
  unfold Good at h ⊢
  simp only at h
  unfold runOne
  by_cases hcap : env.cfg.limits.maxOpsPerPage ≤ ops
  · simp only [hcap, ↓reduceIte]
    exact h
  · simp only [hcap, ↓reduceIte]
    by_cases hf : env.maxForms ≤ forms
    · simp only [hf, ↓reduceIte]
      exact h
    · simp only [hf, ↓reduceIte]
      split
      · exact h
      · split
        · exact h
        · rename_i job s' _
          have hcl := Run.FormJob.pre_post_le job
          have h1 : Good env.cfg.limits (pendBit m + k + job.post.length)
              ⟨job.machine, pushAll items job.pre, warnings + (job.w + job.tokW), unsupported,
                ops + 1, forms + 1, truncated, s', obs⟩ := by
            unfold Good
            simp only [size_pushAll, Run.FormJob.machine, Run.formMachine, pendBit,
              Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Paint.maxItems] at h hcl ⊢
            omega
          have h2 := Run.runOps_good env fuel _ (job.frame fr) _ job.ops h1
          revert h2
          rcases Run.runOps env fuel (job.frame fr)
              ⟨job.machine, pushAll items job.pre, warnings + (job.w + job.tokW), unsupported,
                ops + 1, forms + 1, truncated, s', obs⟩ job.ops with
            ⟨m2, items2, w2, u2, ops2, forms2, tr2, s2, obs2⟩
          intro h2
          unfold Good at h2
          simp only [size_pushAll] at h2 ⊢
          omega

/-- What is left of the page's operator and form budgets for the appearances. -/
structure Budget where
  /-- Operators. -/
  ops : Nat
  /-- Form expansions. -/
  forms : Nat
  deriving Repr, Inhabited

/-- The environment `env` with its operator cap and form cap replaced by the budget. -/
def budgetEnv {σ ω : Type} (env : Env σ ω) (bud : Budget) : Env σ ω :=
  { env with cfg := { env.cfg with limits := { env.cfg.limits with maxOpsPerPage := bud.ops } },
             maxForms := bud.forms }

/-- The page frame: the page's resources, nothing visited, owner 0, identity base. -/
def pageFrame (pageRes : Dict) : Frame := ⟨pageRes, [], 0, 0, Matrix.identity⟩

/-- **Run the appearances** `ds` in order from a fresh runner state, all under the shared
budget `bud`, appearances without own `/Resources` resolving in `pageRes`. The items are in
page space, to be painted after the page content. -/
def runAppearances {σ ω : Type} (env : Env σ ω) (bud : Budget) (pageRes : Dict)
    (ds : List Drawable) (s : σ) (obs : ω) : St σ ω :=
  ds.foldl (runOne (budgetEnv env bud) (env.cfg.limits.maxXObjectDepth - 1) (pageFrame pageRes))
    (St.init s obs)

/-- Folding `runOne` keeps `Good`. -/
theorem foldl_runOne_good {σ ω : Type} (env : Env σ ω) (fuel : Nat) (fr : Frame) (k : Nat) :
    ∀ (l : List Drawable) (st : St σ ω), Good env.cfg.limits k st →
      Good env.cfg.limits k (l.foldl (runOne env fuel fr) st)
  | [], _, h => h
  | d :: rest, st, h => foldl_runOne_good env fuel fr k rest _ (runOne_good env fuel fr k st d h)

/-- **Operator bound**: the appearances of a page execute at most `bud.ops` operators in all
(each appearance counts as one), however they nest. -/
theorem runAppearances_ops_le {σ ω : Type} (env : Env σ ω) (bud : Budget) (pageRes : Dict)
    (ds : List Drawable) (s : σ) (obs : ω) :
    (runAppearances env bud pageRes ds s obs).ops ≤ bud.ops :=
  (foldl_runOne_good (budgetEnv env bud) _ _ 0 ds _ (St.init_good _ s obs)).2

/-- **Item bound**: the appearances of a page produce at most `Paint.maxItems · bud.ops` display
items in all. -/
theorem runAppearances_items_le {σ ω : Type} (env : Env σ ω) (bud : Budget) (pageRes : Dict)
    (ds : List Drawable) (s : σ) (obs : ω) :
    (runAppearances env bud pageRes ds s obs).items.size ≤ Paint.maxItems * bud.ops := by
  have h := foldl_runOne_good (budgetEnv env bud) (env.cfg.limits.maxXObjectDepth - 1)
    (pageFrame pageRes) 0 ds _ (St.init_good _ s obs)
  unfold Good at h
  have h3 := Nat.mul_le_mul_left Paint.maxItems h.2
  unfold runAppearances
  simp only [budgetEnv] at h h3 ⊢
  omega

/-! ## 5. Fonts and entry points -/

/-- The appearances' own resource dictionaries, by appearance object number (each once):
the roots of the font scan. Appearances without `/Resources` use the page's fonts. -/
def apRoots {σ : Type} (src : Source σ) (s : σ) (ds : List Drawable) : List (Nat × Dict) × σ :=
  ds.foldl (fun (acc : List (Nat × Dict) × σ) d =>
    if acc.1.any (·.1 == d.apNum) then acc else
    match Run.formResources src acc.2 d.ap.dict [] 0 d.apNum with
    | ((rd, ow), s) => if ow = d.apNum ∧ d.apNum ≠ 0 then (acc.1 ++ [(d.apNum, rd)], s)
      else (acc.1, s)) ([], s)

/-- **Fonts of the appearances**: every font `Text.scanFonts` collects from `roots` (and the
forms they use), added to the page's table `pageFonts` (a font already there is not built
again); at most `Text.maxFonts` new font objects (as `Text.loadFonts`). -/
def loadAnnotFonts {σ : Type} (limits : Limits) (src : Source σ) (s : σ)
    (pageFonts : Text.FontTable) (roots : List (Nat × Dict)) : Text.FontTable × σ :=
  let (es, s) := Text.scanFonts src (Text.maxFormFonts + 1 + roots.length) roots [] [] s
  let (t, _, s) := es.foldl (fun (acc : Text.FontTable × Nat × σ) (e : Text.FontEntry) =>
    let (t, k, s) := acc
    let (key, keys, o) := e
    let add (fi : Text.FontInfo) : Text.FontTable :=
      t ++ (keys.filter fun k' => (t.lookup k').isNone).map fun k' => (k', fi)
    match t.lookup key with
    | some fi => (add fi, k, s)
    | none =>
      if Text.maxFonts ≤ k then acc
      else
        let (fi, s') := Text.buildFont limits src s o
        (add fi, k + 1, s')) (pageFonts, 0, s)
  (t, s)

/-- The annotations of a page, run. -/
structure AnnotPage where
  /-- Display items of the appearances, page space, in drawing order (paint after the page). -/
  items : DisplayList
  /-- The page's font table extended with the appearances' fonts. -/
  fonts : Text.FontTable
  /-- The appearances' own resource dictionaries (for glyph sources: scan them like the page's
  resources). -/
  roots : List (Nat × Dict)
  /-- What was drawn and skipped. -/
  collected : Collected
  /-- Runner warnings. -/
  warnings : Nat
  /-- Operators executed (each appearance counts one). -/
  ops : Nat
  /-- Forms expanded (each appearance counts one). -/
  forms : Nat
  /-- The operator budget ran out. -/
  truncated : Bool

/-- **Annotations of a page** (page dictionary `pd`, resources `pageRes`, the page's font
table `pageFonts`), run under the budget `bud`. Total. -/
def pageAnnots {σ : Type} (limits : Limits) (src : Source σ) (s : σ) (pd pageRes : Dict)
    (pageFonts : Text.FontTable) (bud : Budget) : AnnotPage × σ :=
  let (c, s) := collect src s pd
  let (roots, s) := apRoots src s c.drawn
  let (fonts, s) := loadAnnotFonts limits src s pageFonts roots
  let st := runAppearances (Text.textEnv limits src fonts) bud pageRes c.drawn s ()
  (⟨st.items, fonts, roots, c, st.warnings, st.ops, st.forms, st.truncated⟩, st.s)

/-- **Bounds of `pageAnnots`**: at most `maxAnnots` annotations drawn, at most `bud.ops`
operators and `Paint.maxItems · bud.ops` items. -/
theorem pageAnnots_bounds {σ : Type} (limits : Limits) (src : Source σ) (s : σ) (pd pageRes : Dict)
    (pageFonts : Text.FontTable) (bud : Budget) :
    (pageAnnots limits src s pd pageRes pageFonts bud).1.collected.drawn.length ≤ maxAnnots ∧
    (pageAnnots limits src s pd pageRes pageFonts bud).1.ops ≤ bud.ops ∧
    (pageAnnots limits src s pd pageRes pageFonts bud).1.items.size ≤ Paint.maxItems * bud.ops :=
  ⟨collect_drawn_le src s pd, runAppearances_ops_le _ _ _ _ _ _,
   runAppearances_items_le _ _ _ _ _ _⟩

/-- **Annotations of a page of an opened document**, charging the decode `budget`; `pageFonts`
is the page's font table (`Text.PageText.fonts`), `bud` what is left of the page's operator
and form budgets. -/
def docAnnots (limits : Limits) (doc : Doc.Doc) (page : Doc.Page) (pageFonts : Text.FontTable)
    (bud : Budget) (budget : Filter.Budget) : AnnotPage × Filter.Budget :=
  let src := Text.docSource limits doc
  let (pd, b) := Run.dictOf src budget (.ref page.num page.gen)
  pageAnnots limits src b pd (page.resources.getD []) pageFonts bud

/-! ## 6. Checks -/

-- A 10 × 10 box into the rectangle [40, 60]²: scale 2, translation 40.
#guard aOf ⟨40, 40, 60, 60⟩ ⟨0, 0, 10, 10⟩ == ⟨2, 2, 40, 40⟩
-- A box rotated by 90° (`[0 1 -1 0 0 0]`): [0, 40] × [0, 20] becomes [−20, 0] × [0, 40].
#guard tBox ⟨Fixed.zero, Fixed.one, Fixed.neg Fixed.one, Fixed.zero, Fixed.zero, Fixed.zero⟩
  ⟨0, 0, 40, 20⟩ == ⟨-20, 0, 0, 40⟩
-- A degenerate box scales by 0.
#guard (aOf ⟨0, 0, 10, 10⟩ ⟨5, 0, 5, 10⟩).sx == 0
#guard hasFlag 2 flagHidden && !hasFlag 4 flagHidden && hasFlag (flagsOf (some (.int (-1)))) flagNoView
#guard fixOfRat (29 / 5) == Fixed.ofDecimal ⟨58, 1⟩

end SafePdf.Core.Annot
