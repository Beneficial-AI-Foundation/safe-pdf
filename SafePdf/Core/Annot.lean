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
  not here — a recorded gap). `/OC` (optional content): hidden in the default configuration →
  `Skip.ocHidden` (task 8.3c, `ocHidden`).
* `/Subtype /Widget` is drawn only if both `/FT` and `/T` are found on it or on its `/Parent`
  chain (at most `maxFieldDepth` levels), as MuPDF does.
* `/Rect` must be an array of four numbers (normalised); otherwise `Skip.badRect`.
* **Appearance** (`selectAP`, = `pdf_annot_ap` without interaction state): `/AP /N`; if it is a
  reference to a stream that stream is used, else it is resolved to a dictionary of
  appearance states and the entry named by `/AS` (which must be a reference to a stream) is
  used. No `/AS`, or no stream: a non-widget Square, Circle, Line, Ink, Highlight, Underline
  or StrikeOut gets a **synthesised** appearance (task 8.3b, `synthesize`, as MuPDF's
  `pdf_update_appearance`); anything else is `Skip.noAppearance` (MuPDF also synthesises
  FreeText, Text icons, Polygon, Caret, Stamp, Squiggly, Redact and widgets: not done here).
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
and `Paint.maxItems · bud.ops` items in all, however the appearances nest. The budget is what
the page run left (`Budget.after`, from `Text.PageText.ops`/`forms`): page and annotations
share one `Limits.maxOpsPerPage` (`docAnnots_shared_ops`).

## Text (task 8.3b)

`extractDocPageAnnots` appends the glyphs of the annotation items to the page's (`withAnnots`;
MuPDF's `-F txt` includes annotation text), item indices continuing after the page's items.

Not done (recorded): `/F` NoZoom and NoRotate (MuPDF: NoRotate in `pdf_run_annot_with_usage`
only).

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
  /-- `/OC` hidden in the default optional-content configuration (task 8.3c). -/
  | ocHidden
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
  /-- A synthesised appearance (`synthesize`): `ap.data` is the decoded content, not a stream
  of the document. -/
  synth : Bool := false

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

/-! ### Optional content of annotations (task 8.3c; §8.11, MuPDF `pdf_is_ocg_hidden`)

An annotation whose `/OC` names an optional content group (or membership dictionary) that is
hidden in the default configuration is not drawn (MuPDF `pdf_process_annot`, usage "View").
The configuration is read like `pdf_read_ocg` + `pdf_select_layer_config(doc, 0)`: the catalog's
`/OCProperties`, its `/OCGs` (each initially ON), the configuration `/Configs [0]` if present,
else `/D` (neither: no optional content at all, as MuPDF's "broken configuration" path);
`/BaseState /OFF` turns every group off (anything else: on), then `/ON` and `/OFF` (later wins);
the configuration's `/Intent` is kept.

`ocHidden` follows `pdf_is_ocg_hidden_imp`: no groups described → visible; a name (the
annotation has no resource dictionary) or nothing → visible; an `/OCG` is hidden when its
`/Intent` (name, array, or absent = `View`) is not included by the configuration's intent, else
by `/Usage /View /ViewState` (`/OFF` hidden, `/ON` visible), else by its default state (groups
are matched by reference, not resolved, as MuPDF); an `/OCMD` with an array `/VE` is visible
(MuPDF's FIXME), else `/P` (`AllOn`, `AnyOff`, `AllOff`, default `AnyOn`) over `/OCGs` (an array,
or a single group) with MuPDF's literal `combine` arithmetic, which differs from §8.11.2.2 for
arrays: `AllOn` is visible when any group is on, `AnyOff` hidden when any group is on
(pixel-checked against `mutool draw`). Recursion depth is bounded by `maxOCDepth` (MuPDF: a cycle check; a cycle
or exhausted depth is visible). At most `maxOCGs` groups are read. -/

/-- Most `/OCGs` entries read (local cap). -/
def maxOCGs : Nat := 4096

/-- Most nesting levels of membership dictionaries followed (local cap). -/
def maxOCDepth : Nat := 32

/-- The default optional-content configuration (`pdf_ocg_descriptor`). -/
structure OCDesc where
  /-- The `/OCGs` entries (as written: references) with their state (`true` = ON). -/
  ocgs : List (PdfObject × Bool) := []
  /-- The configuration's `/Intent`, resolved one level (`null` when absent). -/
  intent : PdfObject := .null

/-- The object number and generation of a reference. -/
def refKey : PdfObject → Option (Nat × Nat)
  | .ref n g => some (n, g)
  | _ => none

/-- An object resolved one level, `null` when absent. -/
def resolveOpt {σ : Type} (src : Source σ) (s : σ) : Option PdfObject → PdfObject × σ
  | none => (.null, s)
  | some o => Run.resolve src s o

/-- **Read the default configuration** from the catalog `cat` (see the section doc). -/
def readOC {σ : Type} (src : Source σ) (s : σ) (cat : Dict) : OCDesc × σ :=
  match resolveOpt src s (Dict.get? cat (nm "OCProperties")) with
  | (.dict prop, s) =>
    let (groups, s) := match resolveOpt src s (Dict.get? prop (nm "OCGs")) with
      | (.array xs, s) => (xs.take maxOCGs, s)
      | (_, s) => ([], s)
    let (cfg0, s) := match resolveOpt src s (Dict.get? prop (nm "Configs")) with
      | (.array xs, s) => (xs[0]?, s)
      | (_, s) => (none, s)
    match cfg0.or (Dict.get? prop (nm "D")) with
    | none => ({}, s)
    | some c =>
      let (cd, s) := Run.dictOf src s c
      let (intent, s) := resolveOpt src s (Dict.get? cd (nm "Intent"))
      let (base, s) := nameOf src s (Dict.get? cd (nm "BaseState"))
      let keys := fun (s : σ) (k : String) =>
        match resolveOpt src s (Dict.get? cd (nm k)) with
        | (.array xs, s) => (xs.filterMap refKey, s)
        | (_, s) => ([], s)
      let (onK, s) := keys s "ON"
      let (offK, s) := keys s "OFF"
      let st0 := base != some (nm "OFF")
      let state := fun (o : PdfObject) =>
        match refKey o with
        | some k => if offK.contains k then false else if onK.contains k then true else st0
        | none => st0
      ({ ocgs := groups.map fun o => (o, state o), intent }, s)
  | (_, s) => ({}, s)

/-- `ocg_intents_include`: whether intent `n` is included by the configuration's intent. -/
def intentIncludes (desc : PdfObject) (n : Name) : Bool :=
  if n = nm "All" then true else
  match desc with
  | .null => n = nm "View"
  | .name i => i = nm "All" || i = n
  | .array xs => xs.any fun x => match x with
    | .name i => i = nm "All" || i = n
    | _ => n = nm ""
  | _ => false

/-- The `/P` policy of a membership dictionary as MuPDF's `combine` bits (bit 0: AND, bit 1:
true means off). -/
def combineOf (p : Option Name) : Nat :=
  if p = some (nm "AllOn") then 1 else if p = some (nm "AnyOff") then 2
  else if p = some (nm "AllOff") then 3 else 0

/-- **Whether optional content `o` is hidden** (usage "View"; see the section doc), following
membership dictionaries at most `fuel` levels deep. -/
def ocHidden {σ : Type} (src : Source σ) (desc : OCDesc) : Nat → PdfObject → σ → Bool × σ
  | 0, _, s => (false, s)
  | f + 1, o, s =>
    if desc.ocgs.isEmpty then (false, s) else
    match o with
    | .null => (false, s)
    | .name _ => (false, s)
    | _ =>
      match Run.resolve src s o with
      | (.dict d, s) =>
        let (ty, s) := nameOf src s (Dict.get? d (nm "Type"))
        if ty = some (nm "OCG") then
          let dflt := match refKey o with
            | some k => match desc.ocgs.find? (fun e => refKey e.1 == some k) with
              | some e => !e.2
              | none => false
            | none => false
          let (it, s) := resolveOpt src s (Dict.get? d (nm "Intent"))
          let ok := match it with
            | .name n => intentIncludes desc.intent n
            | .array xs => xs.any fun x => match x with
              | .name n => intentIncludes desc.intent n
              | _ => intentIncludes desc.intent (nm "")
            | _ => intentIncludes desc.intent (nm "View")
          if !ok then (true, s) else
          match resolveOpt src s (Dict.get? d (nm "Usage")) with
          | (.dict ud, s) =>
            let (vd, s) := match Dict.get? ud (nm "View") with
              | some x => Run.dictOf src s x
              | none => ([], s)
            let (es, s) := nameOf src s (Dict.get? vd (nm "ViewState"))
            if es = some (nm "OFF") then (true, s) else if es = some (nm "ON") then (false, s)
            else (dflt, s)
          | (_, s) => (dflt, s)
        else if ty = some (nm "OCMD") then
          match resolveOpt src s (Dict.get? d (nm "VE")) with
          | (.array _, s) => (false, s)
          | (_, s) =>
            let (p, s) := nameOf src s (Dict.get? d (nm "P"))
            let cb := combineOf p
            let flip := fun (h : Bool) => if cb % 2 == 0 then !h else h
            let raw := (Dict.get? d (nm "OCGs")).getD .null
            match Run.resolve src s raw with
            | (.array xs, s) =>
              let (on, s) := xs.foldl (fun (acc : Bool × σ) x =>
                let (h, s) := ocHidden src desc f x acc.2
                let h := flip h
                (if cb / 2 % 2 == 1 then acc.1 && h else acc.1 || h, s)) (cb % 2 == 1, s)
              (!on, s)
            | (_, s) =>
              let (h, s) := ocHidden src desc f raw s
              (!(flip h), s)
        else (false, s)
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

/-! ### Synthesised appearances (task 8.3b; MuPDF `pdf-appearance.c`)

An annotation without a normal appearance of subtype Square, Circle, Line, Ink, Highlight,
Underline or StrikeOut gets one written the way MuPDF 1.25.1 writes it for display
(`pdf_update_appearance` → `pdf_write_appearance`, local synthesis): a content stream in page
coordinates, `/BBox` = the recomputed rectangle, `/Matrix` identity (so A is the identity), and
`/Resources << /ExtGState << /H … >> >>` for `/CA` < 1 and Highlight's Multiply blend. The
annotation's `/Rect` is replaced by the recomputed one (as MuPDF writes it back).

Read like MuPDF: `/C` and `/IC` (`pdf_annot_color_imp`: 0 → none, 1–2 → gray, 3 → RGB,
≥ 4 → CMYK), `/CA` (default 1), border width `/BS /W`, else `/Border [h v w]`, else 1; dash
`/BS /D`, else `/Border`'s fourth element; `/RD`; `/L`, `/LL`, `/LLE`, `/LLO`; `/InkList`;
`/QuadPoints` (ul, ur, ll, lr). Numbers are written with six decimals (MuPDF's `%g`: six
significant digits). Recorded gaps: Line `/LE` endings and `/Cap` captions, cloudy borders
(`/BE`), FreeText, Text icons, Squiggly, Polygon/PolyLine, Caret, Stamp, Redact and widgets are
not synthesised (`Skip.noAppearance`). At most `maxSynthNums` numbers are read per array. -/

/-- Most numbers read from one `/InkList` stroke or `/QuadPoints` array, and most strokes
(local cap). -/
def maxSynthNums : Nat := 65536

/-- A rational written with six decimals (rounded half up). -/
def fmt (q : Rat) : String :=
  let r := (fixOfRat q).raw
  let a := r.natAbs
  let fs := toString (a % 1000000)
  (if r < 0 then "-" else "") ++ toString (a / 1000000) ++ "." ++
    String.ofList (List.replicate (6 - fs.length) '0') ++ fs

/-- Square root to six decimals (0 for a non-positive argument). -/
def rsqrt (q : Rat) : Rat :=
  if q ≤ 0 then 0 else ((Nat.sqrt (q * 1000000000000).floor.toNat : Nat) : Rat) / 1000000

/-- A rectangle that may be empty (`fz_empty_rect`). -/
abbrev OBox := Option RBox

/-- Include a point (`fz_include_point_in_rect`; the empty box becomes the point). -/
def OBox.incl (r : OBox) (x y : Rat) : OBox :=
  match r with
  | none => some ⟨x, y, x, y⟩
  | some b => some ⟨min b.x0 x, min b.y0 y, max b.x1 x, max b.y1 y⟩

/-- Grow by `d` on every side (`fz_expand_rect`; the empty box stays empty). -/
def OBox.expand (r : OBox) (d : Rat) : OBox :=
  r.map fun b => ⟨b.x0 - d, b.y0 - d, b.x1 + d, b.y1 + d⟩

/-- Union (`fz_union_rect`). -/
def OBox.union (a b : OBox) : OBox :=
  match a, b with
  | none, r => r
  | r, none => r
  | some p, some q => some ⟨min p.x0 q.x0, min p.y0 q.y0, max p.x1 q.x1, max p.y1 q.y1⟩

/-- A number (resolved one level; `pdf_to_real`: anything else is 0). -/
def realOf {σ : Type} (src : Source σ) (s : σ) (o : PdfObject) : Rat × σ :=
  match Run.resolve src s o with
  | (v, s) => ((Run.numOf v).map ratOf |>.getD 0, s)

/-- An optional number (`none` when absent or not a number). -/
def realOpt {σ : Type} (src : Source σ) (s : σ) : Option PdfObject → Option Rat × σ
  | none => (none, s)
  | some o => match Run.resolve src s o with
    | (v, s) => ((Run.numOf v).map ratOf, s)

/-- The elements of an array (resolved one level), at most `maxSynthNums`; not an array: none. -/
def arrOf {σ : Type} (src : Source σ) (s : σ) : Option PdfObject → Option (List PdfObject) × σ
  | none => (none, s)
  | some o => match Run.resolve src s o with
    | (.array xs, s) => (some (xs.take maxSynthNums), s)
    | (_, s) => (none, s)

/-- The numbers of a list of objects (`pdf_array_get_real`). -/
def realsOf {σ : Type} (src : Source σ) (s : σ) (xs : List PdfObject) : List Rat × σ :=
  let (acc, s) := xs.foldl (fun (acc : List Rat × σ) o =>
    let (v, s) := realOf src acc.2 o; (v :: acc.1, s)) ([], s)
  (acc.reverse, s)

/-- Element `i` of a list of numbers (0 when missing, as `pdf_array_get_real`). -/
def nth (xs : List Rat) (i : Nat) : Rat := xs[i]?.getD 0

/-- An annotation colour (`pdf_annot_color_imp`): 0 → none, 1–2 → gray, 3 → RGB, else CMYK. -/
def colorOf {σ : Type} (src : Source σ) (s : σ) (o : Option PdfObject) : List Rat × σ :=
  let (xs, s) := arrOf src s o
  let xs := xs.getD []
  let k := if xs.length = 0 then 0 else if xs.length ≤ 2 then 1 else if xs.length = 3 then 3
    else 4
  realsOf src s (xs.take k)

/-- What the appearance writers read from an annotation dictionary. -/
structure Style where
  /-- `/CA` (default 1). -/
  ca : Rat
  /-- `/C`. -/
  c : List Rat
  /-- `/IC`. -/
  ic : List Rat
  /-- Border width. -/
  lw : Rat
  /-- Dash array. -/
  dash : List Rat

/-- Read the style of annotation dictionary `ad` (see the section doc). -/
def styleOf {σ : Type} (src : Source σ) (s : σ) (ad : Dict) : Style × σ :=
  let (ca, s) := realOpt src s (Dict.get? ad (nm "CA"))
  let (c, s) := colorOf src s (Dict.get? ad (nm "C"))
  let (ic, s) := colorOf src s (Dict.get? ad (nm "IC"))
  let (bs, s) := match Dict.get? ad (nm "BS") with
    | some o => Run.dictOf src s o
    | none => ([], s)
  let (bw, s) := realOpt src s (Dict.get? bs (nm "W"))
  let (border, s) := arrOf src s (Dict.get? ad (nm "Border"))
  let (w2, s) := match border.bind (·[2]?) with
    | some o => realOpt src s (some o)
    | none => (none, s)
  let lw := match bw, w2 with
    | some w, _ => w
    | none, some w => w
    | none, none => 1
  let (d, s) := arrOf src s (Dict.get? bs (nm "D"))
  let (d, s) := match d, border with
    | some d, _ => (some d, s)
    | none, some b => arrOf src s (b[3]?)
    | none, none => (none, s)
  let (dash, s) := realsOf src s (d.getD [])
  (⟨ca.getD 1, c, ic, lw, dash⟩, s)

/-- `/H gs` and its resources (`pdf_write_opacity_blend_mode`): nothing for a normal blend at
full opacity. -/
def opacityRes (multiply : Bool) (ca : Rat) : String × Dict :=
  if !multiply && ca == 1 then ("", []) else
  let h : Dict := [(nm "Type", .name (nm "ExtGState"))] ++
    (if multiply then [(nm "BM", .name (nm "Multiply"))] else []) ++
    (if ca < 1 then [(nm "CA", Run.fixedObj (fixOfRat ca)), (nm "ca", Run.fixedObj (fixOfRat ca))]
     else [])
  ("/H gs\n", [(nm "ExtGState", .dict [(nm "H", .dict h)])])

/-- The dash operator (`pdf_write_dash_pattern`). -/
def dashStr (d : List Rat) : String :=
  if d.isEmpty then "" else "[" ++ " ".intercalate (d.map fmt) ++ "]0 d\n"

/-- A colour operator (`write_color`); `none` for no colour. -/
def colorStr (c : List Rat) (stroke : Bool) : Option String :=
  let j := fun (xs : List Rat) => " ".intercalate (xs.map fmt)
  match c.length with
  | 4 => some (j c ++ (if stroke then " K\n" else " k\n"))
  | 3 => some (j c ++ (if stroke then " RG\n" else " rg\n"))
  | 1 => some (j c ++ (if stroke then " G\n" else " g\n"))
  | _ => none

/-- `maybe_stroke_and_fill`. -/
def paintStr (sc ic : Bool) : String :=
  if sc then (if ic then "b\n" else "S\n") else (if ic then "f\n" else "n\n")

/-- The common prelude: dash, width, stroke colour, optionally interior colour; with whether a
stroke and an interior colour were set. -/
def prelude (st : Style) (interior : Bool) : String × Bool × Bool :=
  let sc := colorStr st.c true
  let ic := if interior then colorStr st.ic false else none
  (dashStr st.dash ++ fmt st.lw ++ " w\n" ++ sc.getD "" ++ ic.getD "", sc.isSome, ic.isSome)

/-- Bézier magic for a quarter ellipse (`CIRCLE_MAGIC`). -/
def circleMagic : Rat := 551915 / 1000000

/-- `draw_circle`. -/
def circleStr (rx ry cx cy : Rat) : String :=
  let mx := rx * circleMagic
  let my := ry * circleMagic
  let p := fun (xs : List Rat) => " ".intercalate (xs.map fmt)
  p [cx, cy + ry] ++ " m\n" ++
  p [cx + mx, cy + ry, cx + rx, cy + my, cx + rx, cy] ++ " c\n" ++
  p [cx + rx, cy - my, cx + mx, cy - ry, cx, cy - ry] ++ " c\n" ++
  p [cx - mx, cy - ry, cx - rx, cy - my, cx - rx, cy] ++ " c\n" ++
  p [cx - rx, cy + my, cx - mx, cy + ry, cx, cy + ry] ++ " c\n"

/-- Square and Circle (`pdf_write_square_appearance`, `pdf_write_circle_appearance`, without
clouds): the border centred on `/Rect` inset by `/RD`, at least half the line width. -/
def boxAp (circle : Bool) (st : Style) (orect : RBox) (rd : List Rat) : String × OBox :=
  let (pre, sc, ic) := prelude st true
  let e := st.lw / 2
  let r0 := max (nth rd 0) e
  let r1 := max (nth rd 1) e
  let r2 := max (nth rd 2) e
  let r3 := max (nth rd 3) e
  let x := orect.x0 + r0
  let y := orect.y0 + r1
  let w := max (orect.x1 - orect.x0 - r0 - r2) 1
  let h := max (orect.y1 - orect.y0 - r1 - r3) 1
  let path := if circle then circleStr (w / 2) (h / 2) (x + w / 2) (y + h / 2)
    else fmt x ++ " " ++ fmt y ++ " " ++ fmt w ++ " " ++ fmt h ++ " re\n"
  -- MuPDF's circle writer uses `rd.x1` for the bottom (kept for pixel equality)
  let y0 := if circle then y - r2 else y - r1
  (pre ++ path ++ paintStr sc ic, some ⟨x - r0, y0, x + w + r2, y + h + r3⟩)

/-- `x y m\nx' y' l\n`. -/
def segStr (ax ay bx by_ : Rat) : String :=
  fmt ax ++ " " ++ fmt ay ++ " m\n" ++ fmt bx ++ " " ++ fmt by_ ++ " l\n"

/-- Line (`pdf_write_line_appearance` without `/LE` endings and `/Cap` captions): leader lines
`/LL`, `/LLE`, `/LLO`; the box grown by `max 1 w`. -/
def lineAp (st : Style) (l : List Rat) (ll lle llo : Rat) : String × OBox :=
  let (pre, sc, _) := prelude st true
  let (ax, ay, bx, by_) := (nth l 0, nth l 1, nth l 2, nth l 3)
  let len := rsqrt ((bx - ax) * (bx - ax) + (by_ - ay) * (by_ - ay))
  let dx := (bx - ax) / len
  let dy := (by_ - ay) / len
  let r0 : OBox := some ⟨min ax bx, min ay by_, max ax bx, max ay by_⟩
  let (lle, llo) := if ll < 0 then (-lle, -llo) else (lle, llo)
  let (lead, a, b, r) :=
    if ll = 0 then ("", (ax, ay), (bx, by_), r0) else
    let aa := (ax - dy * llo, ay + dx * llo)
    let ba := (bx - dy * llo, by_ + dx * llo)
    let ab := (ax - dy * (llo + ll + lle), ay + dx * (llo + ll + lle))
    let bb := (bx - dy * (llo + ll + lle), by_ + dx * (llo + ll + lle))
    let a := (ax - dy * (llo + ll), ay + dx * (llo + ll))
    let b := (bx - dy * (llo + ll), by_ + dx * (llo + ll))
    (segStr aa.1 aa.2 ab.1 ab.2 ++ segStr ba.1 ba.2 bb.1 bb.2, a, b,
      ((((r0.incl a.1 a.2).incl b.1 b.2).incl ab.1 ab.2).incl bb.1 bb.2))
  (pre ++ lead ++ segStr a.1 a.2 b.1 b.2 ++ (if sc then "S\n" else "n\n"), r.expand (max 1 st.lw))

/-- One ink stroke: its path and the box. -/
def inkStroke (r : OBox) (pts : List Rat) : String × OBox :=
  let m := pts.length / 2
  let ps := (List.range m).map fun k => (nth pts (2 * k), nth pts (2 * k + 1))
  let (str, r, _) := ps.foldl (fun (acc : String × OBox × Bool) p =>
    (acc.1 ++ fmt p.1 ++ " " ++ fmt p.2 ++ (if acc.2.2 then " m\n" else " l\n"),
      acc.2.1.incl p.1 p.2, false)) ("", r, true)
  let extra := match ps with
    | [p] => fmt p.1 ++ " " ++ fmt p.2 ++ " l\n"
    | _ => ""
  (str ++ extra, r)

/-- Ink (`pdf_write_ink_appearance`): round caps and joins; the box grown by `lw + 6`. -/
def inkAp (st : Style) (strokes : List (List Rat)) : String × OBox :=
  let (pre, sc, _) := prelude st false
  let (body, r) := strokes.foldl (fun (acc : String × OBox) pts =>
    let (t, r) := inkStroke acc.2 pts; (acc.1 ++ t, r)) ("", none)
  (pre ++ "1 J\n1 j\n" ++ body ++ (if sc then "S\n" else "n\n"), r.expand (st.lw + 6))

/-- A quadrilateral: ul, ur, ll, lr. -/
abbrev Quad := (Rat × Rat) × (Rat × Rat) × (Rat × Rat) × (Rat × Rat)

/-- The quads of a `/QuadPoints` list (groups of 8; a short last group reads 0s). -/
def quadsOf (qp : List Rat) : List Quad :=
  (List.range ((qp.length + 7) / 8)).map fun k =>
    let i := 8 * k
    ((nth qp i, nth qp (i + 1)), (nth qp (i + 2), nth qp (i + 3)),
     (nth qp (i + 4), nth qp (i + 5)), (nth qp (i + 6), nth qp (i + 7)))

/-- `union_quad`: the quad's box grown by `lw`, joined to `r`. -/
def unionQuad (r : OBox) (q : Quad) (lw : Rat) : OBox :=
  let (ul, ur, ll, lr) := q
  OBox.union r (some ⟨min (min ul.1 ur.1) (min ll.1 lr.1) - lw,
    min (min ul.2 ur.2) (min ll.2 lr.2) - lw,
    max (max ul.1 ur.1) (max ll.1 lr.1) + lw, max (max ul.2 ur.2) (max ll.2 lr.2) + lw⟩)

/-- Height of a quad (`|ul − ll|`). -/
def quadH (q : Quad) : Rat :=
  let (ul, _, ll, _) := q
  rsqrt ((ul.1 - ll.1) * (ul.1 - ll.1) + (ul.2 - ll.2) * (ul.2 - ll.2))

/-- One highlight quad (`pdf_write_highlight_appearance`): rounded ends bulging by
`h / 4.2425`. -/
def highlightQuad (r : OBox) (q : Quad) : String × OBox :=
  let (ul, ur, ll, lr) := q
  let h := quadH q
  let m := h / (42425 / 10000)
  let dx := lr.1 - ll.1
  let dy := lr.2 - ll.2
  let vn := rsqrt (dx * dx + dy * dy)
  let v := (dx * m / vn, dy * m / vn)
  let mll := (ll.1 - v.1 - v.2, ll.2 - v.2 + v.1)
  let mul := (ul.1 - v.1 + v.2, ul.2 - v.2 - v.1)
  let mlr := (lr.1 + v.1 - v.2, lr.2 + v.2 + v.1)
  let mur := (ur.1 + v.1 + v.2, ur.2 + v.2 - v.1)
  let p := fun (xs : List Rat) => " ".intercalate (xs.map fmt)
  (p [ll.1, ll.2] ++ " m\n" ++ p [mll.1, mll.2, mul.1, mul.2, ul.1, ul.2] ++ " c\n" ++
    p [ur.1, ur.2] ++ " l\n" ++ p [mur.1, mur.2, mlr.1, mlr.2, lr.1, lr.2] ++ " c\nf\n",
   unionQuad (unionQuad r q (h / 16)) (mul, mur, mll, mlr) 0)

/-- Highlight: Multiply blend, fill colour `/C`. -/
def highlightAp (st : Style) (qs : List Quad) : String × Dict × OBox :=
  let (gs, res) := opacityRes true st.ca
  let (body, r) := qs.foldl (fun (acc : String × OBox) q =>
    let (t, r) := highlightQuad acc.2 q; (acc.1 ++ t, r)) ("", none)
  (gs ++ (colorStr st.c false).getD "" ++ body, res, r)

/-- Underline (`t = 1/7`) and StrikeOut (`t = 3/7`): a line at `t` of the quad's height,
`h / 16` wide, stroke colour `/C`. -/
def barAp (t : Rat) (st : Style) (qs : List Quad) : String × OBox :=
  let (body, r) := qs.foldl (fun (acc : String × OBox) q =>
    let (ul, ur, ll, lr) := q
    let h := quadH q
    let a := (ll.1 + t * (ul.1 - ll.1), ll.2 + t * (ul.2 - ll.2))
    let b := (lr.1 + t * (ur.1 - lr.1), lr.2 + t * (ur.2 - lr.2))
    (acc.1 ++ fmt (h / 16) ++ " w\n" ++ segStr a.1 a.2 b.1 b.2 ++ "S\n",
      unionQuad acc.2 q (h / 16))) ("", none)
  ((colorStr st.c true).getD "" ++ body, r)

/-- A stream dictionary for a synthesised appearance with `/BBox` `r` and resources `res`. -/
def synthDict (r : RBox) (res : Dict) : Dict :=
  [(nm "Type", .name (nm "XObject")), (nm "Subtype", .name (nm "Form")),
   (nm "BBox", .array ([r.x0, r.y0, r.x1, r.y1].map fun q => Run.fixedObj (fixOfRat q)))] ++
  (if res.isEmpty then [] else [(nm "Resources", .dict res)])

/-- **Synthesise a normal appearance** for annotation dictionary `ad` of subtype `sub` with
`/Rect` `orect` (see the section doc): the new rectangle (= `/BBox`) and the content stream;
`none` for a subtype not synthesised, or an empty result rectangle. -/
def synthesize {σ : Type} (src : Source σ) (s : σ) (ad : Dict) (sub : Name) (orect : RBox) :
    Option (RBox × Stream) × σ :=
  let (st, s) := styleOf src s ad
  let (gs, res) := opacityRes false st.ca
  let quads := fun (s : σ) =>
    let (qp, s) := arrOf src s (Dict.get? ad (nm "QuadPoints"))
    let (qp, s) := realsOf src s (qp.getD [])
    (quadsOf qp, s)
  let out : Option (String × Dict × OBox) × σ :=
    if sub = nm "Square" ∨ sub = nm "Circle" then
      let (rd, s) := arrOf src s (Dict.get? ad (nm "RD"))
      let (rd, s) := realsOf src s ((rd.getD []).take 4)
      let (c, r) := boxAp (sub = nm "Circle") st orect rd
      (some (gs ++ c, res, r), s)
    else if sub = nm "Line" then
      let (l, s) := arrOf src s (Dict.get? ad (nm "L"))
      let (l, s) := realsOf src s ((l.getD []).take 4)
      let (ll, s) := realOpt src s (Dict.get? ad (nm "LL"))
      let (lle, s) := realOpt src s (Dict.get? ad (nm "LLE"))
      let (llo, s) := realOpt src s (Dict.get? ad (nm "LLO"))
      let (c, r) := lineAp st l (ll.getD 0) (lle.getD 0) (llo.getD 0)
      (some (gs ++ c, res, r), s)
    else if sub = nm "Ink" then
      let (il, s) := arrOf src s (Dict.get? ad (nm "InkList"))
      let (strokes, s) := (il.getD []).foldl (fun (acc : List (List Rat) × σ) o =>
        let (xs, s) := arrOf src acc.2 (some o)
        let (xs, s) := realsOf src s (xs.getD [])
        (xs :: acc.1, s)) ([], s)
      let (c, r) := inkAp st strokes.reverse
      (some (gs ++ c, res, r), s)
    else if sub = nm "Highlight" then
      let (qs, s) := quads s
      (some (highlightAp st qs), s)
    else if sub = nm "Underline" then
      let (qs, s) := quads s
      let (c, r) := barAp (1 / 7) st qs
      (some (gs ++ c, res, r), s)
    else if sub = nm "StrikeOut" then
      let (qs, s) := quads s
      let (c, r) := barAp (3 / 7) st qs
      (some (gs ++ c, res, if qs.isEmpty then some orect else r), s)
    else (none, s)
  match out with
  | (some (c, res, some r), s) => (some (r, ⟨synthDict r res, c.toUTF8⟩), s)
  | (_, s) => (none, s)

/-- Parse one annotation dictionary `ad` (object `num`, position `idx`). -/
def parseDict {σ : Type} (src : Source σ) (s : σ) (oc : OCDesc) (idx num : Nat) (ad : Dict) :
    Outcome × σ :=
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
    let (och, s) := ocHidden src oc maxOCDepth ((Dict.get? ad (nm "OC")).getD .null) s
    if och then (.skip .ocHidden, s)
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
          | (none, s) =>
            if widget then (.skip .noAppearance, s) else
            match synthesize src s ad subtype rect with
            | (none, s) => (.skip .noAppearance, s)
            | (some (r, st), s) =>
              (.draw ⟨idx, num, subtype, r, flags, state, 0, 0, st, Matrix.identity, widget,
                true⟩, s)
          | (some (n, g, st), s) =>
            let m := annotMatrix rect (Run.bboxOf st.dict) (Run.formMatrix st.dict)
            (.draw ⟨idx, num, subtype, rect, flags, state, n, g, st, m, widget, false⟩, s)

/-- Parse one `/Annots` element (`seen`: annotation object numbers already listed). -/
def parseOne {σ : Type} (src : Source σ) (s : σ) (oc : OCDesc) (idx : Nat) (seen : List Nat)
    (o : PdfObject) : Outcome × σ :=
  match o with
  | .ref n g =>
    if seen.contains n then (.skip .duplicate, s)
    else
      match src.fetch s n g with
      | (.ok (.obj (.dict ad)), s) => parseDict src s oc idx n ad
      | (_, s) => (.skip .notDict, s)
  | .dict ad => parseDict src s oc idx 0 ad
  | _ => (.skip .notDict, s)

/-- Object number of a reference (0 otherwise). -/
def refNum : PdfObject → Nat
  | .ref n _ => n
  | _ => 0

/-- Parse the elements in order: one outcome per element. -/
def parseAll {σ : Type} (src : Source σ) (oc : OCDesc) :
    Nat → List Nat → List PdfObject → σ → List (Nat × Outcome) × σ
  | _, _, [], s => ([], s)
  | idx, seen, o :: os, s =>
    let (r, s) := parseOne src s oc idx seen o
    let (rs, s) := parseAll src oc (idx + 1) (refNum o :: seen) os s
    ((idx, r) :: rs, s)

/-- `parseAll` gives exactly one outcome per element. -/
theorem parseAll_length {σ : Type} (src : Source σ) (oc : OCDesc) :
    ∀ (idx : Nat) (seen : List Nat) (os : List PdfObject) (s : σ),
      (parseAll src oc idx seen os s).1.length = os.length
  | _, _, [], _ => rfl
  | idx, seen, o :: os, s => by
    simp only [parseAll, List.length_cons]
    rw [parseAll_length src oc (idx + 1) (refNum o :: seen) os]

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
def collect {σ : Type} (src : Source σ) (s : σ) (pd : Dict) (oc : OCDesc := {}) :
    Collected × σ :=
  let (arr, s) := match Dict.get? pd (nm "Annots") with
    | some o => Run.resolve src s o
    | none => (.null, s)
  let xs := match arr with
    | .array xs => xs
    | _ => []
  let (rs, s) := parseAll src oc 0 [] (xs.take maxAnnots) s
  let over := (List.range (xs.length - maxAnnots)).map fun i => (maxAnnots + i, Skip.overCap)
  ({ drawn := widgetsLast (rs.filterMap (·.2.drawable?)),
     skipped := rs.filterMap (fun (i, r) => r.skip?.map (i, ·)) ++ over }, s)

/-- **Annotation count bound**: at most `maxAnnots` annotations are drawn per page. -/
theorem collect_drawn_le {σ : Type} (src : Source σ) (s : σ) (pd : Dict) (oc : OCDesc) :
    (collect src s pd oc).1.drawn.length ≤ maxAnnots := by
  simp only [collect]
  generalize (match Dict.get? pd (nm "Annots") with
    | some o => Run.resolve src s o
    | none => (PdfObject.null, s)) = a
  obtain ⟨arr, s1⟩ := a
  generalize (match arr with
    | .array xs => xs
    | _ => []) = xs
  have hl := parseAll_length src oc 0 [] (xs.take maxAnnots) s1
  generalize parseAll src oc 0 [] (xs.take maxAnnots) s1 = p at hl
  obtain ⟨rs, s2⟩ := p
  simp only at hl ⊢
  rw [widgetsLast_length]
  have h1 := List.length_filterMap_le (fun (x : Nat × Outcome) => x.2.drawable?) rs
  have h2 := List.length_take_le maxAnnots xs
  omega

/-! ## 4. Running the appearances -/

open Run (Good)

/-- The decoded content of an appearance: a synthesised one's own bytes, else the stream
decoded through the source. -/
def apBytes {σ : Type} (src : Source σ) (s : σ) (d : Drawable) : (Except Error ByteArray) × σ :=
  if d.synth then (.ok d.ap.data, s) else src.decode s d.apNum d.ap

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
      match apBytes env.src s d with
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
    (pageFonts : Text.FontTable) (bud : Budget) (oc : OCDesc := {}) : AnnotPage × σ :=
  let (c, s) := collect src s pd oc
  let (roots, s) := apRoots src s c.drawn
  let (fonts, s) := loadAnnotFonts limits src s pageFonts roots
  let st := runAppearances (Text.textEnv limits src fonts) bud pageRes c.drawn s ()
  (⟨st.items, fonts, roots, c, st.warnings, st.ops, st.forms, st.truncated⟩, st.s)

/-- **Bounds of `pageAnnots`**: at most `maxAnnots` annotations drawn, at most `bud.ops`
operators and `Paint.maxItems · bud.ops` items. -/
theorem pageAnnots_bounds {σ : Type} (limits : Limits) (src : Source σ) (s : σ) (pd pageRes : Dict)
    (pageFonts : Text.FontTable) (bud : Budget) (oc : OCDesc) :
    (pageAnnots limits src s pd pageRes pageFonts bud oc).1.collected.drawn.length ≤ maxAnnots ∧
    (pageAnnots limits src s pd pageRes pageFonts bud oc).1.ops ≤ bud.ops ∧
    (pageAnnots limits src s pd pageRes pageFonts bud oc).1.items.size ≤
      Paint.maxItems * bud.ops :=
  ⟨collect_drawn_le src s pd oc, runAppearances_ops_le _ _ _ _ _ _,
   runAppearances_items_le _ _ _ _ _ _⟩

/-- **Annotations of a page of an opened document**, charging the decode `budget`; `pageFonts`
is the page's font table (`Text.PageText.fonts`), `bud` what is left of the page's operator
and form budgets. -/
def docAnnots (limits : Limits) (doc : Doc.Doc) (page : Doc.Page) (pageFonts : Text.FontTable)
    (bud : Budget) (budget : Filter.Budget) : AnnotPage × Filter.Budget :=
  let src := Text.docSource limits doc
  let (pd, b) := Run.dictOf src budget (.ref page.num page.gen)
  let (oc, b) := readOC src b doc.catalog
  pageAnnots limits src b pd (page.resources.getD []) pageFonts bud oc

/-- **The shared budget** (task 8.3b): what the page run `pt` left of `Limits.maxOpsPerPage`
and `Limits.maxFormsPerPage`. -/
def Budget.after (limits : Limits) (pt : Text.PageText) : Budget :=
  ⟨limits.maxOpsPerPage - pt.ops, limits.maxFormsPerPage - pt.forms⟩

/-- **One operator budget per page**: page content and annotation appearances together execute
at most `Limits.maxOpsPerPage` operators (given the page run kept to it). -/
theorem docAnnots_shared_ops (limits : Limits) (doc : Doc.Doc) (page : Doc.Page)
    (pt : Text.PageText) (b : Filter.Budget) (h : pt.ops ≤ limits.maxOpsPerPage) :
    pt.ops + (docAnnots limits doc page pt.fonts (Budget.after limits pt) b).1.ops ≤
      limits.maxOpsPerPage := by
  dsimp only [docAnnots]
  generalize Run.dictOf (Text.docSource limits doc) b (.ref page.num page.gen) = r
  obtain ⟨pd, b'⟩ := r
  generalize readOC (Text.docSource limits doc) b' doc.catalog = q
  obtain ⟨oc, b''⟩ := q
  have := (pageAnnots_bounds limits (Text.docSource limits doc) b'' pd
    (page.resources.getD []) pt.fonts (Budget.after limits pt) oc).2.1
  simp only [Budget.after] at this ⊢
  omega

/-- The page text `pt` with the annotations `ap` appended (MuPDF's `-F txt` includes the text
of annotation appearances): annotation glyphs after the page's, their item indices continuing
after the page's items, the font table and counts combined, lines laid out again. -/
def withAnnots (o : Text.Options) (pt : Text.PageText) (ap : AnnotPage) : Text.PageText :=
  let gs := pt.glyphs ++ Text.extractAux ap.fonts pt.items.size ap.items.toList
  let (lines, text) := Text.layout o gs
  { fonts := ap.fonts, items := pt.items ++ ap.items, glyphs := gs, lines, text,
    warnings := pt.warnings + ap.warnings, ops := pt.ops + ap.ops, forms := pt.forms + ap.forms }

/-- **Annotation glyphs (same pass)**: the glyphs of `withAnnots` are the page's glyphs followed
by the extraction of exactly the annotation items that are painted. -/
theorem withAnnots_glyphs (o : Text.Options) (pt : Text.PageText) (ap : AnnotPage) :
    (withAnnots o pt ap).glyphs =
      pt.glyphs ++ Text.extractAux ap.fonts pt.items.size ap.items.toList := rfl

/-- **Text of a page with its annotations** (the text view's entry point, task 8.3b): the page
run (`Text.extractDocPage`), then the annotations under the shared budget, combined by
`withAnnots`. -/
def extractDocPageAnnots (limits : Limits) (doc : Doc.Doc) (page : Doc.Page)
    (budget : Filter.Budget) (o : Text.Options := {}) :
    (Except Error Text.PageText) × Filter.Budget :=
  match Text.extractDocPage limits doc page budget o with
  | (.error e, b) => (.error e, b)
  | (.ok pt, b) =>
    let (ap, b) := docAnnots limits doc page pt.fonts (Budget.after limits pt) b
    (.ok (withAnnots o pt ap), b)

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
-- synthesis helpers: six-decimal numbers, square roots, MuPDF's colour lengths
#guard fmt (-3 / 2) == "-1.500000" && fmt (1 / 3) == "0.333333" && fmt 0 == "0.000000"
#guard rsqrt 225 == 15 && rsqrt (-1) == 0
#guard colorStr [1, 0, 0] true == some "1.000000 0.000000 0.000000 RG\n" && colorStr [] false == none
#guard (quadsOf [1, 2, 3, 4, 5, 6, 7, 8, 9]).length == 2
#guard (boxAp false { ca := 1, c := [1, 0, 0], ic := [], lw := 3, dash := [] }
  (RBox.mk 20 20 80 60) []).2 == some (RBox.mk 20 20 80 60)

end SafePdf.Core.Annot
