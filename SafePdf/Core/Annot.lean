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
  (usage "View"). NoRotate (bit 5, task 8.3d): on a page with `/Rotate`, A is followed by
  `noRotateMatrix` (as `pdf_run_annot_with_usage`; we use the page's effective rotation, MuPDF
  the raw `/Rotate`: they differ only for a value that is not a multiple of 90). NoZoom, Print,
  ReadOnly, Locked … are ignored for display (MuPDF: "TODO: NoZoom"). `/OC` (optional
  content): hidden in the default configuration → `Skip.ocHidden` (task 8.3c, `ocHidden`).
* `/Subtype /Widget` is drawn only if both `/FT` and `/T` are found on it or on its `/Parent`
  chain (at most `maxFieldDepth` levels), as MuPDF does.
* `/Rect` must be an array of four numbers (normalised); otherwise `Skip.badRect`.
* **Appearance** (`selectAP`, = `pdf_annot_ap` without interaction state): `/AP /N`; if it is a
  reference to a stream that stream is used, else it is resolved to a dictionary of
  appearance states and the entry named by `/AS` (which must be a reference to a stream) is
  used. No `/AS`, or no stream: a non-widget Square, Circle, Line, Ink, Highlight, Underline,
  StrikeOut (task 8.3b), Polygon, PolyLine, Squiggly, Caret, Text, FileAttachment or Sound
  (task 8.3c), FreeText or Stamp (task 8.3d) gets a **synthesised** appearance (`synthesize`,
  as MuPDF's `pdf_update_appearance`); anything else is `Skip.noAppearance` (MuPDF also
  synthesises Redact and widgets: not done here).
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

Not done (recorded): `/F` NoZoom (MuPDF ignores it too).

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
/-- NoRotate (task 8.3d). -/
def flagNoRotate : Nat := 16
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

/-- `(cos θ, sin θ)` of the page rotation `θ` (exact). -/
def rotCS : Doc.Rotation → Rat × Rat
  | .r0 => (1, 0)
  | .r90 => (0, 1)
  | .r180 => (-1, 0)
  | .r270 => (0, -1)

/-- **NoRotate** (task 8.3d; MuPDF 1.25.1 `pdf_run_annot_with_usage`): in device space MuPDF
turns the annotation by `−/Rotate` about the device image of the rectangle's upper-left corner
`(x0, y1)`. As the page-to-device map is a rotation by `−/Rotate` after a y-flip, the same map in
page space is `fz_rotate(/Rotate)` about `(x0, y1)`: `T(−p) · R · T(p)` (row vectors), to be
applied after A. Exact (integer rotation entries). -/
def noRotateMatrix (rot : Doc.Rotation) (r : RBox) : Matrix :=
  let (c, s) := rotCS rot
  let px := r.x0
  let py := r.y1
  ⟨fixOfRat c, fixOfRat s, fixOfRat (-s), fixOfRat c,
   fixOfRat (px - px * c + py * s), fixOfRat (py - px * s - py * c)⟩

/-- `noRotateMatrix` fixes the corner `(x0, y1)` it turns about (exactly, over `ℚ`). -/
theorem noRotate_fixes_corner (rot : Doc.Rotation) (r : RBox) :
    r.x0 * (rotCS rot).1 + r.y1 * (-(rotCS rot).2) +
        (r.x0 - r.x0 * (rotCS rot).1 + r.y1 * (rotCS rot).2) = r.x0 ∧
      r.x0 * (rotCS rot).2 + r.y1 * (rotCS rot).1 +
        (r.y1 - r.x0 * (rotCS rot).2 - r.y1 * (rotCS rot).1) = r.y1 :=
  ⟨by grind, by grind⟩

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
  /-- No usable normal appearance (`/AP /N` stream, or state entry chosen by `/AS`) and no
  synthesised one; MuPDF also synthesises Redact and widgets (not done here). -/
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
  /-- Not optional content, but document-level data read with it (task 8.3e): the bytes of the
  catalog's `/AcroForm /DA` (empty when absent or not a string), the default appearance of a
  FreeText without an inheritable `/DA` (`pdf_annot_default_appearance`). -/
  acroDA : List UInt8 := []

/-- The object number and generation of a reference. -/
def refKey : PdfObject → Option (Nat × Nat)
  | .ref n g => some (n, g)
  | _ => none

/-- An object resolved one level, `null` when absent. -/
def resolveOpt {σ : Type} (src : Source σ) (s : σ) : Option PdfObject → PdfObject × σ
  | none => (.null, s)
  | some o => Run.resolve src s o

/-- The default configuration from the catalog `cat` (see the section doc), without `acroDA`. -/
def readOCConfig {σ : Type} (src : Source σ) (s : σ) (cat : Dict) : OCDesc × σ :=
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

/-- **Read the document-level data** of the catalog `cat`: the default optional-content
configuration (`readOCConfig`) and the `/AcroForm /DA` bytes (`pdf_dict_getl(trailer, Root,
AcroForm, DA)`, `pdf_to_str_buf`: anything but a string is empty). -/
def readOC {σ : Type} (src : Source σ) (s : σ) (cat : Dict) : OCDesc × σ :=
  let (oc, s) := readOCConfig src s cat
  let (da, s) := match resolveOpt src s (Dict.get? cat (nm "AcroForm")) with
    | (.dict af, s) => match resolveOpt src s (Dict.get? af (nm "DA")) with
      | (.string b, s) => (b, s)
      | (_, s) => ([], s)
    | (_, s) => ([], s)
  ({ oc with acroDA := da }, s)

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
significant digits). At most `maxSynthNums` numbers are read per array.

Task 8.3c adds line endings `/LE` (Line, PolyLine; `capStr`), Polygon/PolyLine (`/Vertices`,
`polyAp`), Squiggly (`squigglyAp`), Caret (`caretAp`) and the icons of Text, FileAttachment and
Sound annotations (`iconAp`, `/Name`, MuPDF's 8 × 8 open-iconic paths). Caret and icons are
written in a fixed form box (`[0 0 20 14]`, `[0 0 16 16]`) mapped into the recomputed
rectangle by matrix A; everything else has `/BBox` = rectangle and A = identity. Trigonometry
is exact: the arrow and slash directions come from the normalised line vector (`dirOf`, MuPDF's
`atan2f`/`cosf`/`sinf`), `cos 30°` to six decimals. Cloudy borders (`/BE /S /C`): task 8.3e,
below. Recorded gaps: Redact and widgets (`Skip.noAppearance`). FreeText, Stamp and Line `/Cap`
captions (`captionStr`): task 8.3d, below. -/

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

/-! ### Cloudy borders (task 8.3e; MuPDF 1.25.1 `start_cloud` … `end_cloud`)

A Square, Circle or Polygon whose `/BE` has `/S /C` and an intensity `/I` > 0
(`pdf_annot_border_effect`, `pdf_annot_border_effect_intensity`) gets MuPDF's cloudy border
instead of its plain path: points are placed along the outline every
`spacing = 6.666667 · I + 0.8333333 · lw` (the square restarts at each corner; the circle is
32 chords; the polygon continues across vertices), and each point is the centre of an arc of
radius `radius = 4 · I + 0.5 · lw` from where its circle meets the previous one to where it meets
the next (`emit_cloud`), split into Bézier segments of at most 45° (`draw_arc`), plus a short
22.5° tail; with an interior colour the arcs form one filled outline, else each arc starts a
new subpath. Bevel joins (`2 j`). The border box grows by `radius`. FreeText's `/BE` is not drawn
by MuPDF 1.25.1 (its writer has no cloud path): plain border, as here.

Trigonometry and square roots are computed over `ℚ` to about 10⁻¹¹ (`sinR`, `atanR`, `atan2R`,
`sqrtR`; MuPDF: single-precision `cosf`, `atan2`, `sqrtf`): coordinates agree with MuPDF's to
the written six decimals up to rounding. At most `maxCloudPts` points are placed per border
(MuPDF: unbounded — a zero spacing loops forever). -/

/-- Most cloud points per border (local cap). -/
def maxCloudPts : Nat := 4096

/-- Round down to 10⁻¹². -/
def rnd (q : Rat) : Rat := ((q * 1000000000000).floor : Rat) / 1000000000000

/-- π to 10⁻¹². -/
def piR : Rat := 3141592653590 / 1000000000000

/-- Square root to 10⁻¹² (0 for a non-positive argument). -/
def sqrtR (q : Rat) : Rat :=
  if q ≤ 0 then 0 else
    ((Nat.sqrt (q * 1000000000000000000000000).floor.toNat : Nat) : Rat) / 1000000000000

/-- The sine series from term `t = y^i / i!` (`x2 = y²`): `n` terms, each rounded. -/
def taylor (x2 : Rat) : Nat → Nat → Rat → Rat
  | 0, _, _ => 0
  | n + 1, i, t => t + taylor x2 n (i + 2) (rnd (-t * x2 / (((i + 1) * (i + 2) : Nat) : Rat)))

/-- Sine to about 10⁻¹¹ (argument reduced to `[−π, π]`). -/
def sinR (x : Rat) : Rat :=
  let k := ((x / (2 * piR)) + 1 / 2).floor
  let y := rnd (x - (k : Rat) * 2 * piR)
  taylor (rnd (y * y)) 14 1 y

/-- Cosine to about 10⁻¹¹. -/
def cosR (x : Rat) : Rat := sinR (x + piR / 2)

/-- Arctangent series `Σ (−1)^k y^(2k+1) / (2k+1)` for small `y`. -/
def atanSeries (y2 : Rat) : Nat → Nat → Rat → Rat
  | 0, _, _ => 0
  | n + 1, i, p => rnd (p / ((2 * i + 1 : Nat) : Rat)) + atanSeries y2 n (i + 1) (rnd (-p * y2))

/-- Arctangent of `x` with `|x| ≤ 1`: two half-angle steps, then 16 series terms. -/
def atanSmall (x : Rat) : Rat :=
  let h := fun (y : Rat) => rnd (y / (1 + sqrtR (1 + y * y)))
  let y := h (h x)
  4 * atanSeries (rnd (y * y)) 16 0 y

/-- Arctangent to about 10⁻¹¹. -/
def atanR (x : Rat) : Rat :=
  if x > 1 then piR / 2 - atanSmall (1 / x)
  else if x < -1 then -piR / 2 - atanSmall (1 / x)
  else atanSmall x

/-- `atan2(y, x)` (C's: `(−π, π]`, 0 at the origin). -/
def atan2R (y x : Rat) : Rat :=
  if x > 0 then atanR (y / x)
  else if x < 0 then (if y ≥ 0 then atanR (y / x) + piR else atanR (y / x) - piR)
  else if y > 0 then piR / 2 else if y < 0 then -piR / 2 else 0

/-- `draw_arc_seg`: one cubic Bézier for the arc from `th0` to `th1` (with a `m` if `move`). -/
def arcSeg (r xc yc th0 th1 : Rat) (move : Bool) : String :=
  let x1 := xc + r * cosR th0
  let y1 := yc + r * sinR th0
  let x4 := xc + r * cosR th1
  let y4 := yc + r * sinR th1
  let ax := x1 - xc
  let ay := y1 - yc
  let bx := x4 - xc
  let by_ := y4 - yc
  let q1 := ax * ax + ay * ay
  let q2 := q1 + ax * bx + ay * by_
  let k2 := rnd ((4 / 3) * (sqrtR (2 * q1 * q2) - q2) / (ax * by_ - ay * bx))
  let p := fun (xs : List Rat) => " ".intercalate (xs.map fmt)
  (if move then p [x1, y1] ++ " m\n" else "") ++
    p [xc + ax - k2 * ay, yc + ay + k2 * ax, xc + bx + k2 * by_, yc + by_ - k2 * bx, x4, y4] ++
    " c\n"

/-- `draw_arc`: the arc from `th0` down to `th1`, halved while longer than 45° (fuel: depth). -/
def arcStr (r xc yc : Rat) : Nat → Rat → Rat → Bool → String
  | 0, th0, th1, move => arcSeg r xc yc th0 th1 move
  | f + 1, th0, th1, move =>
    let d := th0 - th1
    if d > piR / 4 then
      arcStr r xc yc f th0 (rnd (th0 - d / 2)) move ++ arcStr r xc yc f (rnd (th0 - d / 2)) th1 false
    else arcSeg r xc yc th0 th1 move

/-- The cloud writer's state (`struct cloud_list`) and its output. -/
structure Cloud where
  /-- The first two and the latest three points (`data`, at most five). -/
  data : List (Rat × Rat) := []
  /-- No arc written yet. -/
  first : Bool := true
  /-- Interior colour set (one filled outline). -/
  fill : Bool
  /-- Distance between points. -/
  spacing : Rat
  /-- Arc radius. -/
  radius : Rat
  /-- Distance carried over from the previous line. -/
  phase : Rat := 0
  /-- Points placed. -/
  count : Nat := 0
  /-- Content written. -/
  out : String := ""

/-- `start_cloud` (constants measured from Acrobat by MuPDF). -/
def Cloud.start (lw intensity : Rat) (fill : Bool) : Cloud :=
  { fill, spacing := intensity * 6666667 / 1000000 + lw * 8333333 / 10000000,
    radius := intensity * 4 + lw / 2, out := "2 j\n" }

/-- `intersect_cloud`: the angle, seen from `p1` (`sel` = false) or `p0`, of the intersection of
the circles of radius `r` about `p0` and `p1` (0 when they do not meet or coincide). -/
def intersectCloud (p0 p1 : Rat × Rat) (r : Rat) (sel : Bool) : Rat :=
  let dx := p1.1 - p0.1
  let dy := p1.2 - p0.2
  let d := sqrtR (dx * dx + dy * dy)
  if d ≥ r + r ∨ d ≤ 0 then 0 else
  let a := d / 2
  let h := sqrtR (r * r - a * a)
  let x3 := rnd ((p0.1 + p1.1) / 2 - h * dy / d)
  let y3 := rnd ((p0.2 + p1.2) / 2 + h * dx / d)
  if sel then atan2R (y3 - p0.2) (x3 - p0.1) else atan2R (y3 - p1.2) (x3 - p1.1)

/-- `emit_cloud`: the arc about `b` between its neighbours `a` and `c`, and its tail. -/
def Cloud.emit (cl : Cloud) (a b c : Rat × Rat) : Cloud :=
  let th0 := intersectCloud a b cl.radius false
  let th1 := intersectCloud b c cl.radius true
  let th1 := if th1 > th0 then th1 - 2 * piR else th1
  let th1 := if th1 > th0 then th1 - 2 * piR else th1
  let r := cl.radius
  let tail := arcSeg r b.1 b.2 th1 (th1 - piR / 8) false ++
    (if cl.fill then arcSeg r b.1 b.2 (th1 - piR / 8) th1 false else "")
  { cl with out := cl.out ++ arcStr r b.1 b.2 4 th0 th1 (cl.first || !cl.fill) ++ tail,
            first := false }

/-- Point `i` of the window. -/
def Cloud.pt5 (cl : Cloud) (i : Nat) : Rat × Rat := cl.data[i]?.getD (0, 0)

/-- `add_cloud`: place a point; from the third on, emit the arc about the previous one. -/
def Cloud.add (cl : Cloud) (p : Rat × Rat) : Cloud :=
  let p := (rnd p.1, rnd p.2)
  let data := if cl.data.length < 5 then cl.data ++ [p]
    else [cl.pt5 0, cl.pt5 1, cl.pt5 3, cl.pt5 4, p]
  let cl := { cl with data, count := cl.count + 1 }
  let n := data.length
  if n ≥ 3 then cl.emit (cl.pt5 (n - 3)) (cl.pt5 (n - 2)) (cl.pt5 (n - 1)) else cl

/-- The placing loop of `add_cloud_line` (fuel: `maxCloudPts`; stops at the cap). -/
def Cloud.lineLoop (x0 y0 dx dy total : Rat) : Nat → Cloud → Rat → Cloud × Rat
  | 0, cl, used => (cl, used)
  | f + 1, cl, used =>
    if cl.count ≥ maxCloudPts then (cl, used)
    else if total - used > cl.spacing - cl.phase then
      let used := rnd (used + cl.spacing - cl.phase)
      let t := used / total
      let cl := cl.add (x0 + dx * t, y0 + dy * t)
      Cloud.lineLoop x0 y0 dx dy total f { cl with phase := 0 } used
    else (cl, used)

/-- `add_cloud_line`. -/
def Cloud.line (cl : Cloud) (a b : Rat × Rat) : Cloud :=
  let dx := b.1 - a.1
  let dy := b.2 - a.2
  let total := sqrtR (dx * dx + dy * dy)
  let cl := if cl.phase = 0 ∧ cl.count < maxCloudPts then cl.add a else cl
  let (cl, used) := Cloud.lineLoop a.1 a.2 dx dy total maxCloudPts cl 0
  { cl with phase := rnd (cl.phase + total - used) }

/-- `end_cloud`: join the last points with the first two. -/
def Cloud.finish (cl : Cloud) : String :=
  match cl.data with
  | [] => cl.out
  | [p] => cl.out ++ circleStr cl.radius cl.radius p.1 p.2
  | [p, q] => ((cl.emit p q p).emit q p q).out
  | [p, q, r] => ((cl.emit q r p).emit r p q).out
  | [p, q, s, r] => ((cl.emit s r p).emit r p q).out
  | p :: q :: _ :: r :: t :: _ => ((cl.emit r t p).emit t p q).out

/-- The cloudy outline of the rectangle `(x, y, w, h)` (the square: phase restarts at each
corner). -/
def cloudRect (cl : Cloud) (x y w h : Rat) : String :=
  let cl := cl.line (x, y) (x, y + h)
  let cl := { cl with phase := 0 }.line (x, y + h) (x + w, y + h)
  let cl := { cl with phase := 0 }.line (x + w, y + h) (x + w, y)
  let cl := { cl with phase := 0 }.line (x + w, y) (x, y)
  cl.finish

/-- The cloudy outline of the ellipse in `(x0, y0)–(x1, y1)`: 32 chords, clockwise from the
right (`add_cloud_circle`). -/
def cloudEllipse (cl : Cloud) (x0 y0 x1 y1 : Rat) : String :=
  let cx := (x0 + x1) / 2
  let cy := (y0 + y1) / 2
  let rx := (x1 - x0) / 2
  let ry := (y1 - y0) / 2
  let da := -2 * piR / 32
  let p := fun (i : Nat) => (cx + cosR ((i : Rat) * da) * rx, cy + sinR ((i : Rat) * da) * ry)
  ((List.range 32).foldl (fun (cl : Cloud) i => cl.line (p i) (p (i + 1))) cl).finish

/-- The cloudy outline of a closed polygon (phase carried across vertices). -/
def cloudPoly (cl : Cloud) (vs : List (Rat × Rat)) : String :=
  match vs with
  | [] => cl.out
  | v0 :: rest =>
    let (cl, last) := rest.foldl (fun (acc : Cloud × (Rat × Rat)) p => (acc.1.line acc.2 p, p))
      (cl, v0)
    (cl.line last v0).finish

/-- Square and Circle (`pdf_write_square_appearance`, `pdf_write_circle_appearance`): the
border centred on `/Rect` inset by `/RD`, at least half the line width; cloudy when `cloud`
(the `/BE` intensity) is positive (task 8.3e), the box then grown by the cloud radius. -/
def boxAp (circle : Bool) (st : Style) (orect : RBox) (rd : List Rat) (cloud : Rat := 0) :
    String × OBox :=
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
  let cl := Cloud.start st.lw cloud ic
  let path := if cloud > 0 then
      (if circle then cloudEllipse cl x y (x + w) (y + h) else cloudRect cl x y w h)
    else if circle then circleStr (w / 2) (h / 2) (x + w / 2) (y + h / 2)
    else fmt x ++ " " ++ fmt y ++ " " ++ fmt w ++ " " ++ fmt h ++ " re\n"
  let e := if cloud > 0 then e + cl.radius else e
  let r0 := max r0 e
  let r1 := max r1 e
  let r2 := max r2 e
  let r3 := max r3 e
  -- MuPDF's circle writer uses `rd.x1` for the bottom (kept for pixel equality)
  let y0 := if circle then y - r2 else y - r1
  (pre ++ path ++ paintStr sc ic, some ⟨x - r0, y0, x + w + r2, y + h + r3⟩)

/-- `x y m\nx' y' l\n`. -/
def segStr (ax ay bx by_ : Rat) : String :=
  fmt ax ++ " " ++ fmt ay ++ " m\n" ++ fmt bx ++ " " ++ fmt by_ ++ " l\n"

/-- Numbers separated by spaces (six decimals each). -/
def pts (xs : List Rat) : String := " ".intercalate (xs.map fmt)

/-- `maybe_stroke`. -/
def strokeStr (sc : Bool) : String := if sc then "S\n" else "n\n"

/-- `include_cap`: grow `r` to contain the square of half-side `d` about `(x, y)`. -/
def OBox.cap (r : OBox) (x y d : Rat) : OBox := OBox.union r (some ⟨x - d, y - d, x + d, y + d⟩)

/-- `cos 30°` to six decimals. -/
def cos30 : Rat := 866025 / 1000000

/-- `rotate_vector` for the angle with cosine `c` and sine `s`. -/
def rotV (c s x y : Rat) : Rat × Rat := (x * c - y * s, x * s + y * c)

/-- The unit direction of `(dx, dy)` (`(1, 0)` for the zero vector, as `atan2f(0, 0)`). -/
def dirOf (dx dy : Rat) : Rat × Rat :=
  let l := rsqrt (dx * dx + dy * dy)
  if l = 0 then (1, 0) else (dx / l, dy / l)

/-- `pdf_write_arrow_appearance`: an arrow head at `(x, y)` opening along `(dx, dy)`. -/
def arrowStr (r : OBox) (x y dx dy w : Rat) (close : Bool) : String × OBox :=
  let rr := max 1 w
  let (c, sn) := dirOf dx dy
  let v := rotV c sn (88 / 10 * rr) (45 / 10 * rr)
  let a := (x + v.1, y + v.2)
  let v := rotV c sn (88 / 10 * rr) (-(45 / 10) * rr)
  let b := (x + v.1, y + v.2)
  (pts [a.1, a.2] ++ " m\n" ++ pts [x, y] ++ " l\n" ++ pts [b.1, b.2] ++ " l\n" ++
    (if close then "h\n" else ""), ((r.incl a.1 a.2).incl b.1 b.2).expand w)

/-- **A line ending** (`pdf_write_line_cap_appearance`, §12.5.6.7 Table 179) at `(x, y)`, the
line running along `(dx, dy)` away from it: Square, Circle, Diamond, OpenArrow, ClosedArrow,
Butt, ROpenArrow, RClosedArrow, Slash; anything else draws nothing. MuPDF's Butt includes its
first point twice (kept). -/
def capStr (r : OBox) (x y dx dy w : Rat) (sc ic : Bool) (cap : PdfObject) : String × OBox :=
  let (dx, dy) := dirOf dx dy
  let r3 := max 3 (w * 3)
  match cap with
  | .name n =>
    if n = nm "Square" then
      (pts [x - r3, y - r3, r3 * 2, r3 * 2] ++ " re\n" ++ paintStr sc ic, r.cap x y (r3 + w / 2))
    else if n = nm "Circle" then
      (circleStr r3 r3 x y ++ paintStr sc ic, r.cap x y (r3 + w / 2))
    else if n = nm "Diamond" then
      (pts [x, y + r3] ++ " m\n" ++ pts [x + r3, y] ++ " l\n" ++ pts [x, y - r3] ++ " l\n" ++
        pts [x - r3, y] ++ " l\nh\n" ++ paintStr sc ic, r.cap x y (r3 + w / rsqrt 2))
    else if n = nm "OpenArrow" then
      let (t, r) := arrowStr r x y dx dy w false; (t ++ strokeStr sc, r)
    else if n = nm "ClosedArrow" then
      let (t, r) := arrowStr r x y dx dy w true; (t ++ paintStr sc ic, r)
    else if n = nm "Butt" then
      let a := (x - dy * r3, y + dx * r3)
      let b := (x + dy * r3, y - dx * r3)
      (segStr a.1 a.2 b.1 b.2 ++ strokeStr sc, (r.incl a.1 a.2).expand w)
    else if n = nm "ROpenArrow" then
      let (t, r) := arrowStr r x y (-dx) (-dy) w false; (t ++ strokeStr sc, r)
    else if n = nm "RClosedArrow" then
      let (t, r) := arrowStr r x y (-dx) (-dy) w true; (t ++ paintStr sc ic, r)
    else if n = nm "Slash" then
      let r5 := max 5 (w * 5)
      -- the direction turned by −30°
      let c := dx * cos30 + dy / 2
      let sn := dy * cos30 - dx / 2
      let a := (x - r5 * sn, y + r5 * c)
      let b := (x + r5 * sn, y - r5 * c)
      (segStr a.1 a.2 b.1 b.2 ++ strokeStr sc, ((r.incl a.1 a.2).incl b.1 b.2).expand w)
    else ("", r)
  | _ => ("", r)

/-- Both line endings `le` (exactly two entries, else none), at `a` (line towards `b`) and at
`b` (towards `a`'s side point `b'`). -/
def endsStr (r : OBox) (le : List PdfObject) (w : Rat) (sc ic : Bool)
    (a a' b b' : Rat × Rat) : String × OBox :=
  match le with
  | [e0, e1] =>
    let (t0, r) := capStr r a.1 a.2 (a'.1 - a.1) (a'.2 - a.2) w sc ic e0
    let (t1, r) := capStr r b.1 b.2 (b'.1 - b.1) (b'.2 - b.2) w sc ic e1
    (t0 ++ t1, r)
  | _ => ("", r)

/-- Line (`pdf_write_line_appearance` without `/Cap` captions): leader lines `/LL`, `/LLE`,
`/LLO`, line endings `/LE`; the box grown by `max 1 w`. -/
def lineAp (st : Style) (l : List Rat) (ll lle llo : Rat) (le : List PdfObject := [])
    (caption : Option ((Rat × Rat) → (Rat × Rat) → OBox → String × OBox × Rat) := none) :
    String × OBox :=
  let (pre, sc, ic) := prelude st true
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
  -- `/Cap` (task 8.3d): the caption, and the line broken by its gap when it is inline
  let (capS, segs, r) := match caption with
    | none => ("", segStr a.1 a.2 b.1 b.2, r)
    | some f =>
      let (t, r, gap) := f a b r
      if gap > 0 then
        let m := ((a.1 + b.1) / 2, (a.2 + b.2) / 2)
        (t, segStr a.1 a.2 (m.1 - dx * gap) (m.2 - dy * gap) ++
          segStr (m.1 + dx * gap) (m.2 + dy * gap) b.1 b.2, r)
      else (t, segStr a.1 a.2 b.1 b.2, r)
  let (ends, r) := endsStr r le st.lw sc ic a b b a
  (pre ++ lead ++ capS ++ segs ++ strokeStr sc ++ ends, r.expand (max 1 st.lw))

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

/-- `polygon_winding`: whether the vertices run so that MuPDF writes them in order (the
signed crossing area across the middle line is negative). -/
def polyWinding (vs : List (Rat × Rat)) : Bool :=
  match vs with
  | [] => false
  | v0 :: rest =>
    let minX := rest.foldl (fun m v => min m v.1) v0.1
    let midY := vs.foldl (fun (t : Rat) v => t + v.2) 0 / (vs.length : Rat)
    let (area, _) := rest.foldl (fun (acc : Rat × (Rat × Rat)) r =>
      let (area, q) := acc
      if (r.2 > midY ∧ midY > q.2) ∨ (r.2 < midY ∧ midY < q.2) then
        let w : Rat := if r.2 > midY then 1 else -1
        let x := r.1 + (q.1 - r.1) * (r.2 - midY) / (r.2 - q.2)
        (area + (x - minX) * w, r)
      else (area, r)) (0, v0)
    area < 0

/-- Polygon (`close`) and PolyLine (`pdf_write_polygon_appearance`): the vertices
`/Vertices`, closed and filled with `/IC` for a polygon (cloudy when `cloud` > 0, task 8.3e);
PolyLine line endings `/LE` at the first and last vertex; the box grown by the border width
(and the cloud radius). -/
def polyAp (close : Bool) (st : Style) (vs : List (Rat × Rat)) (le : List PdfObject)
    (cloud : Rat := 0) : String × OBox :=
  let (pre, sc, ic) := prelude st true
  match vs with
  | [] => (pre, none)
  | v0 :: rest =>
    let ord := if polyWinding vs then vs else vs.reverse
    let (path, r, _) := ord.foldl (fun (acc : String × OBox × Bool) p =>
      (acc.1 ++ pts [p.1, p.2] ++ (if acc.2.2 then " m\n" else " l\n"), acc.2.1.incl p.1 p.2,
        false)) ("", none, true)
    let cl := Cloud.start st.lw cloud ic
    let cloudy := close && decide (cloud > 0)
    let path := if cloudy then cloudPoly cl ord else path ++ (if close then "h\n" else "")
    let paint := if close then paintStr sc ic else strokeStr sc
    let r := r.expand (if cloudy then st.lw + cl.radius else st.lw)
    let (ends, r) := if close then ("", r) else
      match rest.reverse with
      | last :: prev :: _ => endsStr r le st.lw sc ic v0 ((rest.head?).getD v0) last prev
      | [last] => endsStr r le st.lw sc ic v0 last last v0
      | [] => ("", r)
    (pre ++ path ++ paint ++ ends, r)

/-- Most zig-zag points written per Squiggly quad (local cap; MuPDF loops while `x < w`). -/
def maxSquiggle : Nat := 10000

/-- Linear interpolation of points. -/
def lerp (a b : Rat × Rat) (t : Rat) : Rat × Rat := (a.1 + t * (b.1 - a.1), a.2 + t * (b.2 - a.2))

/-- Squiggly (`pdf_write_squiggly_appearance`): per quad a zig-zag along the bottom edge with
steps of `h / 7`, peaks at `1/7` of the height, width `h / 16`, stroke colour `/C`. -/
def squigglyAp (st : Style) (qs : List Quad) : String × OBox :=
  let (body, r) := qs.foldl (fun (acc : String × OBox) q =>
    let (ul, ur, ll, lr) := q
    let h := quadH q
    let w := rsqrt ((lr.1 - ll.1) * (lr.1 - ll.1) + (lr.2 - ll.2) * (lr.2 - ll.2))
    -- the loop runs `k` times: the least `k` with `k · h / 7 ≥ w`
    let k := if h ≤ 0 ∨ w ≤ 0 then 0 else min maxSquiggle (7 * w / h).ceil.toNat
    let zig := (List.range k).foldl (fun (t : String) i =>
      let x := ((i + 1 : Nat) : Rat) * h / 7
      let a := lerp ll lr (x / w)
      let c := if i % 2 == 0 then lerp a (lerp ul ur (x / w)) (1 / 7) else a
      t ++ pts [c.1, c.2] ++ " l\n") ""
    (acc.1 ++ fmt (h / 16) ++ " w\n" ++ pts [ll.1, ll.2] ++ " m\n" ++ zig ++ "S\n",
      unionQuad acc.2 q (h / 16))) ("", none)
  ((colorStr st.c true).getD "" ++ body, r)

/-- Caret (`pdf_write_caret_appearance`): a fixed 20 × 14 shape filled with `/C`, centred on
`/Rect`; the rectangle and the box `[0 0 20 14]`. -/
def caretAp (st : Style) (orect : RBox) : String × RBox × RBox :=
  let xc := (orect.x0 + orect.x1) / 2
  let yc := (orect.y0 + orect.y1) / 2
  ((colorStr st.c false).getD "" ++ "0 0 m\n10 0 10 7 10 14 c\n10 7 10 0 20 0 c\nf\n",
    ⟨xc - 10, yc - 7, xc + 10, yc + 7⟩, ⟨0, 0, 20, 14⟩)

/-- MuPDF icon `comment` (open-iconic, MIT). -/
def iconComment : String :=
  ".09 0 m\n" ++
  ".03 0 0 .04 0 .09 c\n" ++
  "0 5.9 l\n" ++
  "0 5.95 .04 6 .09 6 c\n" ++
  "6 6 l\n" ++
  "8 8 l\n" ++
  "8 .08 l\n" ++
  "8 .02 7.96 -.01 7.91 -.01 c\n" ++
  ".1 -.01 l\n" ++
  "h\n" ++
  "f\n"

/-- MuPDF icon `key` (open-iconic, MIT). -/
def iconKey : String :=
  "5.5 0 m\n" ++
  "4.12 0 3 1.12 3 2.5 c\n" ++
  "3 2.66 3 2.82 3.03 2.97 c\n" ++
  "0 6 l\n" ++
  "0 8 l\n" ++
  "3 8 l\n" ++
  "3 6 l\n" ++
  "5 6 l\n" ++
  "5 5 l\n" ++
  "5.03 4.97 l\n" ++
  "5.18 5 5.34 5 5.5 5 c\n" ++
  "6.88 5 8 3.88 8 2.5 c\n" ++
  "8 1.12 6.88 0 5.5 0 c\n" ++
  "h\n" ++
  "6 1 m\n" ++
  "6.55 1 7 1.45 7 2 c\n" ++
  "7 2.55 6.55 3 6 3 c\n" ++
  "5.45 3 5 2.55 5 2 c\n" ++
  "5 1.45 5.45 1 6 1 c\n" ++
  "h\n" ++
  "f\n"

/-- MuPDF icon `note` (open-iconic, MIT). -/
def iconNote : String :=
  "0 0 8 1 re\n" ++
  "0 2 8 1 re\n" ++
  "0 4 8 1 re\n" ++
  "0 6 8 1 re\n" ++
  "f\n"

/-- MuPDF icon `help` (open-iconic, MIT). -/
def iconHelp : String :=
  "1 0 0 1 1 0 cm\n" ++
  "2.47 0 m\n" ++
  "1.62 0 .99 .26 .59 .66 c\n" ++
  ".19 1.06 .05 1.56 0 1.94 c\n" ++
  "1 2.07 l\n" ++
  "1.04 1.82 1.12 1.57 1.31 1.38 c\n" ++
  "1.50 1.19 1.80 1 2.47 1.00 c\n" ++
  "3.13 1 3.49 1.16 3.69 1.34 c\n" ++
  "3.89 1.52 3.97 1.74 3.97 2 c\n" ++
  "3.97 2.83 3.63 3.06 3.13 3.50 c\n" ++
  "2.63 3.94 1.97 4.58 1.97 5.75 c\n" ++
  "1.97 6 l\n" ++
  "2.97 6 l\n" ++
  "2.97 5.75 l\n" ++
  "2.97 4.92 3.28 4.69 3.78 4.25 c\n" ++
  "4.28 3.81 4.97 3.17 4.97 2 c\n" ++
  "4.97 1.52 4.80 .98 4.38 .59 c\n" ++
  "3.95 .20 3.31 0 2.47 .00 c\n" ++
  "h\n" ++
  "1.97 7 m\n" ++
  "1.97 8 l\n" ++
  "2.97 8 l\n" ++
  "2.97 7 l\n" ++
  "1.97 7 l\n" ++
  "h\n" ++
  "f\n"

/-- MuPDF icon `graph` (open-iconic, MIT). -/
def iconGraph : String :=
  "7.03 0 m\n" ++
  "4 3 l\n" ++
  "3 2 l\n" ++
  "0 5.03 l\n" ++
  "1 6.03 l\n" ++
  "3 4 l\n" ++
  "4 5 l\n" ++
  "8 1 l\n" ++
  "7.03 0 l\n" ++
  "h\n" ++
  "0 7 m\n" ++
  "0 8 l\n" ++
  "8 8 l\n" ++
  "8 7 l\n" ++
  "0 7 l\n" ++
  "h\n" ++
  "f\n"

/-- MuPDF icon `push_pin` (open-iconic, MIT). -/
def iconPushPin : String :=
  "1.34 0 m\n" ++
  ".92 .04 .76 .64 1.1 .89 c\n" ++
  "1.34 1.08 1.65 .97 1.93 1 c\n" ++
  "2.08 .98 1.96 1.22 2 1.32 c\n" ++
  "2 1.88 2 2.44 2 3 c\n" ++
  "1.6 3.01 1.2 2.98 .8 3.02 c\n" ++
  ".35 3.11 -.01 3.54 0 4 c\n" ++
  "1 4 2 4 3 4 c\n" ++
  "3 5 3 6 3 7 c\n" ++
  "3.146 7.33 3.29 7.67 3.44 8 c\n" ++
  "3.62 7.66 3.83 7.32 4 6.98 c\n" ++
  "4 5.99 4 4.99 4 4 c\n" ++
  "5 4 6 4 7 4 c\n" ++
  "7.02 3.42 6.46 2.94 5.89 3 c\n" ++
  "5.6 3 5.3 3 5 3 c\n" ++
  "5 2.33 5 1.67 5 1 c\n" ++
  "5.30 .98 5.67 1.09 5.89 .81 c\n" ++
  "6.16 .5 5.89 -.038 5.48 0 c\n" ++
  "4.15 0 2.83 0 1.5 0 c\n" ++
  "h\n" ++
  "f\n"

/-- MuPDF icon `paperclip` (open-iconic, MIT). -/
def iconPaperclip : String :=
  "5 0 m\n" ++
  "4.49 0 3.98 .21 3.59 .59 c\n" ++
  ".81 3.31 l\n" ++
  "-.26 4.38 -.26 6.11 .81 7.19 c\n" ++
  "1.88 8.26 3.61 8.26 4.69 7.19 c\n" ++
  "5.94 5.94 l\n" ++
  "5.25 5.25 l\n" ++
  "4.09 6.38 l\n" ++
  "4 6.51 l\n" ++
  "3.31 7.2 2.19 7.2 1.5 6.51 c\n" ++
  ".82 5.83 .84 4.73 1.5 4.04 c\n" ++
  "4.28 1.29 l\n" ++
  "4.67 .9 5.32 .9 5.72 1.29 c\n" ++
  "6.11 1.68 6.09 2.3 5.72 2.7 c\n" ++
  "3.22 5.17 l\n" ++
  "3.12 5.27 2.95 5.27 2.84 5.17 c\n" ++
  "2.74 5.07 2.74 4.9 2.84 4.79 c\n" ++
  "2.9 4.76 l\n" ++
  "3.81 3.82 l\n" ++
  "3.12 3.13 l\n" ++
  "2.15 4.1 l\n" ++
  "1.67 4.58 1.67 5.37 2.15 5.85 c\n" ++
  "2.63 6.33 3.42 6.34 3.9 5.85 c\n" ++
  "6.4 3.41 l\n" ++
  "7.18 2.63 7.18 1.37 6.4 .6 c\n" ++
  "6.01 .21 5.51 .01 4.99 .01 c\n" ++
  "h\n" ++
  "f\n"

/-- MuPDF icon `tag` (open-iconic, MIT). -/
def iconTag : String :=
  "0 0 m\n" ++
  "0 3 l\n" ++
  "5 8 l\n" ++
  "8 5 l\n" ++
  "3 0 l\n" ++
  "0 0 l\n" ++
  "h\n" ++
  "2 1 m\n" ++
  "2.55 1 3 1.45 3 2 c\n" ++
  "3 2.55 2.55 3 2 3 c\n" ++
  "1.45 3 1 2.55 1 2 c\n" ++
  "1 1.45 1.45 1 2 1 c\n" ++
  "h\n" ++
  "f\n"

/-- MuPDF icon `speaker` (open-iconic, MIT). -/
def iconSpeaker : String :=
  "3.34 0 m\n" ++
  "2 2 l\n" ++
  "0 2 l\n" ++
  "0 6 l\n" ++
  "2 6 l\n" ++
  "3.34 8 l\n" ++
  "4 8 l\n" ++
  "4 0 l\n" ++
  "3.34 0 l\n" ++
  "h\n" ++
  "5 1 m\n" ++
  "5 2 l\n" ++
  "5.17 2 5.34 2.02 5.5 2.06 c\n" ++
  "6.36 2.28 7 3.06 7 4 c\n" ++
  "7 4.94 6.37 5.72 5.5 5.94 c\n" ++
  "5.34 5.98 5.17 6 5 6 c\n" ++
  "5 7 l\n" ++
  "5.25 7 5.48 6.96 5.72 6.91 c\n" ++
  "5.75 6.91 l\n" ++
  "7.05 6.58 8 5.4 8 4 c\n" ++
  "8 2.6 7.05 1.42 5.75 1.09 c\n" ++
  "5.52 1.03 5.26 1 5 1 c\n" ++
  "h\n" ++
  "5 3 m\n" ++
  "5 5 l\n" ++
  "5.09 5 5.18 4.99 5.25 4.97 c\n" ++
  "5.68 4.86 6 4.46 6 4 c\n" ++
  "6 3.54 5.69 3.14 5.25 3.03 c\n" ++
  "5.17 3.01 5.08 3 5 3 c\n" ++
  "h\n" ++
  "f\n"

/-- MuPDF icon `mic` (open-iconic, MIT). -/
def iconMic : String :=
  "1 0 0 1 1 0 cm\n" ++
  "2.91 -.03 m\n" ++
  "2.49 .03 2.11 .34 2.02 .76 c\n" ++
  "1.97 1.12 2.01 1.48 2 1.84 c\n" ++
  "2.01 2.29 1.98 2.73 2.02 3.17 c\n" ++
  "2.1 3.72 2.68 4.11 3.21 3.98 c\n" ++
  "3.7 3.89 4.05 3.39 4 2.9 c\n" ++
  "4 2.21 4.01 1.53 3.99 .84 c\n" ++
  "3.94 .32 3.43 -.09 2.91 -.03 c\n" ++
  "h\n" ++
  ".34 2 m\n" ++
  ".1 2.07 -.04 2.34 - 2.58 c\n" ++
  "-.02 3.18 .03 3.81 .32 4.34 c\n" ++
  ".75 5.18 1.58 5.78 2.5 5.94 c\n" ++
  "2.5 6.29 2.5 6.65 2.5 7 c\n" ++
  "2.11 7.01 1.68 6.94 1.36 7.23 c\n" ++
  "1.14 7.41 .96 7.75 1.02 8 c\n" ++
  "2.35 8 3.67 8 5 8 c\n" ++
  "5.02 7.43 4.47 6.94 3.9 7 c\n" ++
  "3.77 7 3.63 7 3.5 7 c\n" ++
  "3.5 6.65 3.5 6.29 3.5 5.94 c\n" ++
  "4.82 5.73 5.92 4.55 5.99 3.21 c\n" ++
  "5.99 2.93 6.02 2.65 5.98 2.37 c\n" ++
  "5.91 2.05 5.49 1.89 5.23 2.08 c\n" ++
  "5.03 2.2 4.97 2.45 5 2.66 c\n" ++
  "5.02 3.15 4.97 3.66 4.69 4.08 c\n" ++
  "4.18 4.9 3.05 5.24 2.17 4.82 c\n" ++
  "1.42 4.5 .94 3.67 1 2.86 c\n" ++
  ".99 2.61 1.05 2.32 .85 2.13 c\n" ++
  ".71 1.99 .52 1.98 .34 2 c\n" ++
  "h\n" ++
  "f\n"

/-- MuPDF icon `star` (open-iconic, MIT). -/
def iconStar : String :=
  "4 0 m\n" ++
  "3 3 l\n" ++
  "0 3 l\n" ++
  "2.5 5 l\n" ++
  "1.5 8 l\n" ++
  "4 6 l\n" ++
  "6.5 8 l\n" ++
  "5.5 5 l\n" ++
  "8 3 l\n" ++
  "5 3 l\n" ++
  "4 0 l\n" ++
  "h\n" ++
  "f\n"

/-- MuPDF icon `insert` (open-iconic, MIT). -/
def iconInsert : String :=
  "8 5 m\n" ++
  "4 0 l\n" ++
  "0 5 l\n" ++
  "f\n"

/-- MuPDF icon `new_paragraph` (open-iconic, MIT). -/
def iconNewParagraph : String :=
  "8 8 m\n" ++
  "4 0 l\n" ++
  "0 8 l\n" ++
  "f\n"

/-- MuPDF icon `paragraph` (open-iconic, MIT). -/
def iconParagraph : String :=
  "7 0 m\n" ++
  "2 0 l\n" ++
  "1 0 0 1 0 2 c\n" ++
  "0 3 1 4 2 4 c\n" ++
  "3 4 l\n" ++
  "3 8 l\n" ++
  "4 8 l\n" ++
  "4 1 l\n" ++
  "5 1 l\n" ++
  "5 8 l\n" ++
  "6 8 l\n" ++
  "6 1 l\n" ++
  "7 1 l\n" ++
  "f\n"

/-- The icon path for icon name `n` (`pdf_write_icon_appearance`; unknown: the star). -/
def iconPath (n : Name) : String :=
  let tbl : List (String × String) := [("Comment", iconComment), ("Key", iconKey),
    ("Note", iconNote), ("Help", iconHelp), ("NewParagraph", iconNewParagraph),
    ("Paragraph", iconParagraph), ("Insert", iconInsert), ("Graph", iconGraph),
    ("PushPin", iconPushPin), ("Paperclip", iconPaperclip), ("Tag", iconTag),
    ("Speaker", iconSpeaker), ("Mic", iconMic)]
  match tbl.find? (fun e => nm e.1 = n) with
  | some e => e.2
  | none => iconStar

/-- `pdf_is_dark_fill_color` of colour `c` (`/C`). -/
def darkFill (c : List Rat) : Bool :=
  let g : Rat := match c with
    | [k] => k
    | [r, g, b] => r * 3 / 10 + g * 59 / 100 + b * 11 / 100
    | [cy, m, y, k] => 1 - min (cy * 3 / 10 + m * 59 / 100 + y * 11 / 100 + k) 1
    | _ => 1
  g < 1 / 4

/-- Text, FileAttachment and Sound icons (`pdf_write_icon_appearance`): a 15 × 15 square filled
with `/C` (else white) and stroked black, the 8 × 8 icon flipped into it in white on a dark fill
(else black); an 18 × 18 rectangle centred on `/Rect` and the box `[0 0 16 16]`. -/
def iconAp (st : Style) (name : Name) (orect : RBox) : String × RBox × RBox :=
  let xc := (orect.x0 + orect.x1) / 2
  let yc := (orect.y0 + orect.y1) / 2
  ((colorStr st.c false).getD "1 g\n" ++ "1 w\n0.5 0.5 15 15 re\nb\n" ++ "1 0 0 -1 4 12 cm\n" ++
    (if darkFill st.c then "1 g\n" else "0 g\n") ++ iconPath name,
    ⟨xc - 9, yc - 9, xc + 9, yc + 9⟩, ⟨0, 0, 16, 16⟩)

/-! ### FreeText and Stamp (task 8.3d; MuPDF `pdf_write_free_text_appearance`,
`pdf_write_stamp_appearance`)

**FreeText.** `/Contents` (a text string: UTF-16 or UTF-8 with a byte-order mark, else
PDFDocEncoding; at most `maxSynthText` characters) is laid out like MuPDF's
`write_variable_text` (multi-line, `break_string`: break at the last space once a line is wider
than the box, at `\n` and `\r`), aligned by `/Q` (0 left, 1 centre, 2 right; other values 0),
first baseline `0.8 · size` below the top of the padded box, lines `1.2 · size` apart. `/DA` (on
the annotation or its `/Parent` chain, else the catalog's `/AcroForm /DA` (task 8.3e,
`pdf_annot_default_appearance`); `pdf_parse_default_appearance`: the first 99 bytes,
whitespace-separated tokens, `/Name`, `Tf`, `g`, `rg`, `k`, a four-slot operand stack with
`strtof` prefixes) gives the font (`Helv`, `Cour`, `TiRo`, `Symb`, `ZaDb`; anything else
`Helv`), the size (0 → 12) and the text and border colour. The box is `/Rect` inset by `/RD`;
`/C` fills it, the border (`/BS /W`, `/Border`, else 1; dash) is stroked inside it, the text is
clipped to the box less the border, padded by twice the border width; `/Rotate` 90, 180, 270
turns the text inside the box; a `/IT /FreeTextCallout` with a 4- or 6-number `/CL` draws the
callout line with the `/LE` ending and grows the rectangle. The font resource is MuPDF's
`pdf_add_simple_font` of a base-14 font: `<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica
/Encoding /WinAnsiEncoding >>` under the resource name; widths are the AFM widths
(`Std14.width?`; MuPDF's URW fonts are metric-compatible). Characters outside Windows-1252 are
written as `0xB7` (MuPDF: Greek, Cyrillic and CJK go through extra fonts — a recorded gap).

**Stamp.** MuPDF's built-in stamp: `/Name` (default `Draft`) selects the text (`APPROVED`, `AS
IS`, …, two lines for the public-release stamps, the name itself otherwise), Times-Bold, centred
in a `[0 0 190 50]` form box with a 2-point frame, all turned by 0.6°; `/C` is the fill and
stroke colour; the rectangle is shrunk to the box's aspect ratio about its centre.

Rich text `/RC` and `/DS`: task 8.3e, below (`richStyle`, `richText`). Recorded gaps: FreeText
`/Rotate` other than multiples of 90 (left unturned). The rasterizer does not draw text of
non-embedded base-14 fonts yet; text extraction sees it. -/

/-- Most characters of `/Contents` laid out (local cap). -/
def maxSynthText : Nat := 65536

/-- Swap the bytes of each pair (UTF-16LE → UTF-16BE). -/
def swapPairs : List UInt8 → List UInt8
  | a :: b :: r => b :: a :: swapPairs r
  | r => r

/-- A PDFDocEncoding byte as a character (unassigned: the byte as Latin-1). -/
def pdfDocChar (b : UInt8) : Char :=
  let n := b.toNat
  match Font.pdfDocNames[n]? with
  | some g =>
    if g.isEmpty then Char.ofNat n
    else ((Font.glyphToUnicode g).bind (·.toList.head?)).getD (Char.ofNat n)
  | none => Char.ofNat n

/-- UTF-8 bytes as characters (invalid: Latin-1). -/
def utf8Chars (bs : List UInt8) : List Char :=
  match String.fromUTF8? ⟨bs.toArray⟩ with
  | some s => s.toList
  | none => bs.map fun b => Char.ofNat b.toNat

/-- **A text string** (§7.9.2.2, `pdf_to_text_string`). -/
def textOf (bs : List UInt8) : List Char :=
  match bs with
  | 0xFE :: 0xFF :: rest => Font.CMap.utf16 rest
  | 0xFF :: 0xFE :: rest => Font.CMap.utf16 (swapPairs rest)
  | 0xEF :: 0xBB :: 0xBF :: rest => utf8Chars rest
  | _ => bs.map pdfDocChar

/-- `fz_windows_1252_from_unicode`: the Windows-1252 code of a character, if any. -/
def win1252 (u : Char) : Option Nat :=
  let n := u.toNat
  if n < 128 then some n
  else if 0xA0 ≤ n ∧ n ≤ 0xFF then some n
  else ((List.range 32).map (· + 128)).find? fun c =>
    !([0x81, 0x8D, 0x8F, 0x90, 0x9D] : List Nat).contains c &&
      match Font.winAnsiNames[c]? with
      | some g => Font.glyphToUnicode g == some (String.singleton u)
      | none => false

/-- The code written for a character (`REPLACEMENT` 0xB7 outside Windows-1252). -/
def code1252 (u : Char) : Nat := (win1252 u).getD 0xB7

/-- The advance (em) of character `u` in base-14 font `f` (0 when not encodable or no glyph). -/
def charWidth (f : Font.Std14) (u : Char) : Rat :=
  match win1252 u with
  | none => 0
  | some c =>
    let g := match f with
      | .symbol => (Font.symbolNames[c]?).getD ""
      | .zapfDingbats => (Font.zapfDingbatsNames[c]?).getD ""
      | _ => (Font.winAnsiNames[c]?).getD ""
    (((Font.Std14.width? f g).getD 0 : Nat) : Rat) / 1000

/-- An octal digit. -/
def octDigit (d : Nat) : Char := Char.ofNat (48 + d % 8)

/-- One byte inside a literal string: `(`, `)`, `\` escaped, other bytes outside printable
ASCII as `\ooo` (the same string as MuPDF's raw byte). -/
def strByte (c : Nat) : String :=
  if c == 40 || c == 41 || c == 92 then "\\" ++ String.singleton (Char.ofNat c)
  else if c < 32 || c ≥ 127 then
    String.ofList ['\\', octDigit (c / 64), octDigit (c / 8), octDigit c]
  else String.singleton (Char.ofNat c)

/-- A literal string of the Windows-1252 codes of `cs`. -/
def litStr (cs : List Char) : String :=
  "(" ++ String.join (cs.map fun u => strByte (code1252 u)) ++ ")"

/-- What `/DA` gives (`pdf_parse_default_appearance`). -/
structure DAInfo where
  /-- Font resource name: `Helv`, `Cour`, `TiRo`, `Symb` or `ZaDb`. -/
  font : String := "Helv"
  /-- Font size. -/
  size : Rat := 12
  /-- Colour (0, 1, 3 or 4 components). -/
  color : List Rat := []

/-- The parser state: what was read, the four operand slots and their top. -/
structure DAState where
  /-- What was read. -/
  info : DAInfo := {}
  /-- Operand slots. -/
  stack : List Rat := [0, 0, 0, 0]
  /-- Next slot. -/
  top : Nat := 0

/-- Decimal digits at the front: value, count, rest. -/
def takeDigits : List Char → Nat × Nat × List Char
  | c :: cs =>
    if c.isDigit then
      let (v, n, r) := takeDigits cs
      ((c.toNat - 48) * 10 ^ n + v, n + 1, r)
    else (0, 0, c :: cs)
  | [] => (0, 0, [])

/-- `strtof` on a token: the value of its longest `[±]digits[.digits]` prefix (0 if none), and
whether that prefix is the whole token. (Exponents, `inf`, `nan` and hex floats are not read.) -/
def strtof (cs : List Char) : Rat × Bool :=
  let (neg, cs1) := match cs with
    | '-' :: r => (true, r)
    | '+' :: r => (false, r)
    | _ => (false, cs)
  let (iv, ni, r1) := takeDigits cs1
  let (fv, nf, rest) := match r1 with
    | '.' :: r => takeDigits r
    | _ => (0, 0, r1)
  if ni + nf = 0 then (0, false)
  else
    let v : Rat := (iv : Rat) + (fv : Rat) / ((10 ^ nf : Nat) : Rat)
    (if neg then -v else v, rest.isEmpty)

/-- One `/DA` token. -/
def daStep (st : DAState) (tok : List Char) : DAState :=
  let s := fun (i : Nat) => nth st.stack i
  match tok with
  | '/' :: n => { st with info := { st.info with font := String.ofList n } }
  | _ =>
    let t := String.ofList tok
    if t == "Tf" then { st with info := { st.info with size := s 0 }, top := 0 }
    else if t == "g" then { st with info := { st.info with color := [s 0] }, top := 0 }
    else if t == "rg" then { st with info := { st.info with color := [s 0, s 1, s 2] }, top := 0 }
    else if t == "k" then
      { st with info := { st.info with color := [s 0, s 1, s 2, s 3] }, top := 0 }
    else
      let (v, full) := strtof tok
      { st with stack := if st.top < 4 then st.stack.set st.top v else st.stack,
                top := if full then st.top + 1 else 0 }

/-- `/DA` whitespace. -/
def isDAWs (c : Char) : Bool := c == ' ' || c == '\n' || c == '\r' || c == '\t'

/-- Split at whitespace, dropping empty tokens (`cur`: the current token, reversed). -/
def splitWs : List Char → List Char → List (List Char)
  | [], cur => if cur.isEmpty then [] else [cur.reverse]
  | c :: cs, cur =>
    if isDAWs c then (if cur.isEmpty then splitWs cs [] else cur.reverse :: splitWs cs [])
    else splitWs cs (c :: cur)

/-- **Parse a default appearance string** (C string: up to the first NUL, first 99 bytes). -/
def parseDA (bs : List UInt8) : DAInfo :=
  let cs := ((bs.takeWhile (· != 0)).take 99).map fun b => Char.ofNat b.toNat
  let st := (splitWs cs []).foldl daStep {}
  let f := st.info.font
  { st.info with
    font := if ["Cour", "Helv", "TiRo", "Symb", "ZaDb"].contains f then f else "Helv" }

/-- The base-14 font and `/BaseFont` of a `/DA` font name (`full_font_name`). -/
def stdOf (n : String) : Font.Std14 × String :=
  if n == "Cour" then (.courier, "Courier")
  else if n == "TiRo" then (.timesRoman, "Times-Roman")
  else if n == "Symb" then (.symbol, "Symbol")
  else if n == "ZaDb" then (.zapfDingbats, "ZapfDingbats")
  else (.helvetica, "Helvetica")

/-- MuPDF's font dictionary for a built-in base-14 font (`pdf_add_simple_font`, Latin). -/
def stdFontDict (base : String) : PdfObject :=
  .dict [(nm "Type", .name (nm "Font")), (nm "Subtype", .name (nm "Type1")),
    (nm "BaseFont", .name (nm base)), (nm "Encoding", .name (nm "WinAnsiEncoding"))]

/-- `write_color0`: a colour operator, black for no colour. -/
def color0Str (c : List Rat) (stroke : Bool) : String :=
  if c.isEmpty then (if stroke then "0 G\n" else "0 g\n") else (colorStr c stroke).getD ""

/-- **`break_string`**: characters consumed by the next line (a line break included) and its
width; breaks after the last space once the width exceeds `maxw`. -/
def breakLine (wd : Char → Rat) (size maxw : Rat) :
    List Char → Nat → Rat → Option (Nat × Rat) → Nat × Rat
  | [], i, x, _ => (i, x)
  | u :: us, i, x, sp =>
    if u == '\n' || u == '\r' then (i + 1, x)
    else
      let sp := if u == ' ' then some (i + 1, x) else sp
      let x := x + wd u * size
      match sp with
      | some p => if x > maxw then p else breakLine wd size maxw us (i + 1) x sp
      | none => breakLine wd size maxw us (i + 1) x sp

/-- The lines of `cs` (`write_string_with_quadding`): text without its line break, and width. -/
def layoutLines (wd : Char → Rat) (size maxw : Rat) : Nat → List Char → List (List Char × Rat)
  | 0, _ => []
  | _, [] => []
  | f + 1, cs =>
    let (k, w) := breakLine wd size maxw cs 0 0 none
    let k := max k 1
    let line := cs.take k
    let body := match line.getLast? with
      | some c => if c == '\n' || c == '\r' then line.dropLast else line
      | none => line
    (body, w) :: layoutLines wd size maxw f (cs.drop k)

/-- The text lines, aligned by `q` in width `maxw`, each a `Td` down by `lh` then
`/font size Tf (…) Tj` (an empty line writes no string); `trim`: trailing spaces are not
written (an HTML story, task 8.3e). -/
def linesStr (f : Font.Std14) (font : String) (size lh maxw : Rat) (q : Nat) (cs : List Char)
    (trim : Bool := false) :
    String :=
  let (out, _) := (layoutLines (charWidth f) size maxw cs.length cs).foldl
    (fun (acc : String × Rat) (line0, w) =>
      let line := if trim then (line0.reverse.dropWhile (· == ' ')).reverse else line0
      let x := if q == 1 then (maxw - w) / 2 else if q == 2 then maxw - w else 0
      (acc.1 ++ pts [x - acc.2, -lh] ++ " Td\n" ++
        (if line.isEmpty then "" else "/" ++ font ++ " " ++ fmt size ++ " Tf\n" ++ litStr line ++
          " Tj\n"), x)) ("", 0)
  out

/-- `fz_rotate` entries `(a, b, c, d)` for a multiple of 90° (else the identity). -/
def rotEntries (r : Int) : Rat × Rat × Rat × Rat :=
  let m := r % 360
  if m = 90 then (0, 1, -1, 0) else if m = 180 then (-1, 0, 0, -1)
  else if m = 270 then (0, -1, 1, 0) else (1, 0, 0, 1)

/-! #### Rich text (task 8.3e)

MuPDF 1.25.1 (built with its HTML engine, as `mutool`) lays out a FreeText with `/RC`, or with
`/DS` and `/Contents`, as an HTML story (`write_rich_content`): the text is `/RC` (XHTML), else
`/Contents` escaped; the CSS is `body{margin:0} p{margin:0}` plus `body{<DS>}`; the default
size is `/DA`'s, the default font the engine's serif font, the default colour black (not `/DA`'s:
`/DA` still colours the border); the story is placed in the box from `x = 2b` to `x = w − 4b` (`b`
the border width), the first baseline `0.9 · size` below its top and lines `1.2 · size` apart
(measured with `mutool draw -F stext`); `/Q` is not used (CSS `text-align` is).

This is a subset of that engine: `/DS` declarations `font-size` (`pt`, `px` = pt, `em`, `%`),
`font-family` and the `font` shorthand (size and family), `color` (`#rgb`, `#rrggbb`,
`rgb(r, g, b)`, sixteen names) and `text-align` (`left`, `center`, `right`; `justify` as left);
families map to base-14 fonts: `courier`/`mono…` → Courier, `helvetica`/`arial`/`sans…` →
Helvetica, anything else → Times (MuPDF's default serif is Charis SIL: same text, other widths).
`/RC` markup is reduced to its text: tags dropped, `<br>` and the ends of `p`, `div` and
`h1`–`h6` break lines, the five XML entities and `&#N;`/`&#xN;` decoded; whitespace collapses
to one space and empty lines are dropped, as HTML does. Recorded gaps: inline styles of `/RC`
(`<span style>`, `<b>`, `<i>`: bold and italic faces), CSS `line-height`, margins and
`vertical-align`. -/

/-- Lower case (ASCII). -/
def lower (cs : List Char) : List Char := cs.map Char.toLower

/-- Trim ASCII whitespace at both ends. -/
def trimWs (cs : List Char) : List Char :=
  ((cs.dropWhile isDAWs).reverse.dropWhile isDAWs).reverse

/-- Whether `pat` occurs in `cs`. -/
def containsCs (cs pat : List Char) : Bool :=
  ((String.ofList cs).splitOn (String.ofList pat)).length > 1

/-- Split at a separator character. -/
def splitOnChar (sep : Char) (cs : List Char) : List (List Char) :=
  ((String.ofList cs).splitOn (String.ofList [sep])).map String.toList

/-- A CSS length: the number, then `pt`/`px`/nothing (points), `em` (× `base`) or `%`;
`none` without digits or for another unit. -/
def cssLen (base : Rat) (cs : List Char) : Option Rat :=
  let num := cs.takeWhile fun c => c.isDigit || c == '.' || c == '-' || c == '+'
  let unit := lower (cs.drop num.length)
  if !num.any Char.isDigit then none else
  let v := (strtof num).1
  if unit = [] ∨ unit = "pt".toList ∨ unit = "px".toList then some v
  else if unit = "em".toList then some (v * base)
  else if unit = ['%'] then some (v * base / 100)
  else none

/-- The base-14 resource name of a CSS font family list. -/
def cssFamily (cs : List Char) : String :=
  let l := lower cs
  if containsCs l "courier".toList || containsCs l "mono".toList then "Cour"
  else if containsCs l "helvetica".toList || containsCs l "arial".toList ||
    containsCs l "sans".toList then "Helv"
  else "TiRo"

/-- A hexadecimal digit's value. -/
def hexVal (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - 48)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 55)
  else none

/-- An RGB colour from bytes. -/
def rgb255 (r g b : Nat) : List Rat := [(r : Rat) / 255, (g : Rat) / 255, (b : Rat) / 255]

/-- The sixteen basic CSS colour names. -/
def cssNamed : List (String × Nat × Nat × Nat) :=
  [("black", 0, 0, 0), ("silver", 192, 192, 192), ("gray", 128, 128, 128),
   ("grey", 128, 128, 128), ("white", 255, 255, 255), ("maroon", 128, 0, 0),
   ("red", 255, 0, 0), ("purple", 128, 0, 128), ("fuchsia", 255, 0, 255),
   ("green", 0, 128, 0), ("lime", 0, 255, 0), ("olive", 128, 128, 0), ("yellow", 255, 255, 0),
   ("navy", 0, 0, 128), ("blue", 0, 0, 255), ("teal", 0, 128, 128), ("aqua", 0, 255, 255)]

/-- A CSS colour (see the section doc); `none` if not understood. -/
def cssColor (cs : List Char) : Option (List Rat) :=
  let l := lower (trimWs cs)
  match l with
  | '#' :: hs =>
    match hs.mapM hexVal with
    | some [r, g, b] => some (rgb255 (r * 17) (g * 17) (b * 17))
    | some [r1, r2, g1, g2, b1, b2] => some (rgb255 (r1 * 16 + r2) (g1 * 16 + g2) (b1 * 16 + b2))
    | _ => none
  | 'r' :: 'g' :: 'b' :: '(' :: rest =>
    let inner := rest.takeWhile (· != ')')
    match (splitOnChar ',' inner).map (fun p => (strtof (trimWs p)).1) with
    | [r, g, b] =>
      let cl := fun (x : Rat) => max 0 (min 1 (x / 255))
      some [cl r, cl g, cl b]
    | _ => none
  | _ => (cssNamed.find? (·.1 == String.ofList l)).map fun (_, r, g, b) => rgb255 r g b

/-- The text style of a rich FreeText: font, size and colour (as `DAInfo`), and alignment. -/
structure RichStyle where
  /-- Font resource name, size, colour (empty: black). -/
  da : DAInfo
  /-- `text-align`: 0 left, 1 centre, 2 right. -/
  align : Nat := 0

/-- One CSS declaration `prop: value` applied to `st`. -/
def cssDecl (base : Rat) (st : RichStyle) (decl : List Char) : RichStyle :=
  let prop := lower (trimWs (decl.takeWhile (· != ':')))
  let val := trimWs ((decl.dropWhile (· != ':')).drop 1)
  let p := String.ofList prop
  if p == "font-size" then
    match cssLen base val with
    | some v => { st with da := { st.da with size := v } }
    | none => st
  else if p == "font-family" then { st with da := { st.da with font := cssFamily val } }
  else if p == "font" then
    let toks := splitWs val []
    match toks.findIdx? (fun t => (cssLen base t).isSome) with
    | some i =>
      let sz := (toks[i]?.bind (cssLen base)).getD st.da.size
      let fam := toks.drop (i + 1)
      let fnt := if fam.isEmpty then st.da.font else cssFamily (" ".toList.intercalate fam)
      let d : DAInfo := { font := fnt, size := sz, color := st.da.color }
      { st with da := d }
    | none => st
  else if p == "color" then
    match cssColor val with
    | some c => { st with da := { st.da with color := c } }
    | none => st
  else if p == "text-align" then
    let v := String.ofList (lower val)
    { st with align := if v == "center" then 1 else if v == "right" then 2 else 0 }
  else st

/-- **The style of a rich FreeText**: `/DS` over the defaults (serif, `/DA`'s size, black). -/
def richStyle (daSize : Rat) (ds : List Char) : RichStyle :=
  let base := if daSize = 0 then 12 else daSize
  (splitOnChar ';' ds).foldl (cssDecl base) { da := { font := "TiRo", size := base, color := [] } }

/-- An XML entity body (between `&` and `;`). -/
def entityChar (e : List Char) : Option Char :=
  let s := String.ofList e
  if s == "lt" then some '<' else if s == "gt" then some '>' else if s == "amp" then some '&'
  else if s == "quot" then some '"' else if s == "apos" then some '\''
  else match e with
    | '#' :: 'x' :: hs | '#' :: 'X' :: hs =>
      (hs.mapM hexVal).map fun ds => Char.ofNat (ds.foldl (fun a d => a * 16 + d) 0)
    | '#' :: ds =>
      if !ds.isEmpty && ds.all Char.isDigit then
        some (Char.ofNat (ds.foldl (fun a d => a * 10 + (d.toNat - 48)) 0))
      else none
    | _ => none

/-- Whether a tag (its text between `<` and `>`) breaks the line: `br`, or the end of `p`,
`div`, `h1`–`h6`. -/
def tagBreaks (t : List Char) : Bool :=
  let l := lower t
  let name := (l.takeWhile fun c => !isDAWs c && c != '/' && c != '>')
  let n := String.ofList name
  n == "br" ||
    (l.head? == some '/' &&
      ["p", "div", "h1", "h2", "h3", "h4", "h5", "h6"].contains (String.ofList
        ((l.drop 1).takeWhile fun c => !isDAWs c && c != '>')))

/-- The text of XHTML markup, `\n` at line breaks (fuel: the length). -/
def markupText : Nat → List Char → List Char
  | 0, _ => []
  | _, [] => []
  | f + 1, '<' :: rest =>
    let tag := rest.takeWhile (· != '>')
    (if tagBreaks tag then ['\n'] else []) ++ markupText f ((rest.drop tag.length).drop 1)
  | f + 1, '&' :: rest =>
    let e := rest.takeWhile (· != ';')
    match (if e.length ≤ 10 then entityChar e else none) with
    | some c => c :: markupText f ((rest.drop e.length).drop 1)
    | none => '&' :: markupText f rest
  | f + 1, c :: rest => c :: markupText f rest

/-- Collapse each run of whitespace to one space (HTML `white-space: normal`). -/
def collapseWs : List Char → Bool → List Char
  | [], _ => []
  | c :: cs, prevWs =>
    if isDAWs c then (if prevWs then collapseWs cs true else ' ' :: collapseWs cs true)
    else c :: collapseWs cs false

/-- **Rich text lines** (`/RC` markup when `markup`, else plain `/Contents`): whitespace
collapsed per line, trimmed, empty lines dropped, joined by `\n`. -/
def richText (markup : Bool) (cs : List Char) : List Char :=
  let raw := if markup then markupText cs.length cs else collapseWs cs false
  let lines := (splitOnChar '\n' raw).map fun l => trimWs (collapseWs l false)
  ['\n'].intercalate (lines.filter (!·.isEmpty))

/-- **FreeText** (`pdf_write_free_text_appearance`; see the section doc): content, resources
and the rectangle (also the form box); `rich`: the style of rich text (task 8.3e), whose
`text` is already `richText`. -/
def freeTextAp (st : Style) (orect : RBox) (text : List Char) (q : Nat) (da : DAInfo)
    (rd : List Rat) (r : Int) (callout : List Rat) (le : PdfObject)
    (rich : Option RichStyle := none) : String × Dict × OBox :=
  let tb : RBox := ⟨orect.x0 + nth rd 0, orect.y0 + nth rd 1, orect.x1 - nth rd 2,
    orect.y1 - nth rd 3⟩
  let w := tb.x1 - tb.x0
  let h := tb.y1 - tb.y0
  let (gs, res) := opacityRes false st.ca
  let ic := colorStr st.c false
  let b := st.lw
  let head := gs ++ dashStr st.dash ++ ic.getD "" ++ color0Str da.color true ++ fmt b ++ " w\n"
  let (call, rect) : String × OBox :=
    if callout.length = 4 ∨ callout.length = 6 then
      let ps := (List.range (callout.length / 2)).map fun k =>
        (nth callout (2 * k), nth callout (2 * k + 1))
      let rect := ps.foldl (fun (r : OBox) p => r.incl p.1 p.2) (some tb)
      let path := (match ps with
        | p0 :: rest => pts [p0.1, p0.2] ++ " m\n" ++
            String.join (rest.map fun p => pts [p.1, p.2] ++ " l\n")
        | [] => "") ++ "S\n"
      let (cap, rect) := capStr rect (nth callout 0) (nth callout 1)
        (nth callout 2 - nth callout 0) (nth callout 3 - nth callout 1) b true ic.isSome le
      (path ++ cap, rect)
    else ("", some tb)
  let bg := if ic.isSome then pts [tb.x0, tb.y0, w, h] ++ " re\nf\n" else ""
  let border := if b > 0 then pts [tb.x0 + b / 2, tb.y0 + b / 2, w - b, h - b] ++ " re\nS\n"
    else ""
  let clip := pts [tb.x0 + b, tb.y0 + b, w - b * 2, h - b * 2] ++ " re\nW\nn\n"
  let (w, h) := if r = 90 ∨ r = 270 then (h, w) else (w, h)
  let (ra, rb, rc, rdd) := rotEntries r
  let (e, f) : Rat × Rat :=
    if r = 270 then (0, w) else if r = 90 then (h, 0) else if r = 180 then (w, h) else (0, 0)
  let cm := "q\n" ++ pts [ra, rb, rc, rdd, e + tb.x0, f + tb.y0] ++ " cm\n"
  let pad := b * 2
  -- rich text: the story's box runs from `2b` to `w − 4b`, first baseline `0.9 · size` down
  let (tda, q, tw, base) := match rich with
    | some rs => (rs.da, rs.align, w - pad * 3, (9 : Rat) / 10)
    | none => (da, q, w - pad * 2, (4 : Rat) / 5)
  let th := h - pad * 2
  let size := if tda.size = 0 then 12 else tda.size
  let lh := size * 6 / 5
  let (f14, _) := stdOf tda.font
  let body := "BT\n" ++ color0Str tda.color false ++ pts [pad, pad + th - size * base + lh] ++
    " Td\n" ++ linesStr f14 tda.font size lh tw q text rich.isSome ++ "ET\n"
  let fontRes : Dict := [(nm "Font", .dict [(nm tda.font, stdFontDict (stdOf tda.font).2)])]
  (head ++ call ++ bg ++ border ++ clip ++ cm ++ body ++ "Q\n", res ++ fontRes, rect)

/-- The texts of MuPDF's built-in stamps: `(text, baseline, size)`. -/
def stampTexts (n : String) : List (String × Rat × Rat) :=
  let big := fun (t : String) => [(t, (13 : Rat), (30 : Rat))]
  let small := fun (t : String) => [(t, (17 : Rat), (20 : Rat))]
  if n == "Approved" then big "APPROVED" else if n == "AsIs" then big "AS IS"
  else if n == "Confidential" then small "CONFIDENTIAL"
  else if n == "Departmental" then small "DEPARTMENTAL"
  else if n == "Experimental" then small "EXPERIMENTAL"
  else if n == "Expired" then big "EXPIRED" else if n == "Final" then big "FINAL"
  else if n == "ForComment" then small "FOR COMMENT"
  else if n == "ForPublicRelease" then [("FOR PUBLIC", 26, 18), ("RELEASE", 17 / 2, 18)]
  else if n == "NotApproved" then small "NOT APPROVED"
  else if n == "NotForPublicRelease" then [("NOT FOR", 26, 18), ("PUBLIC RELEASE", 17 / 2, 18)]
  else if n == "Sold" then big "SOLD" else if n == "TopSecret" then [("TOP SECRET", 14, 26)]
  else if n == "Draft" then big "DRAFT"
  else small n

/-- `write_stamp`: one line of Times-Bold at `h` points centred in the 190-wide box. -/
def stampLine (t : List Char) (y h : Rat) : String :=
  let tw := (t.map fun u => charWidth .timesBold (if (win1252 u).isSome then u else '·')).foldl
    (· + ·) 0 * h
  "BT\n/Times " ++ fmt h ++ " Tf\n" ++ pts [(190 - tw) / 2, y] ++ " Td\n" ++ litStr t ++
    " Tj\nET\n"

/-- **Stamp** (`pdf_write_stamp_appearance`; `name`: the `/Name` text, `Draft` when absent):
content, resources, the new rectangle and the form box `[0 0 190 50]`. -/
def stampAp (st : Style) (orect : RBox) (name : String) : String × Dict × RBox × RBox :=
  let (gs, res) := opacityRes false st.ca
  let lines := (stampTexts name).map fun (t, y, h) => stampLine t.toList y h
  let c := gs ++ (colorStr st.c false).getD "" ++ (colorStr st.c true).getD "" ++
    "0.999945 0.010472 -0.010472 0.999945 0 0 cm\n2 w\n2 2 186 44 re\nS\n" ++ String.join lines
  let w := orect.x1 - orect.x0
  let h := orect.y1 - orect.y0
  let xs := w / 190
  let ys := h / 50
  let r : RBox := if xs > ys then
      let xc := (orect.x1 + orect.x0) / 2
      { orect with x0 := xc - 95 * ys, x1 := xc + 95 * ys }
    else
      let yc := (orect.y1 + orect.y0) / 2
      { orect with y0 := yc - 25 * xs, y1 := yc + 25 * xs }
  (c, res ++ [(nm "Font", .dict [(nm "Times", stdFontDict "Times-Bold")])], r, ⟨0, 0, 190, 50⟩)

/-- **Line caption** (`pdf_write_line_caption`, task 8.3d): `/Contents` in Helvetica 12, black,
along the line from `a` to `b` (turned to its direction), centred on its middle; inline (0.3 ·
size below the line's axis, the line broken by the returned gap) unless `/CP /Top`, an offset
`/CO`, or the text does not fit (`top`: 0.2 · size above, no gap). The rectangle grows to the
text's ends, expanded by the size. -/
def captionStr (text : List Char) (cpTop : Bool) (cox coy : Rat) (a b : Rat × Rat) (r : OBox) :
    String × OBox × Rat :=
  let len := rsqrt ((b.1 - a.1) * (b.1 - a.1) + (b.2 - a.2) * (b.2 - a.2))
  let dx := (b.1 - a.1) / len
  let dy := (b.2 - a.2) / len
  let size : Rat := 12
  let tw := (text.map (charWidth .helvetica)).foldl (· + ·) 0 * size
  let top := cpTop || tw + size > len
  let e := (a.1 + b.1) / 2 - dx * (tw / 2)
  let f := (a.2 + b.2) / 2 - dy * (tw / 2)
  let (top, e, f) :=
    if cox ≠ 0 ∨ coy ≠ 0 then
      let coy := if coy < 0 then coy - size else coy
      (true, e + cox * dx - coy * dy, f + cox * dy + coy * dx)
    else if top then (top, e - dy * size / 5, f + dx * size / 5)
    else (top, e + dy * size * 3 / 10, f - dx * size * 3 / 10)
  let t := "q\n" ++ pts [dx, dy, -dy, dx, e, f] ++ " cm\n0 g\nBT\n" ++
    (if text.isEmpty then "" else "/Helv " ++ fmt size ++ " Tf\n" ++ litStr text ++ " Tj\n") ++
    "ET\nQ\n"
  let r := ((r.incl (e - dx * tw / 2) (f - dy * tw / 2)).incl (e + dx * tw / 2)
    (f + dy * tw / 2)).expand size
  (t, r, if top then 0 else (tw + size / 2) / 2)

/-- The value of key `k` on `d` or its `/Parent` chain (`pdf_dict_get_inheritable`), resolved
one level; at most `fuel` levels up. -/
def inheritGet {σ : Type} (src : Source σ) (k : Name) : Nat → Dict → σ → Option PdfObject × σ
  | 0, d, s => match Dict.get? d k with
    | some o => let (v, s) := Run.resolve src s o; (some v, s)
    | none => (none, s)
  | f + 1, d, s =>
    match Dict.get? d k with
    | some o => let (v, s) := Run.resolve src s o; (some v, s)
    | none =>
      match Dict.get? d (nm "Parent") with
      | none => (none, s)
      | some p =>
        match Run.resolve src s p with
        | (.dict pd, s) => inheritGet src k f pd s
        | (_, s) => (none, s)

/-- A string value's bytes (resolved one level; anything else: empty). -/
def strOf {σ : Type} (src : Source σ) (s : σ) : Option PdfObject → List UInt8 × σ
  | none => ([], s)
  | some o => match Run.resolve src s o with
    | (.string b, s) => (b, s)
    | (_, s) => ([], s)

/-- An integer value (`pdf_dict_get_int`: a real is truncated; anything else 0). -/
def intOf {σ : Type} (src : Source σ) (s : σ) : Option PdfObject → Int × σ
  | none => (0, s)
  | some o => match Run.resolve src s o with
    | (.int i, s) => (i, s)
    | (v, s) => match Run.numOf v with
      | some x => (x.raw / 1000000 + (if x.raw < 0 ∧ x.raw % 1000000 ≠ 0 then 1 else 0), s)
      | none => (0, s)

/-- A stream dictionary for a synthesised appearance with `/BBox` `r` and resources `res`. -/
def synthDict (r : RBox) (res : Dict) : Dict :=
  [(nm "Type", .name (nm "XObject")), (nm "Subtype", .name (nm "Form")),
   (nm "BBox", .array ([r.x0, r.y0, r.x1, r.y1].map fun q => Run.fixedObj (fixOfRat q)))] ++
  (if res.isEmpty then [] else [(nm "Resources", .dict res)])

/-- **Synthesise a normal appearance** for annotation dictionary `ad` of subtype `sub` with
`/Rect` `orect` (see the section doc): the new rectangle, the form's `/BBox` (= the rectangle
except for Caret and icons) and the content stream; `none` for a subtype not synthesised, or an
empty result rectangle. `acroDA`: the catalog's `/AcroForm /DA` (`OCDesc.acroDA`). -/
def synthesize {σ : Type} (src : Source σ) (s : σ) (ad : Dict) (sub : Name) (orect : RBox)
    (acroDA : List UInt8 := []) :
    Option (RBox × RBox × Stream) × σ :=
  let (st, s) := styleOf src s ad
  let (gs, res) := opacityRes false st.ca
  let quads := fun (s : σ) =>
    let (qp, s) := arrOf src s (Dict.get? ad (nm "QuadPoints"))
    let (qp, s) := realsOf src s (qp.getD [])
    (quadsOf qp, s)
  -- `/BE /S /C` → the intensity `/I` (task 8.3e), else 0
  let cloudOf := fun (s : σ) => match resolveOpt src s (Dict.get? ad (nm "BE")) with
    | (.dict be, s) => match nameOf src s (Dict.get? be (nm "S")) with
      | (some n, s) => if n = nm "C" then realOf src s ((Dict.get? be (nm "I")).getD .null)
          else (0, s)
      | (none, s) => (0, s)
    | (_, s) => ((0 : Rat), s)
  let le := fun (s : σ) => match arrOf src s (Dict.get? ad (nm "LE")) with
    | (some xs, s) => (xs, s)
    | (none, s) => ([], s)
  let out : Option (String × Dict × OBox × Option RBox) × σ :=
    if sub = nm "Square" ∨ sub = nm "Circle" then
      let (rd, s) := arrOf src s (Dict.get? ad (nm "RD"))
      let (rd, s) := realsOf src s ((rd.getD []).take 4)
      let (cloud, s) := cloudOf s
      let (c, r) := boxAp (sub = nm "Circle") st orect rd cloud
      (some (gs ++ c, res, r, none), s)
    else if sub = nm "Line" then
      let (l, s) := arrOf src s (Dict.get? ad (nm "L"))
      let (l, s) := realsOf src s ((l.getD []).take 4)
      let (ll, s) := realOpt src s (Dict.get? ad (nm "LL"))
      let (lle, s) := realOpt src s (Dict.get? ad (nm "LLE"))
      let (llo, s) := realOpt src s (Dict.get? ad (nm "LLO"))
      let (e, s) := le s
      let (cap, s) := resolveOpt src s (Dict.get? ad (nm "Cap"))
      if cap == .bool true then
        let (contents, s) := strOf src s (Dict.get? ad (nm "Contents"))
        let (cp, s) := nameOf src s (Dict.get? ad (nm "CP"))
        let (co, s) := arrOf src s (Dict.get? ad (nm "CO"))
        let (co, s) := realsOf src s ((co.getD []).take 2)
        let f := captionStr ((textOf contents).take maxSynthText) (cp = some (nm "Top"))
          (nth co 0) (nth co 1)
        let (c, r) := lineAp st l (ll.getD 0) (lle.getD 0) (llo.getD 0) e (some f)
        (some (gs ++ c, res ++ [(nm "Font", .dict [(nm "Helv", stdFontDict "Helvetica")])], r,
          none), s)
      else
      let (c, r) := lineAp st l (ll.getD 0) (lle.getD 0) (llo.getD 0) e
      (some (gs ++ c, res, r, none), s)
    else if sub = nm "Ink" then
      let (il, s) := arrOf src s (Dict.get? ad (nm "InkList"))
      let (strokes, s) := (il.getD []).foldl (fun (acc : List (List Rat) × σ) o =>
        let (xs, s) := arrOf src acc.2 (some o)
        let (xs, s) := realsOf src s (xs.getD [])
        (xs :: acc.1, s)) ([], s)
      let (c, r) := inkAp st strokes.reverse
      (some (gs ++ c, res, r, none), s)
    else if sub = nm "Highlight" then
      let (qs, s) := quads s
      let (c, res, r) := highlightAp st qs
      (some (c, res, r, none), s)
    else if sub = nm "Underline" then
      let (qs, s) := quads s
      let (c, r) := barAp (1 / 7) st qs
      (some (gs ++ c, res, r, none), s)
    else if sub = nm "StrikeOut" then
      let (qs, s) := quads s
      let (c, r) := barAp (3 / 7) st qs
      (some (gs ++ c, res, if qs.isEmpty then some orect else r, none), s)
    else if sub = nm "Squiggly" then
      let (qs, s) := quads s
      let (c, r) := squigglyAp st qs
      (some (gs ++ c, res, r, none), s)
    else if sub = nm "Polygon" ∨ sub = nm "PolyLine" then
      let (vs, s) := arrOf src s (Dict.get? ad (nm "Vertices"))
      let (vs, s) := realsOf src s (vs.getD [])
      let pairs := (List.range (vs.length / 2)).map fun k => (nth vs (2 * k), nth vs (2 * k + 1))
      let (e, s) := le s
      let (cloud, s) := cloudOf s
      let (c, r) := polyAp (sub = nm "Polygon") st pairs e cloud
      (some (gs ++ c, res, r, none), s)
    else if sub = nm "Caret" then
      let (c, r, bb) := caretAp st orect
      (some (gs ++ c, res, some r, some bb), s)
    else if sub = nm "Text" ∨ sub = nm "FileAttachment" ∨ sub = nm "Sound" then
      let (n, s) := match Dict.get? ad (nm "Name") with
        | none => (nm (if sub = nm "Text" then "Note" else if sub = nm "Sound" then "Speaker"
            else "PushPin"), s)
        | some o => match nameOf src s (some o) with
          | (some n, s) => (n, s)
          | (none, s) => (nm "", s)
      let (c, r, bb) := iconAp st n orect
      (some (gs ++ c, res, some r, some bb), s)
    else if sub = nm "FreeText" then
      let (contents, s) := strOf src s (Dict.get? ad (nm "Contents"))
      let (q, s) := intOf src s (Dict.get? ad (nm "Q"))
      let (daO, s) := inheritGet src (nm "DA") maxFieldDepth ad s
      let (daB, s) := if daO.isNone then (acroDA, s) else strOf src s daO
      let (rd, s) := arrOf src s (Dict.get? ad (nm "RD"))
      let (rd, s) := realsOf src s ((rd.getD []).take 4)
      let (rot, s) := intOf src s (Dict.get? ad (nm "Rotate"))
      let (it, s) := nameOf src s (Dict.get? ad (nm "IT"))
      let (cl, s) := if it = some (nm "FreeTextCallout") then
          match arrOf src s (Dict.get? ad (nm "CL")) with
          | (some xs, s) => realsOf src s (xs.take 7)
          | (none, s) => ([], s)
        else ([], s)
      let (leO, s) := resolveOpt src s (Dict.get? ad (nm "LE"))
      let qn := if q < 0 ∨ q > 2 then 0 else q.toNat
      -- task 8.3e: rich text when `/RC`, or `/DS` with `/Contents` (`pdf_dict_get_text_string_opt`)
      let (dsO, s) := resolveOpt src s (Dict.get? ad (nm "DS"))
      let (rcO, s) := resolveOpt src s (Dict.get? ad (nm "RC"))
      let da := parseDA daB
      let text := (textOf contents).take maxSynthText
      let (c, res, r) := match rcO, dsO with
        | .string rc, ds =>
          let dsT := match ds with | .string b => textOf b | _ => []
          freeTextAp st orect (richText true ((textOf rc).take maxSynthText)) qn da rd rot cl leO
            (some (richStyle da.size dsT))
        | _, .string ds =>
          freeTextAp st orect (richText false text) qn da rd rot cl leO
            (some (richStyle da.size (textOf ds)))
        | _, _ => freeTextAp st orect text qn da rd rot cl leO
      (some (c, res, r, none), s)
    else if sub = nm "Stamp" then
      let (name, s) := match Dict.get? ad (nm "Name") with
        | none => ("Draft", s)
        | some o => match nameOf src s (some o) with
          | (some n, s) => (String.ofList (utf8Chars n.bytes), s)
          | (none, s) => ("", s)
      let (c, res, r, bb) := stampAp st orect name
      (some (c, res, some r, some bb), s)
    else (none, s)
  match out with
  | (some (c, res, some r, bb), s) =>
    let bb := bb.getD r
    (some (r, bb, ⟨synthDict bb res, c.toUTF8⟩), s)
  | (_, s) => (none, s)

/-- First pseudo object number of synthesised appearances: above every object number a document
can have (`Limits.maxObjects` < 2²³), so the owner of a synthesised appearance's direct font
resources (`FontId.res`) never clashes with the page's (0) or a form's. -/
def synthBase : Nat := 1099511627776

/-- The pseudo object number of the synthesised appearance of `/Annots` element `idx`. -/
def synthNum (idx : Nat) : Nat := synthBase + idx

/-- Matrix A followed by the NoRotate turn when flag NoRotate is set and the page is rotated
(`noRotateMatrix` about the rectangle `r`'s upper-left corner); else A. -/
def noRotate (flags : Nat) (rot : Doc.Rotation) (r : RBox) (a : Matrix) : Matrix :=
  if hasFlag flags flagNoRotate && rot != .r0 then Matrix.mul a (noRotateMatrix rot r) else a

/-- Parse one annotation dictionary `ad` (object `num`, position `idx`) on a page with rotation
`rot`. -/
def parseDict {σ : Type} (src : Source σ) (s : σ) (oc : OCDesc) (rot : Doc.Rotation) (idx num : Nat) (ad : Dict) :
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
            match synthesize src s ad subtype rect oc.acroDA with
            | (none, s) => (.skip .noAppearance, s)
            | (some (r, bb, st), s) =>
              let m := if r = bb then Matrix.identity else (aOf r bb).matrix
              (.draw ⟨idx, num, subtype, r, flags, state, synthNum idx, 0, st,
                noRotate flags rot r m, widget, true⟩, s)
          | (some (n, g, st), s) =>
            let m := annotMatrix rect (Run.bboxOf st.dict) (Run.formMatrix st.dict)
            (.draw ⟨idx, num, subtype, rect, flags, state, n, g, st, noRotate flags rot rect m,
              widget, false⟩, s)

/-- Parse one `/Annots` element (`seen`: annotation object numbers already listed). -/
def parseOne {σ : Type} (src : Source σ) (s : σ) (oc : OCDesc) (rot : Doc.Rotation) (idx : Nat) (seen : List Nat)
    (o : PdfObject) : Outcome × σ :=
  match o with
  | .ref n g =>
    if seen.contains n then (.skip .duplicate, s)
    else
      match src.fetch s n g with
      | (.ok (.obj (.dict ad)), s) => parseDict src s oc rot idx n ad
      | (_, s) => (.skip .notDict, s)
  | .dict ad => parseDict src s oc rot idx 0 ad
  | _ => (.skip .notDict, s)

/-- Object number of a reference (0 otherwise). -/
def refNum : PdfObject → Nat
  | .ref n _ => n
  | _ => 0

/-- Parse the elements in order: one outcome per element. -/
def parseAll {σ : Type} (src : Source σ) (oc : OCDesc) (rot : Doc.Rotation) :
    Nat → List Nat → List PdfObject → σ → List (Nat × Outcome) × σ
  | _, _, [], s => ([], s)
  | idx, seen, o :: os, s =>
    let (r, s) := parseOne src s oc rot idx seen o
    let (rs, s) := parseAll src oc rot (idx + 1) (refNum o :: seen) os s
    ((idx, r) :: rs, s)

/-- `parseAll` gives exactly one outcome per element. -/
theorem parseAll_length {σ : Type} (src : Source σ) (oc : OCDesc) (rot : Doc.Rotation) :
    ∀ (idx : Nat) (seen : List Nat) (os : List PdfObject) (s : σ),
      (parseAll src oc rot idx seen os s).1.length = os.length
  | _, _, [], _ => rfl
  | idx, seen, o :: os, s => by
    simp only [parseAll, List.length_cons]
    rw [parseAll_length src oc rot (idx + 1) (refNum o :: seen) os]

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
def collect {σ : Type} (src : Source σ) (s : σ) (pd : Dict) (oc : OCDesc := {})
    (rot : Doc.Rotation := .r0) :
    Collected × σ :=
  let (arr, s) := match Dict.get? pd (nm "Annots") with
    | some o => Run.resolve src s o
    | none => (.null, s)
  let xs := match arr with
    | .array xs => xs
    | _ => []
  let (rs, s) := parseAll src oc rot 0 [] (xs.take maxAnnots) s
  let over := (List.range (xs.length - maxAnnots)).map fun i => (maxAnnots + i, Skip.overCap)
  ({ drawn := widgetsLast (rs.filterMap (·.2.drawable?)),
     skipped := rs.filterMap (fun (i, r) => r.skip?.map (i, ·)) ++ over }, s)

/-- **Annotation count bound**: at most `maxAnnots` annotations are drawn per page. -/
theorem collect_drawn_le {σ : Type} (src : Source σ) (s : σ) (pd : Dict) (oc : OCDesc)
    (rot : Doc.Rotation) :
    (collect src s pd oc rot).1.drawn.length ≤ maxAnnots := by
  simp only [collect]
  generalize (match Dict.get? pd (nm "Annots") with
    | some o => Run.resolve src s o
    | none => (PdfObject.null, s)) = a
  obtain ⟨arr, s1⟩ := a
  generalize (match arr with
    | .array xs => xs
    | _ => []) = xs
  have hl := parseAll_length src oc rot 0 [] (xs.take maxAnnots) s1
  generalize parseAll src oc rot 0 [] (xs.take maxAnnots) s1 = p at hl
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
    (pageFonts : Text.FontTable) (bud : Budget) (oc : OCDesc := {}) (rot : Doc.Rotation := .r0) :
    AnnotPage × σ :=
  let (c, s) := collect src s pd oc rot
  let (roots, s) := apRoots src s c.drawn
  let (fonts, s) := loadAnnotFonts limits src s pageFonts roots
  let st := runAppearances (Text.textEnv limits src fonts) bud pageRes c.drawn s ()
  (⟨st.items, fonts, roots, c, st.warnings, st.ops, st.forms, st.truncated⟩, st.s)

/-- **Bounds of `pageAnnots`**: at most `maxAnnots` annotations drawn, at most `bud.ops`
operators and `Paint.maxItems · bud.ops` items. -/
theorem pageAnnots_bounds {σ : Type} (limits : Limits) (src : Source σ) (s : σ) (pd pageRes : Dict)
    (pageFonts : Text.FontTable) (bud : Budget) (oc : OCDesc) (rot : Doc.Rotation) :
    (pageAnnots limits src s pd pageRes pageFonts bud oc rot).1.collected.drawn.length ≤ maxAnnots ∧
    (pageAnnots limits src s pd pageRes pageFonts bud oc rot).1.ops ≤ bud.ops ∧
    (pageAnnots limits src s pd pageRes pageFonts bud oc rot).1.items.size ≤
      Paint.maxItems * bud.ops :=
  ⟨collect_drawn_le src s pd oc rot, runAppearances_ops_le _ _ _ _ _ _,
   runAppearances_items_le _ _ _ _ _ _⟩

/-- **Annotations of a page of an opened document**, charging the decode `budget`; `pageFonts`
is the page's font table (`Text.PageText.fonts`), `bud` what is left of the page's operator
and form budgets. -/
def docAnnots (limits : Limits) (doc : Doc.Doc) (page : Doc.Page) (pageFonts : Text.FontTable)
    (bud : Budget) (budget : Filter.Budget) : AnnotPage × Filter.Budget :=
  let src := Text.docSource limits doc
  let (pd, b) := Run.dictOf src budget (.ref page.num page.gen)
  let (oc, b) := readOC src b doc.catalog
  pageAnnots limits src b pd (page.resources.getD []) pageFonts bud oc page.rotate

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
    (page.resources.getD []) pt.fonts (Budget.after limits pt) oc page.rotate).2.1
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
-- task 8.3d: `/DA` parsing, `strtof` prefixes, text strings, Windows-1252, line breaking
#guard (parseDA "/Helv 0 Tf 0 0 1 rg".toUTF8.toList).size == 0 &&
  (parseDA "/Helv 0 Tf 0 0 1 rg".toUTF8.toList).color == [0, 0, 1]
#guard (parseDA "/Foo 9 Tf".toUTF8.toList).font == "Helv" &&
  (parseDA "/Cour 9 Tf".toUTF8.toList).font == "Cour" && (parseDA []).size == 12
#guard strtof "1.5".toList == (3 / 2, true) && strtof "-2x".toList == (-2, false) &&
  strtof "x".toList == (0, false)
#guard textOf [0xFE, 0xFF, 0, 65, 0x20, 0xAC] == ['A', '€'] && textOf [65, 66] == ['A', 'B']
#guard win1252 '€' == some 0x80 && win1252 'é' == some 0xE9 && win1252 'Ω' == none
#guard breakLine (fun _ => 1 / 2) 10 12 "ab cd".toList 0 0 none == (3, 10)
#guard (layoutLines (fun _ => 1 / 2) 10 100 5 "a\nb".toList).map (·.1) == [['a'], ['b']]
#guard litStr ['(', 'é'] == "(\\(\\351)"
#guard (boxAp false { ca := 1, c := [1, 0, 0], ic := [], lw := 3, dash := [] }
  (RBox.mk 20 20 80 60) []).2 == some (RBox.mk 20 20 80 60)

end SafePdf.Core.Annot
