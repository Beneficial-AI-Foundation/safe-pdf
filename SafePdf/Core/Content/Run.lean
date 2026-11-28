import SafePdf.Core.DictIndex
import SafePdf.Core.Content.Interp
import SafePdf.Core.Doc.OptionalContent

/-!
# Content runner with resources: forms, images, ExtGState, colour spaces (task 5.2b)

Plan.md §6 Phase 5 ("XObjects (recursion fuel proof), inline images"), §5.2 (termination:
every recursive structure carries fuel or a visited set). ISO 32000-2 references: §8.10 (form
XObjects), §8.9.5 (image XObjects), §8.9.7 (inline images), §8.4.5 (ExtGState), §8.6
(colour spaces), §7.8.3 (resource dictionaries).

## Where this layer sits

`Core.Content.Interp.exec` (task 5.2a) interprets one operator without any resources, and
`Spec.Content` (task 5.3) proves it against an inductive specification. This module wraps
`exec` **without changing it**: `stepR` intercepts the operators that need the current
resource dictionary (`Do`, `gs`, `CS`/`cs` on a resource name, `SC`/`SCN`/`sc`/`scn` in a
resolved non-device space) and delegates every other operator, unchanged, to `exec`. So
`Spec.Content` stays valid as it is: it specifies the resource-free core, and this module
adds the resource layer around it.

The document is reached only through a `Source σ` (fetch an indirect object, decode a stream),
threading a caller-chosen state `σ` (e.g. the document decode budget, or an `Open.Session`), so
the module depends on neither `Core.Open` nor `Core.Doc`. Every lookup failure is a warning,
never an error (M5: the interpreter never fails).

## Behaviour

* **Resources** (`Frame.res`): the page's `/Resources` for the page content; a form's own
  `/Resources`, or, when it has none, those of the content that invoked it (the parent's: the
  page's for a top-level form; ISO 32000-2 §7.8.3 deprecates the omission, and viewers resolve
  from the invoking content).
* **`Do` on a form** (`/Subtype /Form`, §8.10.1): the form's stream is decoded through the
  source (charged to its budget), tokenized with `Ops.tokenize`, and run nested as
  `q`, `/Matrix cm`, clip to `/BBox` (in form space; one informational `clip` item), the
  form's operators, `Q`: the invoking machine is restored *as a whole* afterwards, so nothing a
  form does (unbalanced `q`, open text object, pending `W`) leaks out. `/Ref` is ignored;
  `/OC` see "Optional content".
* **Transparency groups** (task 7.3c, §11.6.6, §8.10.3): a form with `/Group << /S /Transparency
  >>` is bracketed by `groupBegin g` … `groupEnd` instead of the informational `clip` item
  (`g` records `/I`, `/K`, the page-space `/BBox`, and the `ca`, blend mode and soft mask
  at the `Do`); inside it alpha, blend mode and soft mask restart from their initial values
  (`resetTx`). `/CS` of the group is ignored. A form adds at most two items of its own
  (`FormJob.pre_post_le`), as before.
* **Termination**: nesting is bounded by **fuel** `Limits.maxXObjectDepth` (structural
  recursion on it: `runOps`), and a form whose object number is on the current nesting path
  (`Frame.visited`) is **not** re-entered (self-reference or mutual recursion): one warning,
  no items (`doStep_form_fresh`). Beyond the fuel a form is skipped with a warning.
* **Work bound**: the runner counts every operator it executes, in page content and in forms,
  and stops executing at `Limits.maxOpsPerPage` (`St.truncated`, one warning). Hence
  `runOps_ops_le` (at most `maxOpsPerPage` operators in all) and `runOps_items_le` (at most
  `Paint.maxItems` items per executed operator), so a page has at most
  `Paint.maxItems · maxOpsPerPage` items however its forms nest (`runBytes_items_le_max`). Form
  decoding is charged to the source's budget; tokenizing is linear in the decoded bytes.
  Because a form tree without cycles can still fan out ("billion laughs"), at most
  `Env.maxForms` (default `Limits.maxFormsPerPage` = 100,000) forms are expanded per page;
  further form `Do`s are skipped with a warning.
* **Form cache** (task 7.9b): forms and soft-mask groups are read through `Env.formCode`
  (decode + tokenize, `Source.code`). `runPage` installs a per-page cache (`FormCache.env`)
  keyed by object number, generation and stream, bounded by `Limits.maxFormCacheEntries` and
  `Limits.maxFormCacheBytes`, so a form drawn many times is decoded once per page run (and
  charged to the document budget once; see the section "Per-page form cache").
  `runPageUncached` is the runner without it.
* **`Do` on an image** (`/Subtype /Image`): `DisplayItem.image (.xobject name num gen)` with the
  CTM (the unit square), the fill snapshot (stencil masks, §8.9.6.2) and the clip. The image
  data is **not** decoded (rendering is phase 7); its dictionary is summarised by consumers.
  `/Subtype /PS` is ignored silently (§8.8.2); a missing or malformed XObject is a warning.
* **Inline images** are executed by `exec` (an `.inline dict data` item); `Ops.tokenize` has
  already expanded the dictionary's abbreviations and sliced the data.
* **Font identity** (`Tf`, task 6.7a): `exec` sets the font by resource name; the runner then
  resolves that name in the current frame's `/Font` resources and records the font *object*
  in `FontRef.id`: `.ref num gen` when the entry is an indirect reference, else `.res owner`
  (the entry of that name in the resources of `Frame.owner`: 0 for the page, the form's object
  number for a form with its own `/Resources`). So a form's `/F1` and the page's `/F1` are
  different fonts, and a font set before a form is invoked keeps its identity inside it.
* **`gs`** (§8.4.5, Table 57): `/LW`, `/LC`, `/LJ`, `/ML`, `/D`, `/RI`, `/CA`, `/ca` are
  applied to the graphics state (what the display list carries); `/Font [ref size]` sets the
  font (`FontId.ref`, empty resource name) and size (a direct font dictionary there is skipped
  with a warning). `/BM` (task 7.3c): a name or an array of names, the first recognised one
  wins, unknown means `Normal`. `/SMask` (task 7.3c, §11.6.5): `/None` clears the soft mask; a
  dictionary `<< /S /Luminosity|/Alpha /G form /BC [...] >>` has its group `/G` run like a
  form (same nesting fuel, visited path and form budget; in the coordinates at the `gs`;
  `resetTx` state) into a separate list, wrapped as one `softMask id info items` item (`id` =
  the operator count at the `gs`, unique per page) and the state's `softMask` becomes
  `some id` (`gsR`; `gsR_good`: the wrapper counts as the `gs`'s one item, the group's items
  are counted by its nested run, so every item bound below still holds). A mask that cannot be
  expanded is a warning and clears the mask. `/TR` is ignored. Ignored, documented: `/AIS`, `/TK`, `/OP`, `/op`, `/OPM`, `/BG`,
  `/BG2`, `/UCR`, `/UCR2`, `/TR`, `/TR2`, `/HT`, `/FL`, `/SM`, `/SA`, `/UseBlackPtComp`,
  `/HTO`, `/Type`. A malformed value of an applied key is skipped with a warning; a missing
  ExtGState is a warning.
* **Named colour spaces** (`CS`/`cs` with a `/ColorSpace` resource, §8.6): `ICCBased` (by
  `/Alternate` when it is a device space with `/N` components, else by `/N`), `CalGray`,
  `CalRGB` and device names become `ColorSpace.device` (so `exec` handles `sc`); `Pattern`
  (with or without an underlying space) becomes `.pattern`; `Indexed`, `Separation`,
  `DeviceN` and `Lab` become `ColorSpace.other key n alt` with the **resource name** `key`,
  the operand count `n` (1, 1, number of colorants, 3) and the device space colours are held
  in. `SC`/`SCN`/`sc`/`scn` in such a space take exactly the last `n` numeric operands
  (fewer: warning, skipped) and compute the colour (`CSInfo.color`): `Indexed` looks the index
  up in the table (string or stream); `Separation` evaluates a type 2 (exponential) tint
  transform with integral exponent; other tint transforms (types 0, 3, 4) and `DeviceN` use a
  documented placeholder (tint `t` → `1 - t` gray, or `(0, 0, 0, t)` CMYK, in the alternate
  space); `Lab` shows `L*/100` as gray. Initial colours follow §8.6: index 0, tint 1, `L* = 0`;
  an `ICCBased` space with 4 components starts at `(0, 0, 0, 0)`. An unresolvable resource
  name keeps 5.2a's behaviour (`.other name 0 .gray`) and adds a warning.
* **`BDC` property lists** (task 6.8d, §14.6.2): a `/Properties` resource name is looked up in
  the current frame and handed to `exec` as an inline dictionary (`bdcStep`, `bdcProps`; an
  indirect `/ActualText` value is fetched), so `exec`'s `/ActualText` handling sees both forms.
* **Optional content** (task 9.r11a, ISO 32000-2 §8.11.3, `Doc.OptionalContent`): the
  environment carries a visibility state (`Env.oc`; default: no groups, nothing hidden). The
  runner tracks marked-content nesting per content stream in `Machine.oc` (`ocTrack`: every
  `BMC`/`BDC` opens a sequence so `EMC`s match, an unbalanced `EMC` is ignored; a
  `BDC /OC /name` whose `/Properties` entry is hidden (`bdcVisible`) hides everything up to its
  `EMC`, nested sequences included). While hidden, operators still execute (graphics state,
  text position, `gs` soft masks: §8.11.3.2 hides painting only), but their items are dropped
  (`ocKeep`), and `Do` draws nothing (no form expanded, no image); a form or image XObject
  whose `/OC` is hidden (`dictVisible`) is skipped too. Annotations with `/OC`: `Annot`. With no
  groups in the state the runner never hides anything (`runOps_oc_visible`, `ocKeep_visible`,
  `dictVisible_inactive`).
* **Resource annotation** (task 7.3f): every item a step emits is annotated in the current
  frame (`annotItem`), so consumers resolve resources without the page's resources: an `sh`
  records its `ResRef` (`resRefOf`: the indirect object, or the owner form `num gen` of a
  direct entry, or `.page`); a pattern colour in a fill/stroke snapshot (fills, strokes, glyph
  runs, stencil images) records a `PatternUse` — its `ResRef`, the frame's **base matrix**
  (`Frame.base`: identity for the page, the form's start CTM `/Matrix × CTM` for a form or
  soft-mask group, §8.7.3) and, for uncoloured patterns, the underlying colour of the last
  `SCN`/`scn` (`patBook`: computed in the underlying space of a named `[/Pattern base]` space,
  else by operand count; kept in `Machine.patFill`/`patStroke`, not saved by `q`/`Q`, matched
  by pattern name); an inline image's resource-name `/ColorSpace` is replaced by its
  definition in the current frame, as a direct object (`CSInfo.toObj`). Consumers look a
  `ResRef` up with `resLookup`. Annotation keeps the item count (`annotAll_length`).
-/

namespace SafePdf.Core.Content

open SafePdf
open Interp

/-- How the runner reaches the document: fetch an indirect object, and decode a fetched stream
to bytes (its filters applied; an image codec is an error), threading a state `σ` (a budget,
a session). -/
structure Source (σ : Type) where
  /-- Fetch object `num gen`. -/
  fetch : σ → Nat → Nat → (Except Error IndirectBody) × σ
  /-- Decode stream object `num` (already fetched). -/
  decode : σ → Nat → Stream → (Except Error ByteArray) × σ

/-- A source with no objects that leaves its caller's state untouched. -/
def Source.emptyState {σ : Type} : Source σ :=
  ⟨fun s _ _ => (.error (.malformed 0 "no document"), s),
   fun s _ _ => (.error (.malformed 0 "no document"), s)⟩

/-- A source with no objects (resource-free runs and tests). -/
def Source.empty : Source Unit := Source.emptyState

/-- A form's content (task 7.9b): stream object `num` decoded through the source and
tokenized with `Ops.tokenize lim`. The runner's default way to read a form or soft-mask group
(`Env.formCode`). -/
def Source.code {σ : Type} (src : Source σ) (lim : Limits) (s : σ) (num _gen : Nat) (st : Stream) :
    (Except Error TokResult) × σ :=
  match src.decode s num st with
  | (.ok bytes, s) => (.ok (Ops.tokenize lim bytes), s)
  | (.error e, s) => (.error e, s)

/-- The runner's environment: interpreter configuration, document source, and an observer
called once per executed operator with its warning and unknown-operator counts (the `ops`
view's histogram; `fun w _ _ _ => w` when unused). -/
structure Env (σ ω : Type) where
  /-- Interpreter configuration (limits, glyph advance). -/
  cfg : Config
  /-- Document access. -/
  src : Source σ
  /-- Per-operator observer. -/
  observe : ω → Op → Nat → Nat → ω
  /-- Maximum number of form expansions per page, by default `Limits.maxFormsPerPage` of
  `cfg.limits`. Without it a form tree without cycles, within the nesting fuel, that invokes
  each child many times ("billion laughs": 16 children over 8 levels) runs until
  `maxOpsPerPage` operators, i.e. millions of form decodes (≈ 30 s). With it the run stops
  expanding after `maxForms` forms (each further form `Do` is skipped with a warning). -/
  maxForms : Nat := cfg.limits.maxFormsPerPage
  /-- How the content of a form or soft-mask group `num gen` (stream already fetched) is read:
  decoded and tokenized, threading the source state (task 7.9b). By default `Source.code`
  (decode through `src`, then `Ops.tokenize`); `runPage` installs the per-page cache
  (`FormCache.env`) over that default. -/
  formCode : σ → Nat → Nat → Stream → (Except Error TokResult) × σ := src.code cfg.limits
  /-- The optional content visibility state (task 9.r11a, `Doc.OptionalContent.State`): the
  document's groups and those that are OFF. Content hidden by it is not painted and not
  extracted. The default (no groups) shows everything, as before optional content existed. -/
  oc : Doc.OptionalContent.State := {}

/-- The resource context of the content being run. -/
structure Frame where
  /-- The current resource dictionary. -/
  res : Dict
  /-- Object numbers of the forms on the current nesting path (innermost first). -/
  visited : List Nat
  /-- Whose resources `res` are: 0 for the page, else the object number of the form whose own
  `/Resources` they are (a form without them inherits its parent's owner). Identifies direct
  font dictionaries (`FontId.res`). -/
  owner : Nat
  /-- Generation number of the owner form (`0` for the page; task 7.3f, `ResRef.form`). -/
  ownerGen : Nat
  /-- Base matrix (task 7.3f): the CTM at the start of the content being run, i.e. its
  default coordinate space → page space (the identity for the page; a form's `/Matrix` × the
  CTM at its `Do`). Pattern colours record it (`PatternUse.base`, §8.7.3). -/
  base : Matrix
  /-- The ordered index of `res` (task 13.24): built on the first lookup and reused by every
  later lookup in this frame, so `n` resource lookups into an `n`-entry dictionary cost
  `O(n log n)` in all, not `O(n²)`. `ResIdx` carries the proof that lookups through it equal
  `Dict.lookup res`; frames are built with `Frame.mk'`. -/
  idx : ResIdx res

/-- A frame with the index of its resources. -/
def Frame.mk' (res : Dict) (visited : List Nat) (owner ownerGen : Nat) (base : Matrix) : Frame :=
  ⟨res, visited, owner, ownerGen, base, ResIdx.of res⟩

/-- Runner state. -/
structure St (σ ω : Type) where
  /-- Interpreter machine of the content being run. -/
  m : Machine
  /-- Display list so far. -/
  items : DisplayList
  /-- Warnings (interpreter, resource resolution, form tokenizing). -/
  warnings : Nat
  /-- Unknown-operator count. -/
  unsupported : Nat
  /-- Operators executed (page and forms). -/
  ops : Nat
  /-- Forms expanded. -/
  forms : Nat
  /-- Execution stopped at `Limits.maxOpsPerPage`. -/
  truncated : Bool
  /-- Source state. -/
  s : σ
  /-- Observer state. -/
  obs : ω

namespace Run

/-- A name from a string. -/
def nm (s : String) : Name := Name.ofString s

/-! ## Resolving objects -/

/-- Resolve a reference one level; a stream stands for its dictionary; a failed fetch is
`null`. -/
def resolve {σ : Type} (src : Source σ) (s : σ) : PdfObject → PdfObject × σ
  | .ref n g =>
    match src.fetch s n g with
    | (.ok (.obj o), s') => (o, s')
    | (.ok (.stream st), s') => (.dict st.dict, s')
    | (.error _, s') => (.null, s')
  | o => (o, s)

/-- A dictionary (resolved one level), or `[]`. -/
def dictOf {σ : Type} (src : Source σ) (s : σ) (o : PdfObject) : Dict × σ :=
  match resolve src s o with
  | (.dict d, s') => (d, s')
  | (_, s') => ([], s')

/-- The raw entry `name` of resource category `cat` (e.g. `XObject`) in `res`. -/
def resEntry {σ : Type} (src : Source σ) (s : σ) (res : Dict) (cat : String) (name : Name) :
    Option PdfObject × σ :=
  match Dict.get? res (nm cat) with
  | none => (none, s)
  | some o =>
    let (sub, s) := dictOf src s o
    (Dict.get? sub name, s)

/-- `resEntry` through the ordered index of `res` (task 13.24): the top level and a direct
category dictionary are looked up in `O(log n)`; a category given by reference is resolved
through the source and scanned, as in `resEntry`. -/
def resEntryI {σ : Type} (src : Source σ) (s : σ) (res : Dict) (ix : ResIdx res) (cat : String)
    (name : Name) : Option PdfObject × σ :=
  match ix.top.get[(nm cat).bytes]? with
  | none => (none, s)
  | some e =>
    match e.val with
    | .null => (none, s)
    | .dict _ => (Dict.getIdx e.sub.get name, s)
    | o =>
      let (sub, s) := dictOf src s o
      (Dict.get? sub name, s)

/-- **`resEntryI` is `resEntry`**, for every resource dictionary (duplicate keys included:
both take the first entry). -/
theorem resEntryI_eq {σ : Type} (src : Source σ) (s : σ) (res : Dict) (ix : ResIdx res)
    (cat : String) (name : Name) :
    resEntryI src s res ix cat name = resEntry src s res cat name := by
  have h := ix.htop (nm cat)
  unfold resEntryI resEntry Dict.get?
  cases he : ix.top.get[(nm cat).bytes]? with
  | none => rw [he] at h; simp at h; rw [← h]
  | some e =>
    rw [he] at h
    simp only [Option.map_some] at h
    rw [← h]
    obtain ⟨v, sub, hs⟩ := e
    simp only
    cases v with
    | dict d =>
      simp only [dictOf, resolve]
      rw [hs d rfl, Dict.getIdx_index]
      rfl
    | _ => simp [dictOf, resolve]

/-- A number. -/
def numOf (o : PdfObject) : Option Fixed := num? o

/-- A list of numbers. -/
def numsOf : PdfObject → Option (List Fixed)
  | .array xs => xs.mapM num?
  | _ => none

/-! ## XObjects -/

/-- What a `Do` operand names. -/
inductive XObj where
  /-- A form XObject: object number, generation, the stream. -/
  | form (num gen : Nat) (st : Stream)
  /-- An image XObject. -/
  | image (num gen : Nat) (dict : Dict)
  /-- A PostScript XObject (ignored, §8.8.2). -/
  | ignored
  /-- Not found, not a stream, or an unknown subtype. -/
  | missing

/-- Look up and classify XObject `name`. -/
def xobjectOf {σ : Type} (src : Source σ) (s : σ) (res : Dict) (ix : ResIdx res) (name : Name) :
    XObj × σ :=
  match resEntryI src s res ix "XObject" name with
  | (some (.ref n g), s) =>
    match src.fetch s n g with
    | (.ok (.stream st), s) =>
      match Dict.get? st.dict (nm "Subtype") with
      | some (.name t) =>
        if t = nm "Form" then (.form n g st, s)
        else if t = nm "Image" then (.image n g st.dict, s)
        else if t = nm "PS" then (.ignored, s)
        else (.missing, s)
      | _ => (.missing, s)
    | (_, s) => (.missing, s)
  | (_, s) => (.missing, s)

/-- A form's `/Matrix` (identity when absent or malformed). -/
def formMatrix (d : Dict) : Matrix :=
  match (Dict.get? d (nm "Matrix")).bind numsOf with
  | some [a, b, c, d', e, f] => ⟨a, b, c, d', e, f⟩
  | _ => Matrix.identity

/-- A form's `/BBox` corners. -/
def bboxOf (d : Dict) : Option (Fixed × Fixed × Fixed × Fixed) :=
  match (Dict.get? d (nm "BBox")).bind numsOf with
  | some [x0, y0, x1, y1] => some (x0, y0, x1, y1)
  | _ => none

/-- The closed rectangle `(x0,y0) (x1,y0) (x1,y1) (x0,y1)` mapped by `m`. -/
def rectPath (m : Matrix) (x0 y0 x1 y1 : Fixed) : Path :=
  let p := fun x y => Matrix.apply m ⟨x, y⟩
  ⟨#[.moveTo (p x0 y0), .lineTo (p x1 y0), .lineTo (p x1 y1), .lineTo (p x0 y1), .closePath]⟩

/-- A form's resources and their owner (`Frame.owner`): its own `/Resources` (owner: the
form's object number `num`), else the parent's (`parent`, owner `owner`). -/
def formResources {σ : Type} (src : Source σ) (s : σ) (d : Dict) (parent : Dict) (owner num : Nat) :
    (Dict × Nat) × σ :=
  match Dict.get? d (nm "Resources") with
  | none => ((parent, owner), s)
  | some o =>
    match resolve src s o with
    | (.dict r, s) => ((r, num), s)
    | (_, s) => ((parent, owner), s)

/-! ## ExtGState (§8.4.5) -/

/-- A `/BM` value (§11.6.3): a name, or an array of names of which the first recognised one
is used; an unknown name, or an array with none recognised, means `Normal`. -/
def blendOf : PdfObject → Option BlendMode
  | .name n => some ((BlendMode.ofName? n).getD .normal)
  | .array xs => some ((xs.findSome? fun o => match o with
      | .name n => BlendMode.ofName? n
      | _ => none).getD .normal)
  | _ => none

/-- Apply one ExtGState entry (value resolved): new state and warnings. -/
def gsEntry (g : GState) (k : Name) (v : PdfObject) : GState × Nat :=
  if k = nm "LW" then
    match num? v with
    | some x => ({ g with line := { g.line with width := x } }, 0)
    | none => (g, 1)
  else if k = nm "LC" then
    match (nat? v).bind LineCap.ofNat? with
    | some c => ({ g with line := { g.line with cap := c } }, 0)
    | none => (g, 1)
  else if k = nm "LJ" then
    match (nat? v).bind LineJoin.ofNat? with
    | some j => ({ g with line := { g.line with join := j } }, 0)
    | none => (g, 1)
  else if k = nm "ML" then
    match num? v with
    | some x => ({ g with line := { g.line with miterLimit := x } }, 0)
    | none => (g, 1)
  else if k = nm "D" then
    match v with
    | .array [arr, ph] =>
      match numsOf arr, num? ph with
      | some a, some p => ({ g with line := { g.line with dash := ⟨a, p⟩ } }, 0)
      | _, _ => (g, 1)
    | _ => (g, 1)
  else if k = nm "RI" then
    match v with
    | .name n => ({ g with renderingIntent := n }, 0)
    | _ => (g, 1)
  else if k = nm "CA" then
    match num? v with
    | some x => ({ g with strokeAlpha := Comp.ofFixed x }, 0)
    | none => (g, 1)
  else if k = nm "ca" then
    match num? v with
    | some x => ({ g with fillAlpha := Comp.ofFixed x }, 0)
    | none => (g, 1)
  else if k = nm "Font" then
    match v with
    | .array [.ref n gen, sz] =>
      match num? sz with
      | some x =>
        ({ g with text := { g.text with font := some { name := ⟨[]⟩, size := x, id := .ref n gen } } },
          0)
      | none => (g, 1)
    | _ => (g, 1)
  else if k = nm "BM" then
    match blendOf v with
    | some b => ({ g with blendMode := b }, 0)
    | none => (g, 1)
  else if k = nm "SMask" then
    -- `/None` clears the mask; a dictionary clears it too here: `stepR` sets the new mask
    -- after expanding its group (`gsR`).
    match v with
    | .name _ | .dict _ => ({ g with softMask := none }, 0)
    | _ => ({ g with softMask := none }, 1)
  else (g, 0)

/-- Keys `gsEntry` applies (others are ignored without resolving their values). -/
def gsKeys : List String :=
  ["LW", "LC", "LJ", "ML", "D", "RI", "CA", "ca", "Font", "BM", "SMask"]

/-- Apply an ExtGState dictionary: new state, warnings, source state. -/
def applyExtGState {σ : Type} (src : Source σ) (s : σ) (d : Dict) (g : GState) :
    GState × Nat × σ :=
  d.foldl (fun (acc : GState × Nat × σ) (kv : Name × PdfObject) =>
    if gsKeys.any (fun k => nm k = kv.1) then
      let (v, s') := resolve src acc.2.2 kv.2
      let (g', w) := gsEntry acc.1 kv.1 v
      (g', acc.2.1 + w, s')
    else acc) (g, 0, s)

/-! ## Colour spaces (§8.6) -/

/-- A type 2 (exponential) function `C0 + tᴺ (C1 − C0)` with integral `N` (§7.10.3). -/
structure Exp where
  /-- `C0`. -/
  c0 : List Fixed
  /-- `C1`. -/
  c1 : List Fixed
  /-- `N`. -/
  n : Nat

/-- A resolved colour space. -/
inductive CSInfo where
  /-- A device space (also `ICCBased`, `CalGray`, `CalRGB`) and its initial colour. -/
  | dev (s : DeviceSpace) (init : Color)
  /-- `Pattern`. -/
  | pattern
  /-- `Indexed`: base space, `hival`, lookup table. -/
  | indexed (base : DeviceSpace) (hival : Nat) (lookup : ByteArray)
  /-- `Separation`: alternate space and the tint transform if it is a type 2 function. -/
  | separation (alt : DeviceSpace) (fn : Option Exp)
  /-- `DeviceN`: number of colorants, alternate space. -/
  | deviceN (n : Nat) (alt : DeviceSpace)
  /-- `Lab`. -/
  | lab

/-- A device space by name (including the inline abbreviations). -/
def deviceOfName (n : Name) : Option DeviceSpace :=
  if n = nm "DeviceGray" || n = nm "G" then some .gray
  else if n = nm "DeviceRGB" || n = nm "RGB" then some .rgb
  else if n = nm "DeviceCMYK" || n = nm "CMYK" then some .cmyk
  else none

/-- The device space of an `ICCBased` stream dictionary: `/Alternate` when it is a device
space with `/N` components, else by `/N` (1, 3, 4). -/
def iccDevice (d : Dict) : Option DeviceSpace :=
  let byN : Option DeviceSpace :=
    match Dict.get? d (nm "N") with
    | some (.int 1) => some .gray
    | some (.int 3) => some .rgb
    | some (.int 4) => some .cmyk
    | _ => none
  match Dict.get? d (nm "Alternate"), byN with
  | some (.name a), some s =>
    match deviceOfName a with
    | some t => if t.nComps = s.nComps then some t else some s
    | none => some s
  | _, b => b

/-- Device alternate for an ICC profile, including indirect N and Alternate entries. -/
private def profileDevice {σ : Type} (src : Source σ) (s : σ) (profile : PdfObject) :
    Option DeviceSpace × σ :=
  let (d, s) := dictOf src s profile
  let (n, s) := resolve src s ((Dict.get? d (nm "N")).getD .null)
  let (alt, s) := resolve src s ((Dict.get? d (nm "Alternate")).getD .null)
  (iccDevice [(nm "N", n), (nm "Alternate", alt)], s)

/-- A base or alternate space that must be a device space after fallback (`ICCBased`,
`CalGray`, `CalRGB`, device names, one-element arrays). -/
def baseDevice {σ : Type} (src : Source σ) (s : σ) (o : PdfObject) : Option DeviceSpace × σ :=
  match resolve src s o with
  | (.name n, s) => (deviceOfName n, s)
  | (.array [.name n], s) => (deviceOfName n, s)
  | (.array [.name f, a], s) =>
    if f = nm "ICCBased" then
      profileDevice src s a
    else if f = nm "CalGray" then (some .gray, s)
    else if f = nm "CalRGB" then (some .rgb, s)
    else (none, s)
  | (_, s) => (none, s)

/-- A type 2 function, if `o` is one with an integral exponent ≤ 64. -/
def exp? {σ : Type} (src : Source σ) (s : σ) (o : PdfObject) : Option Exp × σ :=
  let (d, s) := dictOf src s o
  let ty := Dict.get? d (nm "FunctionType")
  let c0 := ((Dict.get? d (nm "C0")).bind numsOf).getD [Fixed.zero]
  let c1 := ((Dict.get? d (nm "C1")).bind numsOf).getD [Fixed.one]
  let n : Option Nat := match Dict.get? d (nm "N") with
    | some (.int k) => if 0 ≤ k ∧ k ≤ 64 then some k.toNat else none
    | some o =>
      match num? o with
      | some x => if x.raw % fixedScale = 0 ∧ 0 ≤ x.raw ∧ x.raw ≤ 64 * fixedScale then
          some (x.raw / fixedScale).toNat else none
      | none => none
    | none => none
  match ty, n with
  | some (.int 2), some k => if c0.length = c1.length then (some ⟨c0, c1, k⟩, s) else (none, s)
  | _, _ => (none, s)

/-- The bytes of an `Indexed` lookup table (string, or stream decoded through the source). -/
def lookupBytes {σ : Type} (src : Source σ) (s : σ) : PdfObject → Option ByteArray × σ
  | .string b => (some ⟨b.toArray⟩, s)
  | .ref n g =>
    match src.fetch s n g with
    | (.ok (.obj (.string b)), s) => (some ⟨b.toArray⟩, s)
    | (.ok (.stream st), s) =>
      match src.decode s n st with
      | (.ok b, s) => (some b, s)
      | (.error _, s) => (none, s)
    | (_, s) => (none, s)
  | _ => (none, s)

/-- Resolve a colour-space object (a `/ColorSpace` resource value). -/
def csInfo {σ : Type} (src : Source σ) (s : σ) (o : PdfObject) : Option CSInfo × σ :=
  match resolve src s o with
  | (.name n, s) =>
    if n = nm "Pattern" then (some .pattern, s)
    else ((deviceOfName n).map fun d => .dev d d.initialColor, s)
  | (.array (.name f :: args), s) =>
    if f = nm "Pattern" then (some .pattern, s)
    else if f = nm "Lab" then (some .lab, s)
    else if f = nm "Indexed" then
      match args with
      | [base, hv, lut] =>
        match baseDevice src s base with
        | (some b, s) =>
          match resolve src s hv with
          | (.int h, s) =>
            if 0 ≤ h then
              match lookupBytes src s lut with
              | (some bytes, s) => (some (.indexed b h.toNat bytes), s)
              | (none, s) => (none, s)
            else (none, s)
          | (_, s) => (none, s)
        | (none, s) => (none, s)
      | _ => (none, s)
    else if f = nm "Separation" then
      match args with
      | [_, alt, tint] =>
        let (a, s) := baseDevice src s alt
        let (e, s) := exp? src s tint
        (some (.separation (a.getD .gray) e), s)
      | _ => (none, s)
    else if f = nm "DeviceN" then
      match args with
      | names :: alt :: _ =>
        let (ns, s) := resolve src s names
        let (a, s) := baseDevice src s alt
        match ns with
        | .array xs => if xs.isEmpty then (none, s) else (some (.deviceN xs.length (a.getD .gray)), s)
        | _ => (none, s)
      | _ => (none, s)
    else if f = nm "ICCBased" then
      match args with
      | [a] =>
        let (space, s) := profileDevice src s a
        match space with
        | some .cmyk => (some (.dev .cmyk (.cmyk Comp.zero Comp.zero Comp.zero Comp.zero)), s)
        | some t => (some (.dev t t.initialColor), s)
        | none => (none, s)
      | _ => (none, s)
    else
      match baseDevice src s (.array (.name f :: args)) with
      | (some d, s) => (some (.dev d d.initialColor), s)
      | (none, s) => (none, s)
  | (_, s) => (none, s)

/-- The interpreter's colour space for a resolved space named `key`. -/
def CSInfo.space (key : Name) : CSInfo → ColorSpace
  | .dev d _ => .device d
  | .pattern => .pattern
  | .indexed b _ _ => .other key 1 b
  | .separation a _ => .other key 1 a
  | .deviceN n a => .other key n a
  | .lab => .other key 3 .rgb

/-- A byte as a component (`b / 255`). -/
def byteComp (b : UInt8) : Comp := Comp.ofFixed (Fixed.div (Fixed.ofInt b.toNat) (Fixed.ofInt 255))

/-- Placeholder colour of tint `t` in a device space: `1 − t` gray, or `(0, 0, 0, t)`. -/
def darkness (alt : DeviceSpace) (t : Fixed) : Color :=
  let c := Comp.ofFixed t
  let w := Comp.ofFixed (Fixed.sub Fixed.one c.toFixed)
  match alt with
  | .gray => .gray w
  | .rgb => .rgb w w w
  | .cmyk => .cmyk Comp.zero Comp.zero Comp.zero c

/-- `x ^ n` by repeated multiplication. -/
def powN (x : Fixed) : Nat → Fixed
  | 0 => Fixed.one
  | n + 1 => Fixed.mul (powN x n) x

/-- Evaluate a type 2 function at `t` (clamped to [0, 1]). -/
def Exp.eval (e : Exp) (t : Fixed) : List Fixed :=
  let tn := powN (Comp.ofFixed t).toFixed e.n
  (e.c0.zip e.c1).map fun (a, b) => Fixed.add a (Fixed.mul tn (Fixed.sub b a))

/-- The colour of components `xs` (exactly the space's count) in a resolved space. -/
def CSInfo.color (info : CSInfo) (xs : List Fixed) : Color :=
  match info with
  | .dev d init => (deviceColor d xs).getD init
  | .pattern => .gray Comp.zero
  | .indexed b hival lut =>
    let t := (xs.head?.getD Fixed.zero).raw
    let i0 : Int := roundDiv t fixedScale
    let i : Nat := if i0 < 0 then 0 else min i0.toNat hival
    let k := b.nComps
    let comps := (List.range k).map fun j => (byteComp ((lut[i * k + j]?).getD 0)).toFixed
    (deviceColor b comps).getD b.initialColor
  | .separation a fn =>
    let t := xs.head?.getD Fixed.zero
    match fn with
    | some e =>
      match deviceColor a (e.eval t) with
      | some c => c
      | none => darkness a t
    | none => darkness a t
  | .deviceN n a =>
    let sum := xs.foldl (fun acc x => Fixed.add acc (Comp.ofFixed x).toFixed) Fixed.zero
    darkness a (Fixed.div sum (Fixed.ofInt (max n 1)))
  | .lab =>
    let l := Comp.ofFixed (Fixed.div (xs.head?.getD Fixed.zero) (Fixed.ofInt 100))
    .rgb l l l

/-- The initial colour of a resolved space (§8.6.5–8.6.6). -/
def CSInfo.initial (info : CSInfo) : Color :=
  match info with
  | .dev _ c => c
  | .pattern => .gray Comp.zero
  | .indexed .. => info.color [Fixed.zero]
  | .separation .. => info.color [Fixed.one]
  | .deviceN n _ => info.color (List.replicate n Fixed.one)
  | .lab => info.color [Fixed.zero, Fixed.zero, Fixed.zero]

/-- Resolve colour-space resource `name`. -/
def namedCS {σ : Type} (src : Source σ) (s : σ) (res : Dict) (ix : ResIdx res) (name : Name) :
    Option CSInfo × σ :=
  match resEntryI src s res ix "ColorSpace" name with
  | (some o, s) => csInfo src s o
  | (none, s) => (none, s)

/-! ## Resource annotation (task 7.3f)

Items that name resources record where those live, resolved here in the current frame, so that
the rasterizer's loaders never consult the page's resources for content of a form. -/

/-- Where resource `name` of category `cat` (`"Shading"`, `"Pattern"`) lives, seen from frame
`fr`: the referenced object when the entry is an indirect reference, else (a direct entry, or
none at all) the resources of the frame's owner (`.page` for the page, `.form` for a form
with its own `/Resources`). -/
def resRefOf {σ : Type} (src : Source σ) (s : σ) (fr : Frame) (cat : String) (name : Name) :
    ResRef × σ :=
  match resEntryI src s fr.res fr.idx cat name with
  | (some (.ref n g), s) => (.ref n g, s)
  | (_, s) => (if fr.owner = 0 then .page else .form fr.owner fr.ownerGen, s)

/-- **Look up a recorded resource** (the consumer side of `resRefOf`): resource `name` of
category `cat` where `r` says it lives — the referenced object itself, the page's resources
`pageRes`, or the own `/Resources` of form `num gen`. -/
def resLookup {σ : Type} (src : Source σ) (s : σ) (pageRes : Dict) (cat : String) (r : ResRef)
    (name : Name) : Option PdfObject × σ :=
  match r with
  | .ref n g => (some (.ref n g), s)
  | .page => resEntry src s pageRes cat name
  | .form n g =>
    match src.fetch s n g with
    | (.ok (.stream st), s) =>
      match Dict.get? st.dict (nm "Resources") with
      | some o =>
        let (d, s) := dictOf src s o
        resEntry src s d cat name
      | none => (none, s)
    | (_, s) => (none, s)

/-- The pattern use of colour `c` in frame `fr` (`none` for a non-pattern colour): where the
pattern lives, the frame's base matrix, and the underlying colour the last `SCN`/`scn` gave
this pattern (`pst.under`, kept only when its pattern name is `c`'s). -/
def patternUse {σ : Type} (src : Source σ) (s : σ) (fr : Frame) (pst : PatState) :
    Color → Option PatternUse × σ
  | .pattern n =>
    let (r, s) := resRefOf src s fr "Pattern" n
    let under := match pst.under with
      | some (n', c) => if n' = n then some c else none
      | none => none
    (some { res := r, base := fr.base, under }, s)
  | _ => (none, s)

/-- Record the pattern use in a fill snapshot. -/
def annotFill {σ : Type} (src : Source σ) (s : σ) (fr : Frame) (pst : PatState) (f : FillStyle) :
    FillStyle × σ :=
  let (p, s) := patternUse src s fr pst f.color
  ({ f with pattern := p }, s)

/-- Record the pattern use in a stroke snapshot. -/
def annotStroke {σ : Type} (src : Source σ) (s : σ) (fr : Frame) (pst : PatState)
    (f : StrokeStyle) :
    StrokeStyle × σ :=
  let (p, s) := patternUse src s fr pst f.color
  ({ f with pattern := p }, s)

/-- The name of a device space. -/
def devName : DeviceSpace → Name
  | .gray => nm "DeviceGray"
  | .rgb => nm "DeviceRGB"
  | .cmyk => nm "DeviceCMYK"

/-- A number as an object (exact: `Fixed.toDecimal`). -/
def fixedObj (x : Fixed) : PdfObject := .real x.toDecimal

/-- A **direct** colour-space object that `csInfo` resolves without any document access to
the same rendering behaviour (task 7.3f; used to inline a resource colour space into an inline
image's parameters): device names, `[/Indexed base hival (lookup)]` with the table as a
string, `[/Separation /Spot alt fn]` with a type 2 function dictionary (or `null`: the
darkness placeholder), `[/DeviceN [/C …] alt null]`, `[/Lab << >>]`. (An `ICCBased` CMYK space
becomes `/DeviceCMYK`: only its initial colour differs, which images do not use.) -/
def CSInfo.toObj : CSInfo → PdfObject
  | .dev d _ => .name (devName d)
  | .pattern => .name (nm "Pattern")
  | .indexed b hival lut =>
    .array [.name (nm "Indexed"), .name (devName b), .int hival, .string lut.data.toList]
  | .separation a fn =>
    let f : PdfObject := match fn with
      | some e => .dict [(nm "FunctionType", .int 2), (nm "Domain", .array [.int 0, .int 1]),
          (nm "C0", .array (e.c0.map fixedObj)), (nm "C1", .array (e.c1.map fixedObj)),
          (nm "N", .int e.n)]
      | none => .null
    .array [.name (nm "Separation"), .name (nm "Spot"), .name (devName a), f]
  | .deviceN n a =>
    .array [.name (nm "DeviceN"), .array (List.replicate n (.name (nm "C"))), .name (devName a),
      .null]
  | .lab => .array [.name (nm "Lab"), .dict []]

private def inlineTint (d : Dict) : PdfObject → Bool
  | .array (.name family :: _) =>
    let jpx := PdfObject.name (nm "JPXDecode")
    (family == nm "DeviceN" || family == nm "Separation") &&
      match Dict.get? d (nm "Filter") with
      | some (.array fs) => fs.getLast? == some jpx
      | f => f == some jpx
  | _ => false

/-- Replace an inline image's named colour space by its definition in the current frame
(§8.9.7). For JPX tints retain the original function reference for the document image
loader. Other spaces use the self-contained `CSInfo.toObj` rendering parameters. -/
def annotInline {σ : Type} (src : Source σ) (s : σ) (fr : Frame) (d : Dict) : Dict × σ :=
  match Dict.get? d (nm "ColorSpace") with
  | some (.name n) =>
    if (deviceOfName n).isSome || n = nm "Pattern" then (d, s) else
    match resEntryI src s fr.res fr.idx "ColorSpace" n with
    | (some entry, s) =>
      let (raw, s) := resolve src s entry
      let (space, s) := if inlineTint d raw then (some raw, s) else
        let (info, s) := csInfo src s raw
        (info.map CSInfo.toObj, s)
      match space with
      | some o => ((nm "ColorSpace", o) :: d.filter (fun kv => kv.1 != nm "ColorSpace"), s)
      | none => (d, s)
    | (none, s) => (d, s)
  | _ => (d, s)

/-- **Annotate one emitted item** with where its resources live (task 7.3f): pattern uses of
fill and stroke snapshots, the `ResRef` of an `sh`, an inline image's named colour space. -/
def annotItem {σ : Type} (src : Source σ) (fr : Frame) (pf ps : PatState) (s : σ) :
    DisplayItem → DisplayItem × σ
  | .fillPath p r f c =>
    let (f, s) := annotFill src s fr pf f
    (.fillPath p r f c, s)
  | .strokePath p k c =>
    let (k, s) := annotStroke src s fr ps k
    (.strokePath p k c, s)
  | .glyphRun r c =>
    let (f, s) := annotFill src s fr pf r.fill
    let (k, s) := annotStroke src s fr ps r.stroke
    (.glyphRun { r with fill := f, stroke := k } c, s)
  | .image (.inline d data) ctm f c =>
    let (d, s) := annotInline src s fr d
    let (f, s) := annotFill src s fr pf f
    (.image (.inline d data) ctm f c, s)
  | .image isrc ctm f c =>
    let (f, s) := annotFill src s fr pf f
    (.image isrc ctm f c, s)
  | .shading n _ ctm f c =>
    let (r, s) := resRefOf src s fr "Shading" n
    (.shading n r ctm f c, s)
  | it => (it, s)

/-- Annotate a list of emitted items. -/
def annotAll {σ : Type} (src : Source σ) (fr : Frame) (pf ps : PatState) :
    σ → List DisplayItem → List DisplayItem × σ
  | s, [] => ([], s)
  | s, it :: rest =>
    let a := annotItem src fr pf ps s it
    let r := annotAll src fr pf ps a.2 rest
    (a.1 :: r.1, r.2)

/-- Annotation keeps the number of items. -/
theorem annotAll_length {σ : Type} (src : Source σ) (fr : Frame) (pf ps : PatState) :
    ∀ (s : σ) (l : List DisplayItem), (annotAll src fr pf ps s l).1.length = l.length
  | _, [] => rfl
  | s, it :: rest => by
    simp only [annotAll, List.length_cons, annotAll_length src fr pf ps _ rest]

/-! ## Steps -/

/-- Output of a step that does not nest: machine, items, warnings, unknown-operator count,
source state. -/
abbrev Local (σ : Type) := Machine × List DisplayItem × Nat × Nat × σ

/-- Delegate to `exec`. -/
def viaExec {σ : Type} (cfg : Config) (m : Machine) (s : σ) (op : Op) : Local σ :=
  match exec cfg m op with
  | (m', its, w, u) => (m', its, w, u, s)

/-- Replace the graphics state. -/
def withGs (m : Machine) (g : GState) : Machine := { m with core := { m.core with gs := g } }

/-- `gs /Name`. -/
def gsStep {σ : Type} (src : Source σ) (fr : Frame) (m : Machine) (s : σ) (op : Op) :
    Local σ :=
  match lastName? op.operands with
  | none => (m, [], 1, 0, s)
  | some n =>
    match resEntryI src s fr.res fr.idx "ExtGState" n with
    | (some o, s) =>
      match resolve src s o with
      | (.dict d, s) =>
        let (g, w, s) := applyExtGState src s d m.core.gs
        (withGs m g, [], w, 0, s)
      | (_, s) => (m, [], 1, 0, s)
    | (none, s) => (m, [], 1, 0, s)

/-- The font object that resource name `name` denotes in frame `fr` (`FontId`): the
referenced object when the `/Font` entry is a reference, else the entry of that name in the
frame owner's resources. -/
def fontIdOf {σ : Type} (src : Source σ) (s : σ) (fr : Frame) (name : Name) : FontId × σ :=
  match resEntryI src s fr.res fr.idx "Font" name with
  | (some (.ref n g), s) => (.ref n g, s)
  | (_, s) => (.res fr.owner, s)

/-- The font name `Tf` selects (the operand pattern `exec` accepts). -/
def tfName? (o : List PdfObject) : Option Name :=
  match lastN 2 o with
  | some [.name n, sz] => (num? sz).map fun _ => n
  | _ => none

/-- Record font object `id` in the current font when it has resource name `n`. -/
def setFontId (m : Machine) (n : Name) (id : FontId) : Machine :=
  let g := m.core.gs
  withGs m { g with text := { g.text with
    font := g.text.font.map fun f => if f.name = n then { f with id } else f } }

/-- `Tf`: `exec` selects the font by name, then the name is resolved in the current frame
(`fontIdOf`). -/
def tfStep {σ ω : Type} (env : Env σ ω) (fr : Frame) (m : Machine) (s : σ) (op : Op) :
    Local σ :=
  match viaExec env.cfg m s op with
  | (m', its, w, u, s1) =>
    match tfName? op.operands with
    | some n =>
      let (id, s2) := fontIdOf env.src s1 fr n
      (setFontId m' n id, its, w, u, s2)
    | none => (m', its, w, u, s1)

/-- `CS`/`cs`: a resource name is resolved; device names and `Pattern` go to `exec`. -/
def csStep {σ ω : Type} (env : Env σ ω) (fr : Frame) (stroke : Bool) (m : Machine) (s : σ)
    (op : Op) : Local σ :=
  match lastName? op.operands with
  | some n =>
    match spaceOfName n with
    | .other .. =>
      match namedCS env.src s fr.res fr.idx n with
      | (some info, s) =>
        ({ m with core := setColor m.core stroke (info.space n) info.initial }, [], 0, 0, s)
      | (none, s) =>
        match viaExec env.cfg m s op with
        | (m', its, w, u, s) => (m', its, w + 1, u, s)
    | _ => viaExec env.cfg m s op
  | none => viaExec env.cfg m s op

/-- `SC`/`SCN`/`sc`/`scn`: in a resolved `.other` space, the last `n` numbers give the
colour; anything else goes to `exec`. -/
def scStepIn {σ ω : Type} (env : Env σ ω) (fr : Frame) (stroke : Bool) (sp : ColorSpace)
    (m : Machine) (s : σ) (op : Op) : Local σ :=
  match sp with
  | .other key k _ =>
    if k = 0 then viaExec env.cfg m s op
    else
      match namedCS env.src s fr.res fr.idx key with
      | (some info, s) =>
        if info.space key = sp then
          match nums k op.operands with
          | some xs => ({ m with core := setColor m.core stroke sp (info.color xs) }, [], 0, 0, s)
          | none => (m, [], 1, 0, s)
        else viaExec env.cfg m s op
      | (none, s) => viaExec env.cfg m s op
  | _ => viaExec env.cfg m s op

/-- `SC`/`SCN` (stroking) or `sc`/`scn` in the current space. -/
def scStep {σ ω : Type} (env : Env σ ω) (fr : Frame) (stroke : Bool) (m : Machine) (s : σ)
    (op : Op) : Local σ :=
  scStepIn env fr stroke (if stroke then m.core.gs.strokeSpace else m.core.gs.fillSpace) m s op

/-- The property list of `BDC` with its `/ActualText` resolved (task 6.8d): an inline
dictionary, or a `/Properties` resource name (ISO 32000-2 §14.6.2) looked up in the current
frame; an indirect `/ActualText` value is fetched. `none` when the operands are not
`/Tag dict-or-name` or the name is not a dictionary resource. -/
def bdcProps {σ : Type} (src : Source σ) (s : σ) (fr : Frame) (o : List PdfObject) :
    Option (Name × Dict) × σ :=
  let withText (tag : Name) (d : Dict) (s : σ) : Option (Name × Dict) × σ :=
    match Dict.get? d (nm "ActualText") with
    | some (.ref n g) =>
      let (v, s) := resolve src s (.ref n g)
      (some (tag, (nm "ActualText", v) :: d), s)
    | _ => (some (tag, d), s)
  match lastN 2 o with
  | some [.name tag, .dict d] => withText tag d s
  | some [.name tag, .name p] =>
    match resEntryI src s fr.res fr.idx "Properties" p with
    | (some e, s) =>
      match resolve src s e with
      | (.dict d, s) => withText tag d s
      | (_, s) => (none, s)
    | (none, s) => (none, s)
  | _ => (none, s)

/-- `BDC`: `exec` sees the property list as an inline dictionary (`bdcProps`), so a
`/Properties` resource carries its `/ActualText` like an inline one. -/
def bdcStep {σ ω : Type} (env : Env σ ω) (fr : Frame) (m : Machine) (s : σ) (op : Op) :
    Local σ :=
  match bdcProps env.src s fr op.operands with
  | (some (tag, d), s) => viaExec env.cfg m s { op with operands := [.name tag, .dict d] }
  | (none, s) => viaExec env.cfg m s op

/-- Every operator but `Do`. -/
def localStep {σ ω : Type} (env : Env σ ω) (fr : Frame) (m : Machine) (s : σ) (op : Op) :
    Local σ :=
  match op.op with
  | [103, 115] => gsStep env.src fr m s op          -- gs
  | [84, 102] => tfStep env fr m s op               -- Tf
  | [67, 83] => csStep env fr true m s op           -- CS
  | [99, 115] => csStep env fr false m s op         -- cs
  | [83, 67] => scStep env fr true m s op           -- SC
  | [83, 67, 78] => scStep env fr true m s op       -- SCN
  | [115, 99] => scStep env fr false m s op         -- sc
  | [115, 99, 110] => scStep env fr false m s op    -- scn
  | [66, 68, 67] => bdcStep env fr m s op           -- BDC
  | _ => viaExec env.cfg m s op

/-- A form to expand: object number, operators, tokenizer warnings, resources, the graphics
state to run it in (`/Matrix` applied, `/BBox` clip added), the `/BBox` clip path (one
informational `clip` item), warnings. -/
structure FormJob where
  /-- Object number. -/
  num : Nat
  /-- The form's operators. -/
  ops : Array Op
  /-- Tokenizer warnings. -/
  tokW : Nat
  /-- The form's resources. -/
  res : Dict
  /-- Whose resources they are (`Frame.owner`). -/
  owner : Nat
  /-- Generation number of the owner (`Frame.ownerGen`). -/
  ownerGen : Nat
  /-- Graphics state at the start of the form. -/
  gs : GState
  /-- The `/BBox` clip, page space. -/
  clip : Option Path
  /-- Warnings (a missing or malformed `/BBox`). -/
  w : Nat
  /-- The transparency group the form is, if any (task 7.3c). -/
  group : Option GroupInfo := none
  /-- Fill pattern bookkeeping at the `Do` (task 7.3f; the colour is inherited). -/
  patFill : PatState := {}
  /-- Stroke pattern bookkeeping at the `Do`. -/
  patStroke : PatState := {}

/-- Items emitted before the form's own items: `groupBegin` for a transparency group, else the
informational `/BBox` `clip` item. -/
def FormJob.pre (j : FormJob) : List DisplayItem :=
  match j.group with
  | some g => [.groupBegin g]
  | none => j.clip.toList.map (.clip · .nonzero)

/-- Items emitted after the form's own items: `groupEnd` for a transparency group. -/
def FormJob.post (j : FormJob) : List DisplayItem :=
  match j.group with
  | some _ => [.groupEnd]
  | none => []

/-- The frame a form job runs in, nested in `fr`: the form's resources and owner, the form
on the nesting path, the form's start CTM as base matrix. -/
def FormJob.frame (j : FormJob) (fr : Frame) : Frame :=
  Frame.mk' j.res (j.num :: fr.visited) j.owner j.ownerGen j.gs.ctm

/-- A form adds at most two items of its own (`Paint.maxItems`, charged to its `Do`). -/
theorem FormJob.pre_post_le (j : FormJob) : j.pre.length + j.post.length ≤ 2 := by
  unfold FormJob.pre FormJob.post
  cases j.group <;> cases j.clip <;> simp

/-- The graphics state inside a transparency group or soft-mask group: alpha, blend mode and
soft mask reset to their initial values (§11.6.6; they apply to the group as a whole). -/
def resetTx (g : GState) : GState :=
  { g with fillAlpha := Comp.one, strokeAlpha := Comp.one, blendMode := BlendMode.normal,
           softMask := Option.none }

/-- A boolean entry (`false` when absent or malformed). -/
def boolEntry (d : Dict) (k : String) : Bool :=
  match Dict.get? d (nm k) with
  | some (.bool b) => b
  | _ => false

/-- The transparency group of a form dictionary `d` (`/Group` with `/S /Transparency`),
composited with the alpha, blend mode and soft mask of `gs`; `bbox` in page space. -/
def groupOf {σ : Type} (src : Source σ) (s : σ) (d : Dict) (gs : GState) (bbox : Option Path) :
    Option GroupInfo × σ :=
  match Dict.get? d (nm "Group") with
  | none => (none, s)
  | some o =>
    let (g, s) := dictOf src s o
    match Dict.get? g (nm "S") with
    | some (.name t) =>
      if t = nm "Transparency" then
        (some { bbox := bbox, isolated := boolEntry g "I", knockout := boolEntry g "K",
                alpha := gs.fillAlpha, blend := gs.blendMode, smask := gs.softMask }, s)
      else (none, s)
    | _ => (none, s)

/-! ## Optional content (task 9.r11a, §8.11.3) -/

/-- Whether optional content `o` (an `/OC` entry, or a `/Properties` entry of `BDC /OC`) is
visible in the environment's state (`Doc.OptionalContent.isVisible`, objects resolved through
the source). -/
def ocVisible {σ ω : Type} (env : Env σ ω) (s : σ) (o : PdfObject) : Bool × σ :=
  Doc.OptionalContent.isVisible (resolve env.src) env.cfg.limits env.oc s o

/-- Whether the `/OC` entry of dictionary `d` (an XObject) leaves it visible (no entry:
visible). -/
def dictVisible {σ ω : Type} (env : Env σ ω) (s : σ) (d : Dict) : Bool × σ :=
  match Dict.get? d (nm "OC") with
  | some o => ocVisible env s o
  | none => (true, s)

/-- Whether a `BDC` with operands `o` opens visible content: `/OC /name BDC` looks `name` up in
the current frame's `/Properties` (§8.11.3.2; an inline dictionary is accepted too); any
other tag, a missing resource, or no optional content in the state: visible. -/
def bdcVisible {σ ω : Type} (env : Env σ ω) (fr : Frame) (s : σ) (o : List PdfObject) :
    Bool × σ :=
  if env.oc.known.isEmpty then (true, s) else
  match lastN 2 o with
  | some [.name tag, .name p] =>
    if tag = nm "OC" then
      match resEntryI env.src s fr.res fr.idx "Properties" p with
      | (some e, s) => ocVisible env s e
      | (none, s) => (true, s)
    else (true, s)
  | some [.name tag, .dict d] => if tag = nm "OC" then ocVisible env s (.dict d) else (true, s)
  | _ => (true, s)

/-- **Optional content nesting** after operator `op`: `BMC` opens a visible sequence, `BDC` a
sequence visible per `bdcVisible`, `EMC` closes one (`OcMarks.push`, `OcMarks.pop`); every
other operator leaves it. -/
def ocTrack {σ ω : Type} (env : Env σ ω) (fr : Frame) (oc : OcMarks) (s : σ) (op : Op) :
    OcMarks × σ :=
  if op.op = [69, 77, 67] then (oc.pop, s)                -- EMC
  else if op.op = [66, 77, 67] then (oc.push true, s)     -- BMC
  else if op.op = [66, 68, 67] then                       -- BDC
    let r := bdcVisible env fr s op.operands
    (oc.push r.1, r.2)
  else (oc, s)

/-- The items an operator emits, kept only when the content is visible both before and after
it (so the `BDC` opening hidden content and the `EMC` closing it emit nothing either). -/
def ocKeep (before after : OcMarks) (its : List DisplayItem) : List DisplayItem :=
  if before.hidden || after.hidden then [] else its

/-- Filtering never adds items. -/
theorem ocKeep_length_le (before after : OcMarks) (its : List DisplayItem) :
    (ocKeep before after its).length ≤ its.length := by
  unfold ocKeep; split <;> simp

/-- With no optional content in the state, `BDC` is always visible and nothing is fetched. -/
theorem bdcVisible_inactive {σ ω : Type} (env : Env σ ω) (fr : Frame) (s : σ)
    (o : List PdfObject) (h : env.oc.known = []) : bdcVisible env fr s o = (true, s) := by
  simp [bdcVisible, h]

/-- With no optional content in the state, `/OC` entries are always visible. -/
theorem dictVisible_inactive {σ ω : Type} (env : Env σ ω) (s : σ) (d : Dict)
    (h : env.oc.known = []) : dictVisible env s d = (true, s) := by
  unfold dictVisible ocVisible
  split
  · exact Doc.OptionalContent.isVisible_inactive _ _ _ _ _ h
  · rfl

/-- With no optional content in the state, tracking never hides anything and touches no
source state. -/
theorem ocTrack_inactive {σ ω : Type} (env : Env σ ω) (fr : Frame) (oc : OcMarks) (s : σ)
    (op : Op) (h : env.oc.known = []) (hv : oc.hiddenAt = none) :
    (ocTrack env fr oc s op).1.hiddenAt = none ∧ (ocTrack env fr oc s op).2 = s := by
  unfold ocTrack
  split
  · exact ⟨OcMarks.pop_visible oc hv, rfl⟩
  · split
    · exact ⟨OcMarks.push_visible oc hv, rfl⟩
    · split
      · rw [bdcVisible_inactive env fr s _ h]
        exact ⟨OcMarks.push_visible oc hv, rfl⟩
      · exact ⟨hv, rfl⟩

/-- **The filter is the identity while nothing is hidden.** -/
theorem ocKeep_visible (before after : OcMarks) (its : List DisplayItem)
    (h1 : before.hiddenAt = none) (h2 : after.hiddenAt = none) : ocKeep before after its = its := by
  simp [ocKeep, OcMarks.hidden, h1, h2]

/-- What `Do` does, before any nesting. -/
inductive DoOut (σ : Type) where
  /-- Finished: an optional item (an image), warnings, source state; the machine is
  unchanged. -/
  | done (it : Option DisplayItem) (w : Nat) (s : σ)
  /-- Expand a form. -/
  | form (job : FormJob) (s : σ)

/-- Prepare form `n` (dictionary `d`, tokenized content `t`). -/
def formJobT {σ ω : Type} (env : Env σ ω) (fr : Frame) (m : Machine) (n g : Nat) (d : Dict)
    (t : TokResult) (s : σ) : DoOut σ :=
  let r := formResources env.src s d fr.res fr.owner n
  let gs := m.core.gs
  let ctm := Matrix.mul (formMatrix d) gs.ctm
  let path := (bboxOf d).map fun (x0, y0, x1, y1) => rectPath ctm x0 y0 x1 y1
  let grp := groupOf env.src r.2 d gs path
  let gs1 := if grp.1.isSome then resetTx gs else gs
  let gs2 := match path with
    | some p => { gs1 with ctm, clip := ⟨p, .nonzero⟩ :: gs1.clip }
    | none => { gs1 with ctm }
  .form ⟨n, t.ops, t.warnings, r.1.1, r.1.2,
    if r.1.2 = n then g else fr.ownerGen, gs2, path, if path.isSome then 0 else 1, grp.1,
    m.patFill, m.patStroke⟩
    grp.2

/-- Prepare form `n` (dictionary `d`, decoded content `bytes`): `formJobT` of the tokenized
bytes. -/
def formJob {σ ω : Type} (env : Env σ ω) (fr : Frame) (m : Machine) (n g : Nat) (d : Dict)
    (bytes : ByteArray) (s : σ) : DoOut σ :=
  formJobT env fr m n g d (Ops.tokenize env.cfg.limits bytes) s

/-- `formJobT` prepares form `n`. -/
theorem formJobT_num {σ ω : Type} {env : Env σ ω} {fr : Frame} {m : Machine} {n g : Nat}
    {d : Dict} {t : TokResult} {s : σ} {job : FormJob} {s' : σ}
    (h : formJobT env fr m n g d t s = .form job s') : job.num = n := by
  unfold formJobT at h
  cases h; rfl

/-- `formJob` prepares form `n`. -/
theorem formJob_num {σ ω : Type} {env : Env σ ω} {fr : Frame} {m : Machine} {n g : Nat}
    {d : Dict} {bytes : ByteArray} {s : σ} {job : FormJob} {s' : σ}
    (h : formJob env fr m n g d bytes s = .form job s') : job.num = n :=
  formJobT_num h

/-- `Do /Name` (`nest`: fuel is left for a form). -/
def doStep {σ ω : Type} (env : Env σ ω) (nest : Bool) (fr : Frame) (m : Machine) (s : σ)
    (op : Op) : DoOut σ :=
  if m.oc.hidden then .done none 0 s else
  match lastName? op.operands with
  | none => .done none 1 s
  | some name =>
    match xobjectOf env.src s fr.res fr.idx name with
    | (.missing, s) => .done none 1 s
    | (.ignored, s) => .done none 0 s
    | (.image n g d, s) =>
      match dictVisible env s d with
      | (false, s) => .done none 0 s
      | (true, s) =>
        let f := annotFill env.src s fr m.patFill m.core.gs.fillStyle
        .done (some (.image (.xobject name n g) m.core.gs.ctm f.1 m.core.gs.clip)) 0 f.2
    | (.form n g st, s) =>
      match dictVisible env s st.dict with
      | (false, s) => .done none 0 s
      | (true, s) =>
      if fr.visited.contains n then .done none 1 s
      else if nest then
        match env.formCode s n g st with
        | (.error _, s) => .done none 1 s
        | (.ok t, s) => formJobT env fr m n g st.dict t s
      else .done none 1 s

/-- The machine a form runs in: the given graphics state, everything else fresh. -/
def formMachine (gs : GState) : Machine := ⟨{ gs }, {}, none, {}, {}, {}⟩

/-- The machine a form job runs in: `formMachine` with the invoking machine's pattern
bookkeeping (task 7.3f). -/
def FormJob.machine (j : FormJob) : Machine :=
  { formMachine j.gs with patFill := j.patFill, patStroke := j.patStroke }

/-! ## Soft masks (§11.6.5, task 7.3c) -/

/-- What an ExtGState's `/SMask` asks for. -/
inductive MaskOut (σ : Type) where
  /-- No soft-mask dictionary (absent, `/None`, or no ExtGState). -/
  | none (s : σ)
  /-- A soft-mask dictionary that cannot be expanded (malformed, missing group, on the
  nesting path, no fuel or form budget left): one warning, the mask is cleared. -/
  | bad (s : σ)
  /-- Expand the mask group `job`. -/
  | form (info : SoftMaskInfo) (job : FormJob) (s : σ)

/-- The ExtGState dictionary `gs` names, if any. -/
def gsDict? {σ : Type} (src : Source σ) (fr : Frame) (s : σ) (op : Op) : Option Dict × σ :=
  match lastName? op.operands with
  | none => (none, s)
  | some n =>
    match resEntryI src s fr.res fr.idx "ExtGState" n with
    | (some o, s) =>
      match resolve src s o with
      | (.dict d, s) => (some d, s)
      | (_, s) => (none, s)
    | (none, s) => (none, s)

/-- A device colour from 1, 3 or 4 components (`/BC`); black otherwise. -/
def colorOfNums : List Fixed → Color
  | [g] => .gray (Comp.ofFixed g)
  | [r, g, b] => .rgb (Comp.ofFixed r) (Comp.ofFixed g) (Comp.ofFixed b)
  | [c, m, y, k] => .cmyk (Comp.ofFixed c) (Comp.ofFixed m) (Comp.ofFixed y) (Comp.ofFixed k)
  | _ => .gray Comp.zero

/-- The `/S` of a soft-mask dictionary. -/
def maskKind? (sm : Dict) : Option SoftMaskKind :=
  match Dict.get? sm (nm "S") with
  | some (.name k) =>
    if k = nm "Luminosity" then some .luminosity
    else if k = nm "Alpha" then some .alpha
    else none
  | _ => none

/-- Prepare the soft mask of `gs` (`nest`: fuel and form budget are left). The mask group
`/G` is run like a form in the state at the `gs` (its coordinate system, §11.6.5.2) with
alpha, blend mode and soft mask reset (`resetTx`). `/TR` is ignored. -/
def maskJob {σ ω : Type} (env : Env σ ω) (nest : Bool) (fr : Frame) (m : Machine) (s : σ)
    (op : Op) : MaskOut σ :=
  match gsDict? env.src fr s op with
  | (none, s) => .none s
  | (some d, s) =>
    match Dict.get? d (nm "SMask") with
    | none => .none s
    | some o =>
      match resolve env.src s o with
      | (.name _, s) => .none s
      | (.dict sm, s) =>
        let bc := ((Dict.get? sm (nm "BC")).bind numsOf).map colorOfNums
        match maskKind? sm, Dict.get? sm (nm "G") with
        | some kind, some (.ref n g) =>
          if fr.visited.contains n || !nest then .bad s else
          match env.src.fetch s n g with
          | (.ok (.stream st), s) =>
            match env.formCode s n g st with
            | (.ok t, s) =>
              match formJobT env fr (withGs m (resetTx m.core.gs)) n g st.dict t s with
              | .form job s =>
                .form { kind, backdrop := bc.getD (.gray Comp.zero), bbox := job.clip } job s
              | .done _ _ s => .bad s
            | (.error _, s) => .bad s
          | (_, s) => .bad s
        | _, _ => .bad s
      | (_, s) => .bad s

/-- **`gs` in the runner**: `gsStep` applies the ExtGState; a soft-mask dictionary's group
is then run by `inner` into a fresh item list, wrapped into one
`softMask id info items` item (`id` = the operator count `ops` at this `gs`, unique in the
page), and the graphics state's `softMask` is set to `some id`. -/
def gsR {σ ω : Type} (env : Env σ ω) (inner : Option (Frame → St σ ω → Array Op → St σ ω))
    (fr : Frame) (m : Machine) (items : DisplayList) (warnings unsupported ops forms : Nat)
    (truncated : Bool) (s : σ) (obs : ω) (op : Op) : St σ ω :=
  match gsStep env.src fr m s op with
  | (m1, _, w, _, s1) =>
    let obs1 := env.observe obs op w 0
    match maskJob env (inner.isSome && decide (forms < env.maxForms)) fr m1 s1 op with
    | .none s2 => ⟨m1, items, warnings + w, unsupported, ops + 1, forms, truncated, s2, obs1⟩
    | .bad s2 => ⟨m1, items, warnings + w + 1, unsupported, ops + 1, forms, truncated, s2, obs1⟩
    | .form info job s2 =>
      match inner with
      | none => ⟨m1, items, warnings + w + 1, unsupported, ops + 1, forms, truncated, s2, obs1⟩
      | some run =>
        match run (job.frame fr)
            ⟨job.machine, #[], warnings + w + (job.w + job.tokW), unsupported, ops + 1,
              forms + 1, truncated, s2, obs1⟩ job.ops with
        | ⟨_, items2, w2, u2, ops2, forms2, tr2, s3, obs3⟩ =>
          ⟨withGs m1 { m1.core.gs with softMask := some ops },
            items.push (.softMask ops info items2), w2, u2, ops2, forms2, tr2, s3, obs3⟩

/-! ## Uncoloured patterns (task 7.3f, §8.7.3.3) -/

/-- Bookkeeping after `CS`/`cs` (space `sp` now current): a pattern space selected by a
resource name remembers that name (its underlying space is read at `SCN`/`scn`). -/
def csBook (sp : ColorSpace) (op : Op) : PatState :=
  match sp, lastName? op.operands with
  | .pattern, some n => { space := if (deviceOfName n).isNone && n != nm "Pattern" then some n else none }
  | _, _ => {}

/-- The underlying space of pattern colour space resource `key` (`[/Pattern base]`). -/
def underOf {σ : Type} (src : Source σ) (s : σ) (res : Dict) (ix : ResIdx res) (key : Name) :
    Option CSInfo × σ :=
  match resEntryI src s res ix "ColorSpace" key with
  | (some o, s) =>
    match resolve src s o with
    | (.array [.name p, b], s) => if p = nm "Pattern" then csInfo src s b else (none, s)
    | (_, s) => (none, s)
  | (none, s) => (none, s)

/-- Bookkeeping after `SCN`/`scn` (current space `sp`, colour `c` after `exec`): in a pattern
space with colour operands before the pattern name, record the pattern's underlying colour —
computed in the underlying space of the named pattern space, else by operand count (1, 3, 4:
gray, RGB, CMYK). -/
def scnBook {σ : Type} (src : Source σ) (fr : Frame) (p : PatState) (sp : ColorSpace) (c : Color)
    (s : σ) (op : Op) : PatState × σ :=
  match sp, c with
  | .pattern, .pattern n =>
    let xs := op.operands.filterMap num?
    if xs.isEmpty then ({ p with under := none }, s) else
    let (info, s) := match p.space with
      | some key => underOf src s fr.res fr.idx key
      | none => (none, s)
    let col := match info with
      | some i => i.color xs
      | none => colorOfNums xs
    ({ p with under := some (n, col) }, s)
  | _, _ => (p, s)

/-- Pattern bookkeeping of one executed local operator (`m`: the machine after it). -/
def patBook {σ : Type} (src : Source σ) (fr : Frame) (m : Machine) (s : σ) (op : Op) :
    PatState × PatState × σ :=
  match op.op with
  | [67, 83] => (m.patFill, csBook m.core.gs.strokeSpace op, s)   -- CS
  | [99, 115] => (csBook m.core.gs.fillSpace op, m.patStroke, s)  -- cs
  | [83, 67, 78] =>                                               -- SCN
    let r := scnBook src fr m.patStroke m.core.gs.strokeSpace m.core.gs.strokeColor s op
    (m.patFill, r.1, r.2)
  | [115, 99, 110] =>                                             -- scn
    let r := scnBook src fr m.patFill m.core.gs.fillSpace m.core.gs.fillColor s op
    (r.1, m.patStroke, r.2)
  | _ => (m.patFill, m.patStroke, s)

/-- **One runner step.** At the operator cap nothing is executed (the first time, one
warning). `Do` of a form runs `inner` (the runner with one less fuel) from `formMachine`, then
restores the invoking machine; every other operator is a `localStep`. -/
def stepR {σ ω : Type} (env : Env σ ω) (inner : Option (Frame → St σ ω → Array Op → St σ ω))
    (fr : Frame) (st : St σ ω) (op : Op) : St σ ω :=
  match st with
  | ⟨m, items, warnings, unsupported, ops, forms, truncated, s, obs⟩ =>
    if env.cfg.limits.maxOpsPerPage ≤ ops then
      ⟨m, items, if truncated then warnings else warnings + 1, unsupported, ops, forms, true,
        s, obs⟩
    else if op.op = [68, 111] then -- Do
      match doStep env (inner.isSome && decide (forms < env.maxForms)) fr m s op with
      | .done it w s' =>
        ⟨m, pushAll items it.toList, warnings + w, unsupported, ops + 1, forms, truncated, s',
          env.observe obs op w 0⟩
      | .form job s' =>
        match inner with
        | some run =>
          let w := job.w + job.tokW
          match run (job.frame fr)
              ⟨job.machine, pushAll items job.pre,
                warnings + w, unsupported, ops + 1, forms + 1, truncated, s',
                env.observe obs op w 0⟩ job.ops with
          | ⟨_, items2, w2, u2, ops2, forms2, tr2, s2, obs2⟩ =>
            ⟨m, pushAll items2 job.post, w2, u2, ops2, forms2, tr2, s2, obs2⟩
        | none =>
          ⟨m, items, warnings + 1, unsupported, ops + 1, forms, truncated, s',
            env.observe obs op 1 0⟩
    else if op.op = [103, 115] then -- gs
      gsR env inner fr m items warnings unsupported ops forms truncated s obs op
    else
      -- `m.oc` is bound BEFORE the call (task 13.1): reading `m` after `localStep` keeps the
      -- machine shared across the call, so every `addSegs` push copies the whole path.
      let moc := m.oc
      match localStep env fr m s op with
      | (m', its, w, u, s') =>
        let t := ocTrack env fr moc s' op
        let pb := patBook env.src fr m' t.2 op
        let a := annotAll env.src fr pb.1 pb.2.1 pb.2.2 (ocKeep moc t.1 its)
        ⟨{ m' with patFill := pb.1, patStroke := pb.2.1, oc := t.1 }, pushAll items a.1,
          warnings + w, unsupported + u, ops + 1, forms, truncated, a.2, env.observe obs op w u⟩

/-- **The runner**, by structural recursion on the nesting fuel: a form invoked at fuel
`f + 1` runs at fuel `f`; at fuel 0 forms are skipped (warning). -/
def runOps {σ ω : Type} (env : Env σ ω) : Nat → Frame → St σ ω → Array Op → St σ ω
  | 0, fr, st, ops => ops.foldl (stepR env none fr) st
  | f + 1, fr, st, ops => ops.foldl (stepR env (some (runOps env f)) fr) st

/-! ## Termination and bounds -/

/-- **A form on the nesting path is never re-entered, and none is entered without fuel**:
whenever `doStep` asks for a form to be expanded, its object number is not on the path and
fuel is left. (With `runOps`' structural recursion on the fuel this is the termination
argument of Plan.md §5.2: a self-referencing or mutually recursive form is cut at its second
occurrence on the path, any nesting at `maxXObjectDepth`.) -/
theorem doStep_form_fresh {σ ω : Type} {env : Env σ ω} {nest : Bool} {fr : Frame}
    {m : Machine} {s : σ} {op : Op} {job : FormJob} {s' : σ}
    (h : doStep env nest fr m s op = .form job s') :
    job.num ∉ fr.visited ∧ nest = true := by
  unfold doStep at h
  split at h
  · cases h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h
    · split at h <;> cases h
    · rename_i n' _ st s1 _
      split at h
      · cases h
      by_cases hv : fr.visited.contains n' = true
      · simp only [hv, ↓reduceIte] at h; cases h
      · cases nest
        · simp only [hv, Bool.false_eq_true, ↓reduceIte] at h; cases h
        · simp only [hv, Bool.false_eq_true, ↓reduceIte] at h
          split at h
          · cases h
          · rw [formJobT_num h]
            exact ⟨by simpa using hv, rfl⟩

/-- `exec` through `viaExec` keeps its per-operator bound. -/
theorem viaExec_bound {σ : Type} (cfg : Config) (m : Machine) (s : σ) (op : Op) :
    (viaExec cfg m s op).2.1.length + pendBit (viaExec cfg m s op).1
      ≤ pendBit m + Paint.maxItems := by
  have := exec_bound cfg m op
  unfold viaExec
  revert this
  rcases exec cfg m op with ⟨m', its, w, u⟩
  exact id

/-- A local step emits at most `Paint.maxItems` items, counting the pending clip. -/
theorem localStep_bound {σ ω : Type} (env : Env σ ω) (fr : Frame) (m : Machine) (s : σ)
    (op : Op) :
    (localStep env fr m s op).2.1.length + pendBit (localStep env fr m s op).1
      ≤ pendBit m + Paint.maxItems := by
  have hk : 0 + pendBit m ≤ pendBit m + Paint.maxItems := by omega
  have hgs : ∀ (g : GState), pendBit (withGs m g) = pendBit m := fun _ => rfl
  have hcs : ∀ (stroke : Bool) (s : σ),
      (csStep env fr stroke m s op).2.1.length + pendBit (csStep env fr stroke m s op).1
        ≤ pendBit m + Paint.maxItems := by
    intro stroke s
    unfold csStep
    split
    · split
      · split
        · exact hk
        · rename_i s1 _
          have := viaExec_bound env.cfg m s1 op
          revert this
          rcases viaExec env.cfg m s1 op with ⟨m', its, w, u, s'⟩
          exact id
      · exact viaExec_bound env.cfg m s op
    · exact viaExec_bound env.cfg m s op
  have hsc : ∀ (stroke : Bool) (s : σ),
      (scStep env fr stroke m s op).2.1.length + pendBit (scStep env fr stroke m s op).1
        ≤ pendBit m + Paint.maxItems := by
    intro stroke s
    unfold scStep
    generalize (if stroke = true then m.core.gs.strokeSpace else m.core.gs.fillSpace) = sp
    unfold scStepIn
    split
    · split
      · exact viaExec_bound env.cfg m s op
      · split
        · split
          · split
            · exact hk
            · exact hk
          · exact viaExec_bound env.cfg m _ op
        · exact viaExec_bound env.cfg m _ op
    · exact viaExec_bound env.cfg m s op
  have htf : (tfStep env fr m s op).2.1.length + pendBit (tfStep env fr m s op).1
      ≤ pendBit m + Paint.maxItems := by
    have := viaExec_bound env.cfg m s op
    unfold tfStep
    revert this
    rcases viaExec env.cfg m s op with ⟨m', its, w, u, s1⟩
    intro hv
    dsimp only at hv ⊢
    split
    · exact hv
    · exact hv
  unfold localStep
  split
  · unfold gsStep
    split
    · exact hk
    · split
      · split
        · simp only [List.length_nil, hgs]; omega
        · exact hk
      · exact hk
  · exact htf
  · exact hcs true s
  · exact hcs false s
  · exact hsc true s
  · exact hsc true s
  · exact hsc false s
  · exact hsc false s
  · unfold bdcStep
    split
    · exact viaExec_bound env.cfg m _ _
    · exact viaExec_bound env.cfg m _ _
  · exact viaExec_bound env.cfg m s op

/-- The bound invariant with slack `k`: items, plus `1` for a pending clip, plus `k`, are at
most `Paint.maxItems` per executed operator; and at most `maxOpsPerPage` operators ran. -/
def Good {σ ω : Type} (lim : Limits) (k : Nat) (st : St σ ω) : Prop :=
  st.items.size + pendBit st.m + k ≤ Paint.maxItems * st.ops ∧ st.ops ≤ lim.maxOpsPerPage

/-- `gsStep` keeps the pending clip. -/
theorem gsStep_pend {σ : Type} (src : Source σ) (fr : Frame) (m : Machine) (s : σ) (op : Op) :
    pendBit (gsStep src fr m s op).1 = pendBit m := by
  unfold gsStep
  split
  · rfl
  · split
    · split
      · rfl
      · rfl
    · rfl

/-- **`gs` keeps `Good`**: the soft-mask item counts as the `gs` operator's one item, the
mask group's own items are counted by the nested run. -/
theorem gsR_good {σ ω : Type} (env : Env σ ω)
    (inner : Option (Frame → St σ ω → Array Op → St σ ω))
    (hin : ∀ run, inner = some run → ∀ k fr st ops,
      Good env.cfg.limits k st → Good env.cfg.limits k (run fr st ops))
    (fr : Frame) (k : Nat) (m : Machine) (items : DisplayList)
    (warnings unsupported ops forms : Nat) (truncated : Bool) (s : σ) (obs : ω) (op : Op)
    (hcap : ops < env.cfg.limits.maxOpsPerPage)
    (h : items.size + pendBit m + k ≤ Paint.maxItems * ops) :
    Good env.cfg.limits k (gsR env inner fr m items warnings unsupported ops forms truncated s obs op) := by
  have hp := gsStep_pend env.src fr m s op
  unfold gsR
  revert hp
  rcases gsStep env.src fr m s op with ⟨m1, its, w, u, s1⟩
  intro hp
  simp only at hp ⊢
  have hbase : items.size + pendBit m1 + k ≤ Paint.maxItems * (ops + 1) ∧
      ops + 1 ≤ env.cfg.limits.maxOpsPerPage := by
    simp only [Paint.maxItems] at h ⊢; omega
  split
  · exact hbase
  · exact hbase
  · rename_i info job s2 _
    split
    · exact hbase
    · rename_i run _
      have h1 : Good env.cfg.limits (items.size + 1 + pendBit m + k)
          ⟨job.machine, #[], warnings + w + (job.w + job.tokW), unsupported, ops + 1,
            forms + 1, truncated, s2, env.observe obs op w 0⟩ := by
        unfold Good
        simp only [FormJob.machine, formMachine, pendBit, Option.isSome_none, Bool.false_eq_true,
          ↓reduceIte,
          Paint.maxItems, List.size_toArray, List.length_nil] at h ⊢
        omega
      have h2 := hin run rfl _ (job.frame fr) _ job.ops h1
      revert h2
      rcases run (job.frame fr)
          ⟨job.machine, #[], warnings + w + (job.w + job.tokW), unsupported, ops + 1,
            forms + 1, truncated, s2, env.observe obs op w 0⟩ job.ops with
        ⟨m2, items2, w2, u2, ops2, forms2, tr2, s3, obs3⟩
      intro h2
      unfold Good at h2 ⊢
      have hw : pendBit (withGs m1 { m1.core.gs with softMask := some ops }) = pendBit m1 := rfl
      simp only [Array.size_push, hw] at h2 ⊢
      omega

/-- **One step keeps `Good`**, given that the nested runner keeps it for every slack. -/
theorem stepR_good {σ ω : Type} (env : Env σ ω)
    (inner : Option (Frame → St σ ω → Array Op → St σ ω))
    (hin : ∀ run, inner = some run → ∀ k fr st ops,
      Good env.cfg.limits k st → Good env.cfg.limits k (run fr st ops))
    (fr : Frame) (k : Nat) (st : St σ ω) (op : Op) (h : Good env.cfg.limits k st) :
    Good env.cfg.limits k (stepR env inner fr st op) := by
  obtain ⟨m, items, warnings, unsupported, ops, forms, truncated, s, obs⟩ := st
  unfold Good at h ⊢
  simp only at h
  unfold stepR
  by_cases hcap : env.cfg.limits.maxOpsPerPage ≤ ops
  · simp only [hcap, ↓reduceIte]
    exact h
  · simp only [hcap, ↓reduceIte]
    split
    · -- Do
      rcases hd : doStep env (inner.isSome && decide (forms < env.maxForms)) fr m s op with ⟨it, w, s'⟩ | ⟨job, s'⟩
      · have : it.toList.length ≤ 1 := by cases it <;> simp
        simp only [size_pushAll, Paint.maxItems] at h ⊢
        omega
      · simp only
        rcases hi : inner with _ | run
        · simp only [Paint.maxItems] at h ⊢
          omega
        · have hrun : inner = some run := hi
          simp only
          have hcl := FormJob.pre_post_le job
          have h1 : Good env.cfg.limits (pendBit m + k + job.post.length)
              ⟨job.machine, pushAll items job.pre,
                warnings + (job.w + job.tokW), unsupported, ops + 1, forms + 1, truncated, s',
                env.observe obs op (job.w + job.tokW) 0⟩ := by
            unfold Good
            simp only [size_pushAll, FormJob.machine, formMachine, pendBit, Option.isSome_none,
              Bool.false_eq_true, ↓reduceIte, Paint.maxItems] at h hcl ⊢
            omega
          have h2 := hin run hrun (pendBit m + k + job.post.length)
            (job.frame fr) _ job.ops h1
          revert h2
          rcases run (job.frame fr)
              ⟨job.machine, pushAll items job.pre,
                warnings + (job.w + job.tokW), unsupported, ops + 1, forms + 1, truncated, s',
                env.observe obs op (job.w + job.tokW) 0⟩ job.ops with
            ⟨m2, items2, w2, u2, ops2, forms2, tr2, s2, obs2⟩
          intro h2
          unfold Good at h2
          simp only [size_pushAll] at h2 ⊢
          omega
    · split
      · -- gs
        exact gsR_good env inner hin fr k m items warnings unsupported ops forms truncated s obs op
          (by omega) h.1
      · -- every other operator
        have hb := localStep_bound env fr m s op
        revert hb
        rcases localStep env fr m s op with ⟨m', its, w, u, s'⟩
        intro hb
        have hk := ocKeep_length_le m.oc (ocTrack env fr m.oc s' op).1 its
        have hl := annotAll_length env.src fr
          (patBook env.src fr m' (ocTrack env fr m.oc s' op).2 op).1
          (patBook env.src fr m' (ocTrack env fr m.oc s' op).2 op).2.1
          (patBook env.src fr m' (ocTrack env fr m.oc s' op).2 op).2.2
          (ocKeep m.oc (ocTrack env fr m.oc s' op).1 its)
        simp only [size_pushAll, hl, pendBit, Paint.maxItems] at h hb hk ⊢
        omega

/-- Folding steps keeps `Good`. -/
theorem foldl_good {σ ω : Type} (env : Env σ ω)
    (inner : Option (Frame → St σ ω → Array Op → St σ ω))
    (hin : ∀ run, inner = some run → ∀ k fr st ops,
      Good env.cfg.limits k st → Good env.cfg.limits k (run fr st ops))
    (fr : Frame) (k : Nat) (l : List Op) (st : St σ ω) (h : Good env.cfg.limits k st) :
    Good env.cfg.limits k (l.foldl (stepR env inner fr) st) := by
  induction l generalizing st with
  | nil => exact h
  | cons op rest ih => exact ih _ (stepR_good env inner hin fr k st op h)

/-- **The runner keeps `Good`** at every fuel (induction on the fuel). -/
theorem runOps_good {σ ω : Type} (env : Env σ ω) :
    ∀ (fuel k : Nat) (fr : Frame) (st : St σ ω) (ops : Array Op),
      Good env.cfg.limits k st → Good env.cfg.limits k (runOps env fuel fr st ops)
  | 0, k, fr, st, ops, h => by
    unfold runOps
    rw [← Array.foldl_toList]
    exact foldl_good env none (fun _ h => by cases h) fr k ops.toList st h
  | f + 1, k, fr, st, ops, h => by
    unfold runOps
    rw [← Array.foldl_toList]
    refine foldl_good env (some (runOps env f)) ?_ fr k ops.toList st h
    intro run hrun k' fr' st' ops' h'
    cases hrun
    exact runOps_good env f k' fr' st' ops' h'

/-! ## Optional content without `/OCProperties` (task 9.r11a)

With no optional content group in the state (`env.oc.known = []`, the default and every
document without `/OCProperties`), nothing is ever hidden: the machine's optional content
nesting never hides (`runOps_oc_visible`), so the item filter `ocKeep` is the identity at every
step (`ocKeep_visible`), `Do` is never skipped for being inside hidden content (`doStep`'s
first test) or for its `/OC` (`dictVisible_inactive`), and no object is fetched for optional
content (`ocTrack_inactive`, `bdcVisible_inactive`): the runner emits exactly what it emitted
before optional content was implemented. -/

/-- `gsStep` keeps the optional content nesting. -/
theorem gsStep_oc {σ : Type} (src : Source σ) (fr : Frame) (m : Machine) (s : σ) (op : Op) :
    (gsStep src fr m s op).1.oc = m.oc := by
  unfold gsStep
  split
  · rfl
  · split
    · split
      · rfl
      · rfl
    · rfl

/-- **One step hides nothing** when the state has no optional content and nothing was hidden. -/
theorem stepR_oc_visible {σ ω : Type} (env : Env σ ω)
    (inner : Option (Frame → St σ ω → Array Op → St σ ω)) (fr : Frame) (st : St σ ω) (op : Op)
    (h : env.oc.known = []) (hv : st.m.oc.hiddenAt = none) :
    (stepR env inner fr st op).m.oc.hiddenAt = none := by
  obtain ⟨m, items, warnings, unsupported, ops, forms, truncated, s, obs⟩ := st
  simp only at hv
  unfold stepR
  by_cases hcap : env.cfg.limits.maxOpsPerPage ≤ ops
  · simp only [hcap, ↓reduceIte]
    exact hv
  · simp only [hcap, ↓reduceIte]
    by_cases hdo : op.op = [68, 111]
    · simp only [hdo, ↓reduceIte]
      repeat (first | exact hv | split)
    · simp only [hdo, ↓reduceIte]
      by_cases hgs : op.op = [103, 115]
      · simp only [hgs, ↓reduceIte]
        unfold gsR
        have hp := gsStep_oc env.src fr m s op
        revert hp
        rcases gsStep env.src fr m s op with ⟨m1, its, w, u, s1⟩
        intro hp
        simp only at hp ⊢
        repeat (first | (rw [hp]; exact hv) | (simp only [withGs]; rw [hp]; exact hv) | split)
      · simp only [hgs, ↓reduceIte]
        rcases localStep env fr m s op with ⟨m', its, w, u, s'⟩
        exact (ocTrack_inactive env fr m.oc s' op h hv).1

/-- Folding steps hides nothing (no optional content in the state). -/
theorem foldl_oc_visible {σ ω : Type} (env : Env σ ω)
    (inner : Option (Frame → St σ ω → Array Op → St σ ω)) (fr : Frame) (h : env.oc.known = []) :
    ∀ (l : List Op) (st : St σ ω), st.m.oc.hiddenAt = none →
      (l.foldl (stepR env inner fr) st).m.oc.hiddenAt = none
  | [], _, hv => hv
  | op :: rest, st, hv => foldl_oc_visible env inner fr h rest _ (stepR_oc_visible env inner fr st op h hv)

/-- **No `/OCProperties`, no hidden content**: with no optional content group in the state, the
runner (at every nesting fuel, so in every form) never enters hidden content. -/
theorem runOps_oc_visible {σ ω : Type} (env : Env σ ω) (h : env.oc.known = []) (fuel : Nat)
    (fr : Frame) (st : St σ ω) (ops : Array Op) (hv : st.m.oc.hiddenAt = none) :
    (runOps env fuel fr st ops).m.oc.hiddenAt = none := by
  cases fuel with
  | zero =>
    unfold runOps; rw [← Array.foldl_toList]; exact foldl_oc_visible env none fr h _ st hv
  | succ f =>
    unfold runOps; rw [← Array.foldl_toList]; exact foldl_oc_visible env _ fr h _ st hv

/-! ## Per-page form cache (task 7.9b)

A form drawn many times on a page (a plot marker: 21,879 `Do`s of one form on arXiv 2307.09288
p25) was decoded and tokenized at every `Do`. `runPage` runs the page with `FormCache.env`:
the source state is paired with a `FormCache`, and `Env.formCode` looks a form up by object
number, generation **and stream** (so a hit is always the content of the very same stream)
before decoding it. The cache lives for one page run, holds at most
`Limits.maxFormCacheEntries` forms of at most `Limits.maxFormCacheBytes` decoded bytes in all
(a form that does not fit is simply not cached), and only successful decodes are cached.

**Budget charging.** A hit does not call the source, so a cached form charges the document's
decoded-bytes budget (`Filter.Budget`, task 3.10) **once per page run** instead of once per
`Do`. The budget theorems (`Filter.decodeAllB_total`, `Doc.decodeContentsB_total`, …) bound the
bytes *actually decoded* by the budget; they are unchanged and still true, since fewer decodes
happen. Every cached entry was charged when it was decoded, so the cache holds no bytes the
budget has not paid for. What changes is only that a page whose repeated form decodes used to
exhaust the budget now gets those forms drawn (`FormCache.code_fst_eq`: whenever the decode
result does not depend on the source state, the cached content equals the uncached one).
-/

/-- A cached form: its reference, its stream, its tokenized content and its decoded size. -/
structure FormEntry where
  /-- Object number. -/
  num : Nat
  /-- Generation number. -/
  gen : Nat
  /-- The form's stream (as fetched). -/
  st : Stream
  /-- Its content, tokenized. -/
  code : TokResult
  /-- Its decoded size in bytes. -/
  size : Nat

/-- An entry is genuine: for some source state its stream decoded successfully through `src`
to `size` bytes, whose tokenization is `code`. -/
def FormEntry.Valid {σ : Type} (src : Source σ) (lim : Limits) (e : FormEntry) : Prop :=
  ∃ s0 bytes s1, src.decode s0 e.num e.st = (.ok bytes, s1) ∧ e.code = Ops.tokenize lim bytes ∧
    e.size = bytes.size

/-- **The per-page form cache**: genuine entries only (`valid`), at most
`maxFormCacheEntries` of them with at most `maxFormCacheBytes` decoded bytes in all — by
construction, every value of this type satisfies these invariants. -/
structure FormCache {σ : Type} (src : Source σ) (lim : Limits) where
  /-- The entries, most recently inserted first. -/
  entries : List FormEntry
  /-- Their total decoded size. -/
  bytes : Nat
  /-- Every entry is genuine. -/
  valid : ∀ e ∈ entries, e.Valid src lim
  /-- `bytes` is the total decoded size. -/
  bytes_eq : bytes = (entries.map FormEntry.size).sum
  /-- Count bound. -/
  count_le : entries.length ≤ lim.maxFormCacheEntries
  /-- Size bound. -/
  bytes_le : bytes ≤ lim.maxFormCacheBytes

namespace FormCache

variable {σ : Type} {src : Source σ} {lim : Limits}

/-- The empty cache. -/
def empty : FormCache src lim :=
  ⟨[], 0, by simp, by simp, Nat.zero_le _, Nat.zero_le _⟩

/-- The entry for form `num gen` with stream `st`, if cached. -/
def find? (c : FormCache src lim) (num gen : Nat) (st : Stream) : Option FormEntry :=
  c.entries.find? fun e => e.num == num && e.gen == gen && decide (e.st = st)

/-- Insert a genuine entry when it fits both bounds; otherwise the cache is unchanged. -/
def insert (c : FormCache src lim) (e : FormEntry) (h : e.Valid src lim) : FormCache src lim :=
  if hc : c.entries.length < lim.maxFormCacheEntries ∧ c.bytes + e.size ≤ lim.maxFormCacheBytes
  then
    ⟨e :: c.entries, c.bytes + e.size,
      fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact h
        · exact c.valid x hx,
      by have := c.bytes_eq; simp only [List.map_cons, List.sum_cons]; omega,
      by simp only [List.length_cons]; omega,
      hc.2⟩
  else c

/-- **Cached form content** (`Env.formCode` of `FormCache.env`): a hit returns the cached
tokens without touching the source state; a miss decodes through `src` and tokenizes
(`Source.code`), caching a success. -/
def code (src : Source σ) (lim : Limits) (p : σ × FormCache src lim) (num gen : Nat)
    (st : Stream) : (Except Error TokResult) × (σ × FormCache src lim) :=
  match p.2.find? num gen st with
  | some e => (.ok e.code, p)
  | none =>
    match h : src.decode p.1 num st with
    | (.ok bytes, s1) =>
      (.ok (Ops.tokenize lim bytes),
        (s1, p.2.insert ⟨num, gen, st, Ops.tokenize lim bytes, bytes.size⟩
          ⟨p.1, bytes, s1, h, rfl, rfl⟩))
    | (.error e, s1) => (.error e, (s1, p.2))

/-- The source over `σ × FormCache`: fetches and decodes act on the first component. -/
def source (src : Source σ) (lim : Limits) : Source (σ × FormCache src lim) :=
  ⟨fun p n g => let r := src.fetch p.1 n g; (r.1, (r.2, p.2)),
   fun p n st => let r := src.decode p.1 n st; (r.1, (r.2, p.2))⟩

/-- A hit is the entry of the same form and stream. -/
theorem find?_spec {c : FormCache src lim} {num gen : Nat} {st : Stream} {e : FormEntry}
    (h : c.find? num gen st = some e) :
    e.num = num ∧ e.gen = gen ∧ e.st = st ∧ e.Valid src lim := by
  have hp := List.find?_some h
  have hm := List.mem_of_find?_eq_some h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hp
  exact ⟨hp.1.1, hp.1.2, hp.2, c.valid e hm⟩

/-- **A hit leaves the source state alone** (nothing decoded, nothing charged). -/
theorem code_hit {p : σ × FormCache src lim} {num gen : Nat} {st : Stream} {e : FormEntry}
    (h : p.2.find? num gen st = some e) : code src lim p num gen st = (.ok e.code, p) := by
  unfold code
  rw [h]

/-- **A miss is the uncached reading** (`Source.code`) on the source state. -/
theorem code_miss {p : σ × FormCache src lim} {num gen : Nat} {st : Stream}
    (h : p.2.find? num gen st = none) :
    (code src lim p num gen st).1 = (src.code lim p.1 num gen st).1 ∧
      (code src lim p num gen st).2.1 = (src.code lim p.1 num gen st).2 := by
  unfold code Source.code
  rw [h]
  simp only
  split
  · rename_i bytes s1 hd
    simp [hd]
  · rename_i er s1 hd
    simp [hd]

/-- **Soundness of the cache**: any content `code` returns is the tokenization of a
successful decode, through `src`, of the very stream asked for. -/
theorem code_ok {p : σ × FormCache src lim} {num gen : Nat} {st : Stream} {t : TokResult}
    {p' : σ × FormCache src lim} (h : code src lim p num gen st = (.ok t, p')) :
    ∃ s0 bytes s1, src.decode s0 num st = (.ok bytes, s1) ∧ t = Ops.tokenize lim bytes := by
  rcases hf : p.2.find? num gen st with _ | e
  · have hm := code_miss (gen := gen) hf
    rw [h] at hm
    unfold Source.code at hm
    revert hm
    rcases hd : src.decode p.1 num st with ⟨_ | bytes, s1⟩
    · intro hm; cases hm.1
    · intro hm
      simp only [Except.ok.injEq] at hm
      exact ⟨p.1, bytes, s1, hd, hm.1⟩
  · rw [code_hit hf] at h
    simp only [Prod.mk.injEq, Except.ok.injEq] at h
    obtain ⟨hn, -, hs, s0, bytes, s1, hd, hc, -⟩ := find?_spec hf
    refine ⟨s0, bytes, s1, ?_, ?_⟩
    · rw [← hn, ← hs]; exact hd
    · rw [← h.1, hc]

/-- **Same content as without the cache** whenever decoding form `num`'s stream does not
depend on the source state (budget-free sources; a document budget that does not run out):
the cached reading equals `Source.code`. -/
theorem code_fst_eq {p : σ × FormCache src lim} {num gen : Nat} {st : Stream}
    (hdet : ∀ s0 s1, (src.decode s0 num st).1 = (src.decode s1 num st).1) :
    (code src lim p num gen st).1 = (src.code lim p.1 num gen st).1 := by
  rcases hf : p.2.find? num gen st with _ | e
  · exact (code_miss hf).1
  · rw [code_hit hf]
    obtain ⟨hn, -, hs, s0, bytes, s1, hd, hc, -⟩ := find?_spec hf
    have h1 := hdet p.1 s0
    rw [← hn, ← hs, hd] at h1
    unfold Source.code
    rw [← hn, ← hs]
    revert h1
    rcases src.decode p.1 e.num e.st with ⟨r, s2⟩
    intro h1
    simp only at h1
    subst h1
    simp only [hc]

end FormCache

/-- The environment with the per-page form cache: the same configuration, observer and form
budget; the source state paired with a `FormCache`; `formCode` reads through the cache. -/
def FormCache.env {σ ω : Type} (env : Env σ ω) : Env (σ × FormCache env.src env.cfg.limits) ω :=
  { cfg := env.cfg, src := FormCache.source env.src env.cfg.limits, observe := env.observe,
    maxForms := env.maxForms, formCode := FormCache.code env.src env.cfg.limits, oc := env.oc }

end Run

open Run

/-- The initial runner state. -/
def St.init {σ ω : Type} (s : σ) (obs : ω) : St σ ω :=
  ⟨{}, #[], 0, 0, 0, 0, false, s, obs⟩

/-- Run a page's tokenized content with its resources, **without** the per-page form cache
(each form `Do` reads the form through `env.formCode`): nesting fuel `Limits.maxXObjectDepth`,
from the initial machine. Total; never fails. The reference for `runPage`. -/
def runPageUncached {σ ω : Type} (env : Env σ ω) (res : Dict) (ops : Array Op) (s : σ)
    (obs : ω) : St σ ω :=
  Run.runOps env env.cfg.limits.maxXObjectDepth (Frame.mk' res [] 0 0 Matrix.identity) (St.init s obs) ops

/-- Forget the second component of the source state. -/
def St.fstState {σ κ ω : Type} (st : St (σ × κ) ω) : St σ ω :=
  ⟨st.m, st.items, st.warnings, st.unsupported, st.ops, st.forms, st.truncated, st.s.1, st.obs⟩

/-- **Entry point.** Run a page's tokenized content with its resources: `runPageUncached`
under `FormCache.env` (task 7.9b: each form is decoded and tokenized once per page run, within
the cache bounds), the cache dropped at the end. Total; never fails. -/
def runPage {σ ω : Type} (env : Env σ ω) (res : Dict) (ops : Array Op) (s : σ) (obs : ω) :
    St σ ω :=
  (runPageUncached (FormCache.env env) res ops (s, FormCache.empty) obs).fstState

/-- Tokenize and run decoded page content; tokenizer warnings and truncation are added. -/
def runBytes {σ ω : Type} (env : Env σ ω) (res : Dict) (bytes : ByteArray) (s : σ)
    (obs : ω) : St σ ω :=
  let t := Ops.tokenize env.cfg.limits bytes
  let st := runPage env res t.ops s obs
  { st with warnings := st.warnings + t.warnings, truncated := st.truncated || t.truncated }

/-- The initial state is `Good`. -/
theorem St.init_good {σ ω : Type} (lim : Limits) (s : σ) (obs : ω) :
    Good lim 0 (St.init s obs) :=
  ⟨by simp [St.init, pendBit], Nat.zero_le _⟩

/-- Operator bound of the uncached run. -/
theorem runPageUncached_ops_le {σ ω : Type} (env : Env σ ω) (res : Dict) (ops : Array Op)
    (s : σ) (obs : ω) : (runPageUncached env res ops s obs).ops ≤ env.cfg.limits.maxOpsPerPage :=
  (runOps_good env _ 0 _ _ ops (St.init_good _ s obs)).2

/-- Item bound of the uncached run. -/
theorem runPageUncached_items_le {σ ω : Type} (env : Env σ ω) (res : Dict) (ops : Array Op)
    (s : σ) (obs : ω) :
    (runPageUncached env res ops s obs).items.size ≤
      Paint.maxItems * (runPageUncached env res ops s obs).ops := by
  have := (runOps_good env env.cfg.limits.maxXObjectDepth 0 (Frame.mk' res [] 0 0 Matrix.identity)
    (St.init s obs) ops (St.init_good _ s obs)).1
  unfold runPageUncached
  omega

/-- **Operator bound**: at most `Limits.maxOpsPerPage` operators are executed, page and forms
together, however the forms nest. -/
theorem runPage_ops_le {σ ω : Type} (env : Env σ ω) (res : Dict) (ops : Array Op) (s : σ)
    (obs : ω) : (runPage env res ops s obs).ops ≤ env.cfg.limits.maxOpsPerPage :=
  runPageUncached_ops_le (FormCache.env env) res ops _ obs

/-- **Item bound** (generalises `interp_items_le` to forms): at most `Paint.maxItems` items per
executed operator. -/
theorem runPage_items_le {σ ω : Type} (env : Env σ ω) (res : Dict) (ops : Array Op) (s : σ)
    (obs : ω) :
    (runPage env res ops s obs).items.size ≤
      Paint.maxItems * (runPage env res ops s obs).ops :=
  runPageUncached_items_le (FormCache.env env) res ops _ obs

/-- **Display-list bound** for the bytes entry point: at most
`Paint.maxItems · Limits.maxOpsPerPage` items, whatever the page's forms do. -/
theorem runBytes_items_le_max {σ ω : Type} (env : Env σ ω) (res : Dict) (bytes : ByteArray)
    (s : σ) (obs : ω) :
    (runBytes env res bytes s obs).items.size ≤
      Paint.maxItems * env.cfg.limits.maxOpsPerPage := by
  have h1 := runPage_items_le env res (Ops.tokenize env.cfg.limits bytes).ops s obs
  have h2 := runPage_ops_le env res (Ops.tokenize env.cfg.limits bytes).ops s obs
  have h3 := Nat.mul_le_mul_left Paint.maxItems h2
  simp only [runBytes]
  omega

/-! ## Samples -/

section Tests

private def obj (s : String) : PdfObject :=
  match ObjParse.parseObject {} s.toUTF8 0 with
  | .ok (o, _) => o
  | .error _ => .null

private def dictS (s : String) : Dict :=
  match obj s with
  | .dict d => d
  | _ => []

/-- A document of numbered objects; `decode` returns stream data as is (no filters). -/
private def mkSrc (objs : List (Nat × IndirectBody)) : Source Unit :=
  ⟨fun s n _ => match objs.lookup n with
     | some b => (.ok b, s)
     | none => (.error (.malformed 0 "missing"), s),
   fun s _ st => (.ok st.data, s)⟩

private def strm (d : String) (data : String) : IndirectBody :=
  .stream ⟨dictS d, data.toUTF8⟩

private def env (objs : List (Nat × IndirectBody)) (lim : Limits := {}) : Env Unit Nat :=
  { cfg := { limits := lim }, src := mkSrc objs, observe := fun n _ _ _ => n + 1 }

private def run (objs : List (Nat × IndirectBody)) (res content : String) (lim : Limits := {}) :
    St Unit Nat :=
  runBytes (env objs lim) (dictS res) content.toUTF8 () 0

private def kinds (st : St Unit Nat) : List String := st.items.toList.map DisplayItem.kind

private def fi (n : Int) : Fixed := Fixed.ofInt n

private def pathOf : DisplayItem → Option Path
  | .fillPath p .. | .strokePath p .. | .clip p _ => some p
  | _ => none

private def fillOf : DisplayItem → Option FillStyle
  | .fillPath _ _ st _ => some st
  | _ => none

private def strokeOf : DisplayItem → Option StrokeStyle
  | .strokePath _ st _ => some st
  | _ => none

private def clipOf : DisplayItem → Option Clip
  | .fillPath _ _ _ cl | .strokePath _ _ cl | .glyphRun _ cl | .image _ _ _ cl => some cl
  | _ => none

-- a form with /Matrix and /BBox, expanded in place between q … Q
private def formDoc : List (Nat × IndirectBody) :=
  [(6, strm "<< /Subtype /Form /BBox [0 0 10 10] /Matrix [2 0 0 2 5 5] >>"
     "0 0 10 10 re f")]
private def fres : String := "<< /XObject << /Fm1 6 0 R >> >>"
#guard kinds (run formDoc fres "q /Fm1 Do Q 0 0 1 1 re f") == ["clip", "fillPath", "fillPath"]
#guard ((run formDoc fres "/Fm1 Do").items[1]?.bind pathOf) ==
  some ⟨#[.moveTo ⟨fi 5, fi 5⟩, .lineTo ⟨fi 25, fi 5⟩, .lineTo ⟨fi 25, fi 25⟩,
    .lineTo ⟨fi 5, fi 25⟩, .closePath]⟩
#guard ((run formDoc fres "/Fm1 Do").items[1]?.bind clipOf).map (·.length) == some 1
#guard ((run formDoc fres "/Fm1 Do 0 0 1 1 re f").items[2]?.bind clipOf) == some []
#guard (run formDoc fres "q /Fm1 Do Q").ops == 5      -- q Do Q and the form's re f
#guard (run formDoc fres "q /Fm1 Do Q").obs == 5      -- the observer sees each one
#guard (run formDoc fres "q /Fm1 Do Q").forms == 1
#guard (run formDoc fres "q /Fm1 Do Q").warnings == 0
-- the form's colour does not leak out; the invoking colour flows in
private def colDoc : List (Nat × IndirectBody) :=
  [(6, strm "<< /Subtype /Form /BBox [0 0 1 1] >>" "0 0 1 rg 0 0 1 1 re f q")]
#guard ((run colDoc fres "1 0 0 rg /Fm1 Do 0 0 1 1 re f").items[2]?.bind fillOf).map (·.color) ==
  some (.rgb Comp.one Comp.zero Comp.zero)
#guard ((run colDoc fres "1 0 0 rg /Fm1 Do").items[1]?.bind fillOf).map (·.color) ==
  some (.rgb Comp.zero Comp.zero Comp.one)
-- self-reference: the inner Do is cut (one warning), the rest of the form runs
private def selfDoc : List (Nat × IndirectBody) :=
  [(6, strm "<< /Subtype /Form /BBox [0 0 1 1] /Resources << /XObject << /Fm1 6 0 R >> >> >>"
     "/Fm1 Do 0 0 1 1 re f")]
#guard kinds (run selfDoc fres "/Fm1 Do") == ["clip", "fillPath"]
#guard (run selfDoc fres "/Fm1 Do").warnings == 1
#guard (run selfDoc fres "/Fm1 Do").forms == 1
-- mutual recursion Fm1 → Fm2 → Fm1: cut at the second occurrence of 6
private def mutualDoc : List (Nat × IndirectBody) :=
  [(6, strm "<< /Subtype /Form /BBox [0 0 1 1] /Resources << /XObject << /Fm2 7 0 R >> >> >>"
     "/Fm2 Do"),
   (7, strm "<< /Subtype /Form /BBox [0 0 1 1] /Resources << /XObject << /Fm1 6 0 R >> >> >>"
     "/Fm1 Do")]
#guard (run mutualDoc fres "/Fm1 Do").forms == 2
#guard (run mutualDoc fres "/Fm1 Do").warnings == 1
#guard kinds (run mutualDoc fres "/Fm1 Do") == ["clip", "clip"]
-- the fuel: at depth limit 1 the nested form is skipped with a warning
private def chainDoc : List (Nat × IndirectBody) :=
  [(6, strm "<< /Subtype /Form /BBox [0 0 1 1] /Resources << /XObject << /Fm2 7 0 R >> >> >>"
     "/Fm2 Do"),
   (7, strm "<< /Subtype /Form /BBox [0 0 1 1] >>" "0 0 1 1 re f")]
#guard (run chainDoc fres "/Fm1 Do").forms == 2
#guard (run chainDoc fres "/Fm1 Do" { maxXObjectDepth := 1 }).forms == 1
#guard (run chainDoc fres "/Fm1 Do" { maxXObjectDepth := 1 }).warnings == 1
-- a form without /Resources uses the invoking content's
#guard kinds (run chainDoc "<< /XObject << /Fm1 6 0 R /Fm2 7 0 R >> >>" "/Fm2 Do") ==
  ["clip", "fillPath"]
-- the operator cap counts form operators too
#guard (run formDoc fres "/Fm1 Do /Fm1 Do /Fm1 Do" { maxOpsPerPage := 4 }).ops == 4
#guard (run formDoc fres "/Fm1 Do /Fm1 Do /Fm1 Do" { maxOpsPerPage := 4 }).truncated
-- the form-expansion cap
#guard (runBytes { env formDoc with maxForms := 1 } (dictS fres) "/Fm1 Do /Fm1 Do".toUTF8 () 0).forms
  == 1
#guard (runBytes { env formDoc with maxForms := 1 } (dictS fres) "/Fm1 Do /Fm1 Do".toUTF8 () 0).warnings
  == 1
-- images: referenced, not decoded; PostScript XObjects ignored; missing ones warned
private def imgDoc : List (Nat × IndirectBody) :=
  [(8, strm "<< /Subtype /Image /Width 1 /Height 1 /BitsPerComponent 8 /ColorSpace /DeviceGray >>"
     "x"),
   (9, strm "<< /Subtype /PS >>" "")]
private def ires : String := "<< /XObject << /Im0 8 0 R /P 9 0 R >> >>"
#guard (match (run imgDoc ires "/Im0 Do").items[0]? with
  | some (DisplayItem.image (.xobject n 8 0) _ _ _) => n == Name.ofString "Im0"
  | _ => false)
#guard kinds (run imgDoc ires "/P Do") == []
#guard (run imgDoc ires "/P Do").warnings == 0
#guard (run imgDoc ires "/Nope Do").warnings == 1
#guard kinds (run imgDoc ires "/Nope Do") == []
-- ExtGState
private def gsRes : String :=
  "<< /ExtGState << /GS0 << /LW 5 /LC 1 /CA 0.5 /ca 0.25 /D [[2 1] 0] /Font [1 0 R 12] /BM /Multiply >> >> >>"
#guard ((run [] gsRes "/GS0 gs 0 0 1 1 re S").items[0]?.bind strokeOf).map
    (fun st => (st.line.width, st.line.cap, st.alpha, st.line.dash.array)) ==
  some (fi 5, .round, Comp.ofFixed (Fixed.ofDecimal ⟨5, 1⟩), [fi 2, fi 1])
#guard ((run [] gsRes "/GS0 gs 0 0 1 1 re f").items[0]?.bind fillOf).map (·.alpha) ==
  some (Comp.ofFixed (Fixed.ofDecimal ⟨25, 2⟩))
#guard (run [] gsRes "/GS0 gs").warnings == 0
#guard (run [] gsRes "/GS9 gs").warnings == 1
-- transparency (7.3c): blend modes, transparency groups, soft masks
#guard ((run [] gsRes "/GS0 gs 0 0 1 1 re f").items[0]?.bind fillOf).map (·.blend) ==
  some .multiply
#guard ((run [] "<< /ExtGState << /G << /BM [/Foo /Screen] >> >> >>" "/G gs 0 0 1 1 re S").items[0]?.bind
  strokeOf).map (·.blend) == some .screen
private def grpDoc : List (Nat × IndirectBody) :=
  [(6, strm "<< /Subtype /Form /BBox [0 0 10 10] /Group << /S /Transparency /I true >> >>"
     "0 0 10 10 re f 5 5 10 10 re f"),
   (7, strm "<< /Subtype /Form /BBox [0 0 4 4] /Group << /S /Transparency >> >>" "0 0 4 4 re f")]
private def grpRes : String :=
  "<< /XObject << /Fm1 6 0 R >> /ExtGState << /H << /ca 0.5 /BM /Multiply >> " ++
  "/M << /SMask << /S /Luminosity /G 7 0 R /BC [1] >> >> /N << /SMask /None >> " ++
  "/B << /SMask << /S /Luminosity /G 9 0 R >> >> >> >>"
#guard kinds (run grpDoc grpRes "/H gs /Fm1 Do 0 0 1 1 re f") ==
  ["groupBegin", "fillPath", "fillPath", "groupEnd", "fillPath"]
#guard (match (run grpDoc grpRes "/H gs /Fm1 Do").items[0]? with
  | some (DisplayItem.groupBegin g) => g.isolated && !g.knockout && g.blend == .multiply &&
      g.alpha == Comp.ofFixed (Fixed.ofDecimal ⟨5, 1⟩) && g.bbox.isSome
  | _ => false)
-- inside the group alpha and blend mode are reset; after it they are back
#guard ((run grpDoc grpRes "/H gs /Fm1 Do").items[1]?.bind fillOf).map (fun f => (f.alpha, f.blend))
  == some (Comp.one, .normal)
#guard ((run grpDoc grpRes "/H gs /Fm1 Do 0 0 1 1 re f").items[4]?.bind fillOf).map (·.blend)
  == some .multiply
#guard (run grpDoc grpRes "/H gs /Fm1 Do").warnings == 0
-- a soft mask: one nested item (its group's items), referenced by later painting
#guard kinds (run grpDoc grpRes "/M gs 0 0 1 1 re f") == ["softMask", "fillPath"]
#guard (match (run grpDoc grpRes "q /M gs 0 0 1 1 re f").items[0]? with
  | some (DisplayItem.softMask 1 info its) => info.kind == .luminosity &&
      info.backdrop == .gray Comp.one && its.toList.map DisplayItem.kind == ["fillPath"]
  | _ => false)
#guard ((run grpDoc grpRes "q /M gs 0 0 1 1 re f").items[1]?.bind fillOf).map (·.smask)
  == some (some 1)
#guard ((run grpDoc grpRes "q /M gs Q 0 0 1 1 re f").items[1]?.bind fillOf).map (·.smask)
  == some none
#guard ((run grpDoc grpRes "/M gs /N gs 0 0 1 1 re f").items[1]?.bind fillOf).map (·.smask)
  == some none
#guard (run grpDoc grpRes "/M gs").warnings == 0
#guard (run grpDoc grpRes "/M gs").forms == 1
-- a mask group that cannot be expanded: one warning, no mask
#guard kinds (run grpDoc grpRes "/B gs 0 0 1 1 re f") == ["fillPath"]
#guard (run grpDoc grpRes "/B gs").warnings == 1
#guard (run grpDoc grpRes "/M gs" { maxXObjectDepth := 0 }).warnings == 1
-- font identity (6.7a): `Tf` resolved in the current frame; ExtGState `/Font`
private def fontOf : DisplayItem → Option FontRef
  | .glyphRun r _ => some r.font
  | _ => none
private def fontDoc : List (Nat × IndirectBody) :=
  [(6, strm "<< /Subtype /Form /BBox [0 0 1 1] /Resources << /Font << /F1 21 0 R >> >> >>"
     "BT /F1 9 Tf (x) Tj ET"),
   (7, strm "<< /Subtype /Form /BBox [0 0 1 1] /Resources << /Font << /F1 << /Subtype /Type1 >> >> >> >>"
     "BT /F1 9 Tf (x) Tj ET"),
   (8, strm "<< /Subtype /Form /BBox [0 0 1 1] /Resources << /Font << /F1 23 0 R >> >> >>"
     "BT (y) Tj ET"),
   (9, strm "<< /Subtype /Form /BBox [0 0 1 1] >>" "BT /F2 5 Tf (z) Tj ET")]
private def fontRes : String :=
  "<< /Font << /F1 20 0 R /F2 << /Subtype /Type1 >> >> " ++
  "/XObject << /A 6 0 R /B 7 0 R /C 8 0 R /D 9 0 R >> /ExtGState << /G << /Font [22 0 R 7] >> >> >>"
private def fontsIn (c : String) : List FontRef :=
  (run fontDoc fontRes c).items.toList.filterMap fontOf
#guard (fontsIn "BT /F1 12 Tf (a) Tj ET").map (·.id) == [.ref 20 0]
#guard (fontsIn "BT /F2 12 Tf (a) Tj ET").map (·.id) == [.res 0]
#guard (fontsIn "/A Do BT /F1 12 Tf (a) Tj ET").map (·.id) == [.ref 21 0, .ref 20 0]
#guard (fontsIn "/B Do").map (·.id) == [.res 7]
-- a font selected before a form keeps its identity inside it (form 8 has its own /F1)
#guard (fontsIn "/F1 12 Tf /C Do").map (·.id) == [.ref 20 0]
-- a form without /Resources resolves in the invoking content's frame
#guard (fontsIn "/D Do").map (·.id) == [.res 0]
#guard (fontsIn "BT /G gs (a) Tj ET").map (fun f => (f.id, f.size)) == [(.ref 22 0, fi 7)]
#guard (run fontDoc fontRes "BT /G gs (a) Tj ET").warnings == 0
#guard (run [] "<< /ExtGState << /G << /Font [<< >> 7] >> >> >>" "/G gs").warnings == 1
-- named colour spaces
private def csDoc : List (Nat × IndirectBody) :=
  [(10, strm "<< /N 3 /Alternate /DeviceRGB >>" ""),
   (11, strm "<< /N 4 >>" "")]
private def csRes : String :=
  "<< /ColorSpace << /Ix [/Indexed /DeviceRGB 1 <000000FF0000>] " ++
  "/Sp [/Separation /Spot /DeviceCMYK << /FunctionType 2 /Domain [0 1] /C0 [0 0 0 0] /C1 [0 1 0 0] /N 1 >>] " ++
  "/Sp4 [/Separation /Spot /DeviceRGB 12 0 R] /Dn [/DeviceN [/A /B] /DeviceCMYK 12 0 R] " ++
  "/Icc [/ICCBased 10 0 R] /Icc4 [/ICCBased 11 0 R] /L [/Lab << /WhitePoint [1 1 1] >>] >> >>"
private def fillCol (cs : String) : Option Color :=
  ((run csDoc csRes (cs ++ " 0 0 1 1 re f")).items[0]?.bind fillOf).map (·.color)
#guard fillCol "/Ix cs 1 sc" == some (.rgb Comp.one Comp.zero Comp.zero)
#guard fillCol "/Ix cs" == some (.rgb Comp.zero Comp.zero Comp.zero)
#guard fillCol "/Ix cs 7 sc" == some (.rgb Comp.one Comp.zero Comp.zero)  -- clamped to hival
#guard fillCol "/Sp cs 0.5 sc" ==
  some (.cmyk Comp.zero (Comp.ofFixed (Fixed.ofDecimal ⟨5, 1⟩)) Comp.zero Comp.zero)
#guard fillCol "/Sp cs" == some (.cmyk Comp.zero Comp.one Comp.zero Comp.zero)  -- tint 1
#guard fillCol "/Sp4 cs 0.25 scn" ==
  some (.rgb (Comp.ofFixed (Fixed.ofDecimal ⟨75, 2⟩)) (Comp.ofFixed (Fixed.ofDecimal ⟨75, 2⟩))
    (Comp.ofFixed (Fixed.ofDecimal ⟨75, 2⟩)))
#guard fillCol "/Dn cs 1 0 scn" ==
  some (.cmyk Comp.zero Comp.zero Comp.zero (Comp.ofFixed (Fixed.ofDecimal ⟨5, 1⟩)))
#guard fillCol "/Icc cs 1 0 0 sc" == some (.rgb Comp.one Comp.zero Comp.zero)
#guard fillCol "/Icc4 cs" == some (.cmyk Comp.zero Comp.zero Comp.zero Comp.zero)
#guard fillCol "/L cs 50 0 0 sc" ==
  some (.rgb (Comp.ofFixed (Fixed.ofDecimal ⟨5, 1⟩)) (Comp.ofFixed (Fixed.ofDecimal ⟨5, 1⟩))
    (Comp.ofFixed (Fixed.ofDecimal ⟨5, 1⟩)))
#guard (run csDoc csRes "/Dn cs 1 scn").warnings == 1   -- too few operands
#guard (run csDoc csRes "/Nope cs 1 sc").warnings == 1  -- unresolved: 5.2a fallback
#guard (run csDoc csRes "/Ix CS 1 SC 0 0 1 1 re S").warnings == 0
-- everything else is exec: the resource-free core is unchanged
#guard kinds (run [] "<< >>" "0 0 1 1 re f 1 2 foo") == ["fillPath", "unsupported"]
#guard (run [] "<< >>" "0 0 1 1 re f 1 2 foo").unsupported == 1
-- inline images come through exec with expanded abbreviations
#guard (match (run [] "<< >>" "BI /W 1 /H 1 /CS /G /BPC 8 ID x EI").items[0]? with
  | some (DisplayItem.image (.inline d data) _ _ _) =>
    Dict.get? d (Name.ofString "ColorSpace") == some (.name (Name.ofString "DeviceGray")) &&
      data.size == 1
  | _ => false)
-- resource annotation (7.3f): `sh`, pattern uses and inline colour spaces resolved in the
-- frame that emits them; the pattern base matrix is the form's start CTM
private def annDoc : List (Nat × IndirectBody) :=
  [(30, strm ("<< /Subtype /Form /BBox [0 0 10 10] /Matrix [2 0 0 2 0 0] /Resources << " ++
      "/Shading << /S1 40 0 R /S2 << /ShadingType 2 >> >> /Pattern << /P1 41 0 R >> " ++
      "/ColorSpace << /Ix [/Indexed /DeviceRGB 1 <000000FF0000>] >> >> >>")
     "/S1 sh /S2 sh /Pattern cs /P1 scn 0 0 1 1 re f BI /W 1 /H 1 /CS /Ix /BPC 8 ID x EI"),
   (31, strm "<< /Subtype /Form /BBox [0 0 10 10] >>" "/S0 sh /Pattern CS /P0 SCN 0 0 1 1 re S"),
   (32, strm "<< /Subtype /Form /BBox [0 0 10 10] >>" "0 0 1 1 re S")]
private def annRes : String :=
  "<< /XObject << /Fm 30 0 R /Fn 31 0 R >> /Shading << /S0 << /ShadingType 2 >> >> " ++
  "/Pattern << /P0 42 0 R >> >>"
private def annItems : List DisplayItem := (run annDoc annRes "1 0 0 1 5 5 cm /Fm Do /S0 sh").items.toList
private def shRes : DisplayItem → Option ResRef
  | .shading _ r _ _ _ => some r
  | _ => none
#guard annItems.filterMap shRes == [.ref 40 0, .form 30 0, .page]
#guard (annItems.filterMap fillOf).map (·.pattern) ==
  [some { res := .ref 41 0, base := ⟨fi 2, fi 0, fi 0, fi 2, fi 5, fi 5⟩ }]
#guard annItems.any fun
  | .image (.inline d _) _ _ _ => (Dict.get? d (nm "ColorSpace")).isSome &&
      (match Dict.get? d (nm "ColorSpace") with
       | some o => ((csInfo Source.empty () o).1.map (·.color [fi 1])) ==
           some (.rgb Comp.one Comp.zero Comp.zero)
       | none => false)
  | _ => false
-- a form without its own resources resolves in the page's; strokes record the use too
#guard ((run annDoc annRes "/Fn Do").items.toList.filterMap shRes) == [.page]
#guard ((run annDoc annRes "/Fn Do").items.toList.filterMap strokeOf).map (·.pattern) ==
  [some { res := .ref 42 0, base := Matrix.identity }]
-- uncoloured patterns: the `scn` colour operands in the underlying space
private def uRes : String :=
  "<< /ColorSpace << /PCS [/Pattern /DeviceRGB] /PIx [/Pattern [/Indexed /DeviceRGB 1 <000000FF0000>]] >> " ++
  "/Pattern << /P0 42 0 R >> >>"
private def underOfRun (c : String) : List (Option Color) :=
  ((run [] uRes c).items.toList.filterMap fillOf).map fun f => f.pattern.bind (·.under)
#guard underOfRun "/PCS cs 1 0 0 /P0 scn 0 0 1 1 re f" == [some (.rgb Comp.one Comp.zero Comp.zero)]
#guard underOfRun "/PIx cs 1 /P0 scn 0 0 1 1 re f" == [some (.rgb Comp.one Comp.zero Comp.zero)]
#guard underOfRun "/Pattern cs 1 /P0 scn 0 0 1 1 re f" == [some (.gray Comp.one)]
#guard underOfRun "/PCS cs /P0 scn 0 0 1 1 re f" == [none]
-- the underlying colour is inherited by a form
#guard ((run annDoc ("<< /XObject << /Fn 32 0 R >> /ColorSpace << /PCS [/Pattern /DeviceRGB] >> " ++
    "/Pattern << /P0 42 0 R >> /Shading << /S0 1 0 R >> >>") "/PCS CS 0 1 0 /P0 SCN /Fn Do").items.toList.filterMap
    strokeOf).map (fun k => k.pattern.bind (·.under)) == [some (.rgb Comp.zero Comp.one Comp.zero)]
-- the consumer side: `resLookup`
#guard ((resLookup (mkSrc annDoc) () [] "Shading" (.form 30 0) (nm "S2")).1.map fun
  | .dict _ => true | _ => false) == some true
#guard (resLookup (mkSrc annDoc) () [] "Shading" (.ref 40 0) (nm "S1")).1.isSome
-- non-pattern colours record nothing
#guard ((run [] "<< >>" "0 0 1 1 re f").items.toList.filterMap fillOf).map (·.pattern) == [none]
-- `CSInfo.toObj` resolves, without document access, to the same colours
private def csRound (i : CSInfo) (xs : List Fixed) : Bool :=
  (csInfo Source.empty () i.toObj).1.map (·.color xs) == some (i.color xs)
#guard csRound (.dev .rgb (.rgb Comp.zero Comp.zero Comp.zero)) [fi 1, fi 0, fi 0]
#guard csRound (.indexed .rgb 1 ⟨#[0, 0, 0, 255, 0, 0]⟩) [fi 1]
#guard csRound (.separation .cmyk (some ⟨[fi 0, fi 0, fi 0, fi 0], [fi 0, fi 1, fi 0, fi 0], 1⟩))
  [Fixed.ofDecimal ⟨5, 1⟩]
#guard csRound (.separation .gray none) [Fixed.ofDecimal ⟨25, 2⟩]
#guard csRound (.deviceN 2 .cmyk) [fi 1, fi 0]
#guard csRound .lab [fi 50, fi 0, fi 0]

end Tests

end SafePdf.Core.Content
