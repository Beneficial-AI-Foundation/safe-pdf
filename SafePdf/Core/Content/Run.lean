import SafePdf.Core.Content.Interp

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
  form does (unbalanced `q`, open text object, pending `W`) leaks out. Transparency groups,
  `/OC` and `/Ref` are ignored.
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
  `Env.maxForms` (default `defaultMaxForms` = 100,000) forms are expanded per page; further
  form `Do`s are skipped with a warning (an interim constant: `Limits` has no such field).
* **`Do` on an image** (`/Subtype /Image`): `DisplayItem.image (.xobject name num gen)` with the
  CTM (the unit square), the fill snapshot (stencil masks, §8.9.6.2) and the clip. The image
  data is **not** decoded (rendering is phase 7); its dictionary is summarised by consumers.
  `/Subtype /PS` is ignored silently (§8.8.2); a missing or malformed XObject is a warning.
* **Inline images** are executed by `exec` (an `.inline dict data` item); `Ops.tokenize` has
  already expanded the dictionary's abbreviations and sliced the data.
* **`gs`** (§8.4.5, Table 57): `/LW`, `/LC`, `/LJ`, `/ML`, `/D`, `/RI`, `/CA`, `/ca` are
  applied to the graphics state (what the display list carries). Ignored, documented: `/Font`
  (the display list's `FontRef` names a `/Font` *resource*, an ExtGState font is an indirect
  font dictionary: phase 6), `/SMask`, `/BM`, `/AIS`, `/TK`, `/OP`, `/op`, `/OPM`, `/BG`,
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

/-- A source with no objects (resource-free runs and tests). -/
def Source.empty : Source Unit :=
  ⟨fun s _ _ => (.error (.malformed 0 "no document"), s),
   fun s _ _ => (.error (.malformed 0 "no document"), s)⟩

/-- Default cap on form expansions per page (interim constant of task 5.2b; `Limits` has no
such field yet). Without it a form tree without cycles, within the nesting fuel, that invokes
each child many times ("billion laughs": 16 children over 8 levels) runs until
`maxOpsPerPage` operators, i.e. millions of form decodes (≈ 30 s). With it the run stops
expanding after `defaultMaxForms` forms (each further form `Do` is skipped with a warning). -/
def defaultMaxForms : Nat := 100000

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
  /-- Maximum number of form expansions per page (see `defaultMaxForms`). -/
  maxForms : Nat := defaultMaxForms

/-- The resource context of the content being run. -/
structure Frame where
  /-- The current resource dictionary. -/
  res : Dict
  /-- Object numbers of the forms on the current nesting path (innermost first). -/
  visited : List Nat

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

/-- A number. -/
def numOf (o : PdfObject) : Option Fixed := num? o

/-- A list of numbers. -/
def numsOf : PdfObject → Option (List Fixed)
  | .array xs => xs.mapM num?
  | _ => none

/-! ## XObjects -/

/-- What a `Do` operand names. -/
inductive XObj where
  /-- A form XObject: object number, the stream. -/
  | form (num : Nat) (st : Stream)
  /-- An image XObject. -/
  | image (num gen : Nat) (dict : Dict)
  /-- A PostScript XObject (ignored, §8.8.2). -/
  | ignored
  /-- Not found, not a stream, or an unknown subtype. -/
  | missing

/-- Look up and classify XObject `name`. -/
def xobjectOf {σ : Type} (src : Source σ) (s : σ) (res : Dict) (name : Name) : XObj × σ :=
  match resEntry src s res "XObject" name with
  | (some (.ref n g), s) =>
    match src.fetch s n g with
    | (.ok (.stream st), s) =>
      match Dict.get? st.dict (nm "Subtype") with
      | some (.name t) =>
        if t = nm "Form" then (.form n st, s)
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

/-- A form's resources: its own `/Resources`, else the parent's. -/
def formResources {σ : Type} (src : Source σ) (s : σ) (d : Dict) (parent : Dict) :
    Dict × σ :=
  match Dict.get? d (nm "Resources") with
  | none => (parent, s)
  | some o =>
    match resolve src s o with
    | (.dict r, s) => (r, s)
    | (_, s) => (parent, s)

/-! ## ExtGState (§8.4.5) -/

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
  else (g, 0)

/-- Keys `gsEntry` applies (others are ignored without resolving their values). -/
def gsKeys : List String := ["LW", "LC", "LJ", "ML", "D", "RI", "CA", "ca"]

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

/-- A base or alternate space that must be a device space after fallback (`ICCBased`,
`CalGray`, `CalRGB`, device names, one-element arrays). -/
def baseDevice {σ : Type} (src : Source σ) (s : σ) (o : PdfObject) : Option DeviceSpace × σ :=
  match resolve src s o with
  | (.name n, s) => (deviceOfName n, s)
  | (.array [.name n], s) => (deviceOfName n, s)
  | (.array [.name f, a], s) =>
    if f = nm "ICCBased" then
      let (d, s) := dictOf src s a
      (iccDevice d, s)
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
        let (d, s) := dictOf src s a
        match iccDevice d with
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
def namedCS {σ : Type} (src : Source σ) (s : σ) (res : Dict) (name : Name) :
    Option CSInfo × σ :=
  match resEntry src s res "ColorSpace" name with
  | (some o, s) => csInfo src s o
  | (none, s) => (none, s)

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
    match resEntry src s fr.res "ExtGState" n with
    | (some o, s) =>
      match resolve src s o with
      | (.dict d, s) =>
        let (g, w, s) := applyExtGState src s d m.core.gs
        (withGs m g, [], w, 0, s)
      | (_, s) => (m, [], 1, 0, s)
    | (none, s) => (m, [], 1, 0, s)

/-- `CS`/`cs`: a resource name is resolved; device names and `Pattern` go to `exec`. -/
def csStep {σ ω : Type} (env : Env σ ω) (fr : Frame) (stroke : Bool) (m : Machine) (s : σ)
    (op : Op) : Local σ :=
  match lastName? op.operands with
  | some n =>
    match spaceOfName n with
    | .other .. =>
      match namedCS env.src s fr.res n with
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
      match namedCS env.src s fr.res key with
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

/-- Every operator but `Do`. -/
def localStep {σ ω : Type} (env : Env σ ω) (fr : Frame) (m : Machine) (s : σ) (op : Op) :
    Local σ :=
  match op.op with
  | [103, 115] => gsStep env.src fr m s op          -- gs
  | [67, 83] => csStep env fr true m s op           -- CS
  | [99, 115] => csStep env fr false m s op         -- cs
  | [83, 67] => scStep env fr true m s op           -- SC
  | [83, 67, 78] => scStep env fr true m s op       -- SCN
  | [115, 99] => scStep env fr false m s op         -- sc
  | [115, 99, 110] => scStep env fr false m s op    -- scn
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
  /-- Graphics state at the start of the form. -/
  gs : GState
  /-- The `/BBox` clip, page space. -/
  clip : Option Path
  /-- Warnings (a missing or malformed `/BBox`). -/
  w : Nat

/-- What `Do` does, before any nesting. -/
inductive DoOut (σ : Type) where
  /-- Finished: an optional item (an image), warnings, source state; the machine is
  unchanged. -/
  | done (it : Option DisplayItem) (w : Nat) (s : σ)
  /-- Expand a form. -/
  | form (job : FormJob) (s : σ)

/-- Prepare form `n` (dictionary `d`, decoded content `bytes`). -/
def formJob {σ ω : Type} (env : Env σ ω) (fr : Frame) (m : Machine) (n : Nat) (d : Dict)
    (bytes : ByteArray) (s : σ) : DoOut σ :=
  let t := Ops.tokenize env.cfg.limits bytes
  let r := formResources env.src s d fr.res
  let gs := m.core.gs
  let ctm := Matrix.mul (formMatrix d) gs.ctm
  match bboxOf d with
  | some (x0, y0, x1, y1) =>
    let path := rectPath ctm x0 y0 x1 y1
    .form ⟨n, t.ops, t.warnings, r.1, { gs with ctm, clip := ⟨path, .nonzero⟩ :: gs.clip },
      some path, 0⟩ r.2
  | none => .form ⟨n, t.ops, t.warnings, r.1, { gs with ctm }, none, 1⟩ r.2

/-- `formJob` prepares form `n`. -/
theorem formJob_num {σ ω : Type} {env : Env σ ω} {fr : Frame} {m : Machine} {n : Nat}
    {d : Dict} {bytes : ByteArray} {s : σ} {job : FormJob} {s' : σ}
    (h : formJob env fr m n d bytes s = .form job s') : job.num = n := by
  unfold formJob at h
  split at h <;> (cases h; rfl)

/-- `Do /Name` (`nest`: fuel is left for a form). -/
def doStep {σ ω : Type} (env : Env σ ω) (nest : Bool) (fr : Frame) (m : Machine) (s : σ)
    (op : Op) : DoOut σ :=
  match lastName? op.operands with
  | none => .done none 1 s
  | some name =>
    match xobjectOf env.src s fr.res name with
    | (.missing, s) => .done none 1 s
    | (.ignored, s) => .done none 0 s
    | (.image n g _, s) =>
      .done (some (.image (.xobject name n g) m.core.gs.ctm m.core.gs.fillStyle m.core.gs.clip))
        0 s
    | (.form n st, s) =>
      if fr.visited.contains n then .done none 1 s
      else if nest then
        match env.src.decode s n st with
        | (.error _, s) => .done none 1 s
        | (.ok bytes, s) => formJob env fr m n st.dict bytes s
      else .done none 1 s

/-- The machine a form runs in: the given graphics state, everything else fresh. -/
def formMachine (gs : GState) : Machine := ⟨{ gs }, {}, none⟩

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
          match run ⟨job.res, job.num :: fr.visited⟩
              ⟨formMachine job.gs, pushAll items (job.clip.toList.map (.clip · .nonzero)),
                warnings + w, unsupported, ops + 1, forms + 1, truncated, s',
                env.observe obs op w 0⟩ job.ops with
          | ⟨_, items2, w2, u2, ops2, forms2, tr2, s2, obs2⟩ =>
            ⟨m, items2, w2, u2, ops2, forms2, tr2, s2, obs2⟩
        | none =>
          ⟨m, items, warnings + 1, unsupported, ops + 1, forms, truncated, s',
            env.observe obs op 1 0⟩
    else
      match localStep env fr m s op with
      | (m', its, w, u, s') =>
        ⟨m', pushAll items its, warnings + w, unsupported + u, ops + 1, forms, truncated, s',
          env.observe obs op w u⟩

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
  · split at h
    · cases h
    · cases h
    · cases h
    · rename_i n' st s1 _
      by_cases hv : fr.visited.contains n' = true
      · simp only [hv, ↓reduceIte] at h; cases h
      · cases nest
        · simp only [hv, Bool.false_eq_true, ↓reduceIte] at h; cases h
        · simp only [hv, Bool.false_eq_true, ↓reduceIte] at h
          split at h
          · cases h
          · rw [formJob_num h]
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
  · exact hcs true s
  · exact hcs false s
  · exact hsc true s
  · exact hsc true s
  · exact hsc false s
  · exact hsc false s
  · exact viaExec_bound env.cfg m s op

/-- The bound invariant with slack `k`: items, plus `1` for a pending clip, plus `k`, are at
most `Paint.maxItems` per executed operator; and at most `maxOpsPerPage` operators ran. -/
def Good {σ ω : Type} (lim : Limits) (k : Nat) (st : St σ ω) : Prop :=
  st.items.size + pendBit st.m + k ≤ Paint.maxItems * st.ops ∧ st.ops ≤ lim.maxOpsPerPage

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
          have hcl : (job.clip.toList.map (DisplayItem.clip · FillRule.nonzero)).length ≤ 1 := by
            cases job.clip <;> simp
          have h1 : Good env.cfg.limits (pendBit m + k)
              ⟨formMachine job.gs, pushAll items (job.clip.toList.map (.clip · .nonzero)),
                warnings + (job.w + job.tokW), unsupported, ops + 1, forms + 1, truncated, s',
                env.observe obs op (job.w + job.tokW) 0⟩ := by
            unfold Good
            simp only [size_pushAll, formMachine, pendBit, Option.isSome_none,
              Bool.false_eq_true, ↓reduceIte, Paint.maxItems] at h hcl ⊢
            omega
          have h2 := hin run hrun (pendBit m + k) ⟨job.res, job.num :: fr.visited⟩ _ job.ops h1
          revert h2
          rcases run ⟨job.res, job.num :: fr.visited⟩
              ⟨formMachine job.gs, pushAll items (job.clip.toList.map (.clip · .nonzero)),
                warnings + (job.w + job.tokW), unsupported, ops + 1, forms + 1, truncated, s',
                env.observe obs op (job.w + job.tokW) 0⟩ job.ops with
            ⟨m2, items2, w2, u2, ops2, forms2, tr2, s2, obs2⟩
          intro h2
          unfold Good at h2
          simp only at h2 ⊢
          omega
    · -- every other operator
      have hb := localStep_bound env fr m s op
      revert hb
      rcases localStep env fr m s op with ⟨m', its, w, u, s'⟩
      intro hb
      simp only [size_pushAll, Paint.maxItems] at h hb ⊢
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

end Run

open Run

/-- The initial runner state. -/
def St.init {σ ω : Type} (s : σ) (obs : ω) : St σ ω :=
  ⟨{}, #[], 0, 0, 0, 0, false, s, obs⟩

/-- **Entry point.** Run a page's tokenized content with its resources: nesting fuel
`Limits.maxXObjectDepth`, from the initial machine. Total; never fails. -/
def runPage {σ ω : Type} (env : Env σ ω) (res : Dict) (ops : Array Op) (s : σ) (obs : ω) :
    St σ ω :=
  Run.runOps env env.cfg.limits.maxXObjectDepth ⟨res, []⟩ (St.init s obs) ops

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

/-- **Operator bound**: at most `Limits.maxOpsPerPage` operators are executed, page and forms
together, however the forms nest. -/
theorem runPage_ops_le {σ ω : Type} (env : Env σ ω) (res : Dict) (ops : Array Op) (s : σ)
    (obs : ω) : (runPage env res ops s obs).ops ≤ env.cfg.limits.maxOpsPerPage :=
  (runOps_good env _ 0 _ _ ops (St.init_good _ s obs)).2

/-- **Item bound** (generalises `interp_items_le` to forms): at most `Paint.maxItems` items per
executed operator. -/
theorem runPage_items_le {σ ω : Type} (env : Env σ ω) (res : Dict) (ops : Array Op) (s : σ)
    (obs : ω) :
    (runPage env res ops s obs).items.size ≤
      Paint.maxItems * (runPage env res ops s obs).ops := by
  have := (runOps_good env env.cfg.limits.maxXObjectDepth 0 ⟨res, []⟩ (St.init s obs) ops
    (St.init_good _ s obs)).1
  unfold runPage
  omega

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

end Tests

end SafePdf.Core.Content
