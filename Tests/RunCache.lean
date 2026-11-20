import SafePdf.Core.Content.Run
import SafePdf.Core.Filter
import SafePdf.Core.Filter.Deflate
import SafePdf.Core.ObjParse

/-!
# Per-page form cache suite (task 7.9b)

Plan.md §6 Phase 7 (render time, M7/M8), §5.2 (bounded work). `Core.Content.runPage` runs a
page with `Run.FormCache.env`: each form (and soft-mask group) is decoded and tokenized once
per page run. The cache's invariants (genuine entries, count and byte bounds) are fields of
`Run.FormCache`; `FormCache.code_ok`, `code_hit`, `code_miss`, `code_fst_eq` are theorems.
This suite checks by evaluation, against `runPageUncached` (the runner without the cache):

* one Flate form drawn 2,000 times under a real document budget (`Filter.decodeStreamB`):
  identical display list, warnings, operator and form counts; the budget is charged once
  instead of 2,000 times;
* a counting source (state = number of decodes): three forms used alternately are decoded
  3 times with the default limits, `2 + uses of the third` times with
  `maxFormCacheEntries = 2`, every time with `maxFormCacheBytes = 0` (the bound), output
  identical in all cases;
* nested forms and a soft-mask group used many times: decoded once each, output identical;
* the cache key includes the stream: a source whose fetch returns a different stream for the
  same object number depending on its state gives the same output as without the cache;
* the documented charging change: with a budget that pays for only 3 decodes, the uncached
  run draws 3 forms and warns for the rest, the cached run draws all of them;
* timing of 20,000 `Do`s of one Flate form, cached and uncached (printed).
-/

namespace SafePdf.Tests.RunCache

open SafePdf.Core
open SafePdf.Core.Content

/-- A parsed object. -/
def obj (s : String) : PdfObject :=
  match ObjParse.parseObject {} s.toUTF8 0 with
  | .ok (o, _) => o
  | .error _ => .null

/-- A parsed dictionary. -/
def dictS (s : String) : Dict :=
  match obj s with
  | .dict d => d
  | _ => []

/-- A stream object with dictionary `d` and data `data`. -/
def strm (d : String) (data : ByteArray) : IndirectBody := .stream ⟨dictS d, data⟩

/-- Fetch from a table (any state). -/
def fetchTbl {σ : Type} (objs : List (Nat × IndirectBody)) (s : σ) (n _g : Nat) :
    (Except Error IndirectBody) × σ :=
  match objs.lookup n with
  | some b => (.ok b, s)
  | none => (.error (.malformed 0 "missing"), s)

/-- A source over a table whose decodes run the filters under a document budget. -/
def budgetSrc (lim : Limits) (objs : List (Nat × IndirectBody)) : Source Filter.Budget :=
  ⟨fetchTbl objs,
   fun b _ st =>
     match Filter.decodeStreamB lim b st.dict st.data with
     | (.ok (.data bytes), b) => (.ok bytes, b)
     | (.ok (.image ..), b) => (.error (.unsupported "image"), b)
     | (.error e, b) => (.error e, b)⟩

/-- A source over a table that counts its decodes (data unfiltered). -/
def countSrc (objs : List (Nat × IndirectBody)) : Source Nat :=
  ⟨fetchTbl objs, fun k _ st => (.ok st.data, k + 1)⟩

/-- A runner environment. -/
def mkEnv {σ : Type} (lim : Limits) (src : Source σ) : Env σ Unit :=
  { cfg := { limits := lim }, src, observe := fun u _ _ _ => u }

/-- Run with and without the cache. -/
def both {σ : Type} (lim : Limits) (src : Source σ) (res content : String) (s : σ) :
    St σ Unit × St σ Unit :=
  let ops := (Ops.tokenize lim content.toUTF8).ops
  (runPage (mkEnv lim src) (dictS res) ops s (),
   runPageUncached (mkEnv lim src) (dictS res) ops s ())

/-- Equality of image sources. -/
def srcEq : ImageSource → ImageSource → Bool
  | .xobject a b c, .xobject a' b' c' => decide (a = a' ∧ b = b' ∧ c = c')
  | .inline a b, .inline a' b' => decide (a = a' ∧ b = b')
  | _, _ => false

/-- Equality of display items other than soft masks (`DisplayItem` has no `DecidableEq`: it
is a nested inductive). -/
def shallowEq : DisplayItem → DisplayItem → Bool
  | .fillPath a b c d, .fillPath a' b' c' d' => decide (a = a' ∧ b = b' ∧ c = c' ∧ d = d')
  | .strokePath a b c, .strokePath a' b' c' => decide (a = a' ∧ b = b' ∧ c = c')
  | .clip a b, .clip a' b' => decide (a = a' ∧ b = b')
  | .glyphRun a b, .glyphRun a' b' => decide (a = a' ∧ b = b')
  | .image a b c d, .image a' b' c' d' => srcEq a a' && decide (b = b' ∧ c = c' ∧ d = d')
  | .shading a b c d e, .shading a' b' c' d' e' =>
    decide (a = a' ∧ b = b' ∧ c = c' ∧ d = d' ∧ e = e')
  | .unsupported a, .unsupported a' => decide (a = a')
  | .groupBegin a, .groupBegin a' => decide (a = a')
  | .groupEnd, .groupEnd => true
  | .actualTextBegin a, .actualTextBegin a' => decide (a = a')
  | .actualTextEnd, .actualTextEnd => true
  | _, _ => false

/-- Equality of display items, soft masks compared to `fuel` levels. -/
def itemEq : Nat → DisplayItem → DisplayItem → Bool
  | 0, _, _ => false
  | f + 1, .softMask i a xs, .softMask j b ys =>
    i == j && decide (a = b) && xs.size == ys.size &&
      (xs.toList.zip ys.toList).all fun p => itemEq f p.1 p.2
  | _ + 1, x, y => shallowEq x y

/-- Same display list, warnings, counts. -/
def same {σ : Type} (a b : St σ Unit) : Bool :=
  a.items.size == b.items.size &&
    (a.items.toList.zip b.items.toList).all (fun p => itemEq 64 p.1 p.2) && a.warnings == b.warnings && a.ops == b.ops &&
    a.forms == b.forms && a.unsupported == b.unsupported && a.truncated == b.truncated

/-- `k` copies of `s`. -/
def rep (k : Nat) (s : String) : String := String.join (List.replicate k s)

/-- The marker form's content. -/
def markerContent : String := "0.5 g 0 0 m 4 0 l 4 4 l h B 1 0 0 1 2 2 cm 0 0 1 1 re f"

/-- A document with one Flate-compressed marker form (object 6). -/
def flateDoc : List (Nat × IndirectBody) :=
  [(6, strm "<< /Type /XObject /Subtype /Form /BBox [0 0 10 10] /Filter /FlateDecode >>"
    (Filter.Deflate.zlibFixed markerContent.toUTF8))]

/-- Page resources naming forms 6, 7, 8 and an ExtGState with a soft mask (group 9). -/
def res : String :=
  "<< /XObject << /Fm 6 0 R /Fa 7 0 R /Fb 8 0 R >> " ++
  "/ExtGState << /G1 << /SMask << /S /Luminosity /G 9 0 R >> >> >> >>"

/-- The suite. -/
def run : IO Nat := do
  let mut failures := 0
  let report := fun (msg : String) => IO.println s!"  FAIL run-cache: {msg}"
  -- 1. One Flate form 2,000 times, under a document budget.
  let lim : Limits := {}
  let size := markerContent.toUTF8.size
  let content := rep 2000 "q 1 0 0 1 3 3 cm /Fm Do Q "
  let (c, u) := both lim (budgetSrc lim flateDoc) res content (Filter.Budget.init lim)
  if !same c u then failures := failures + 1; report "flate form: output differs"
  if c.forms != 2000 || c.items.size < 2000 then
    failures := failures + 1; report s!"flate form: {c.forms} forms, {c.items.size} items"
  -- charged once (cached) vs 2,000 times (uncached)
  if lim.maxDecodedTotalBytes - c.s.remaining != size ||
      lim.maxDecodedTotalBytes - u.s.remaining != 2000 * size then
    failures := failures + 1
    report s!"flate form: charged {lim.maxDecodedTotalBytes - c.s.remaining} / {lim.maxDecodedTotalBytes - u.s.remaining}"
  -- 2. Three forms used alternately; the count and byte bounds.
  let three : List (Nat × IndirectBody) :=
    [(6, strm "<< /Subtype /Form /BBox [0 0 10 10] >>" "0 0 1 1 re f".toUTF8),
     (7, strm "<< /Subtype /Form >>" "1 0 0 RG 0 0 m 5 5 l S".toUTF8),
     (8, strm "<< /Subtype /Form /Matrix [2 0 0 2 0 0] >>" "0 0 3 3 re f".toUTF8)]
  let alt := rep 10 "/Fm Do /Fa Do /Fb Do "
  for (name, l, want) in [("default", ({} : Limits), 3),
      ("2 entries", { maxFormCacheEntries := 2 }, 2 + 10),
      ("0 bytes", { maxFormCacheBytes := 0 }, 30),
      ("0 entries", { maxFormCacheEntries := 0 }, 30)] do
    let (c, u) := both l (countSrc three) res alt 0
    if !same c u then failures := failures + 1; report s!"three forms ({name}): output differs"
    if c.s != want || u.s != 30 then
      failures := failures + 1; report s!"three forms ({name}): {c.s} / {u.s} decodes, want {want} / 30"
  -- 3. Nested forms (7 invokes 8 twice), and a soft-mask group, used many times.
  let nested : List (Nat × IndirectBody) :=
    [(7, strm "<< /Subtype /Form /Resources << /XObject << /In 8 0 R >> >> >>"
        "/In Do 1 0 0 1 5 0 cm /In Do".toUTF8),
     (8, strm "<< /Subtype /Form /BBox [0 0 4 4] >>" "0 0 4 4 re f".toUTF8),
     (9, strm "<< /Subtype /Form /Group << /S /Transparency >> /BBox [0 0 10 10] >>"
        "0.5 g 0 0 10 10 re f".toUTF8)]
  let (c, u) := both lim (countSrc nested) res (rep 25 "/Fa Do /G1 gs 0 0 2 2 re f ") 0
  if !same c u then failures := failures + 1; report "nested/soft mask: output differs"
  if c.s != 3 || u.s != 25 * 3 + 25 then
    failures := failures + 1; report s!"nested/soft mask: {c.s} / {u.s} decodes"
  -- 4. The key includes the stream: object 6 alternates between two streams (the state counts
  -- fetches; decoding leaves it alone, so both runs see the same fetches).
  let flip : Source Nat :=
    ⟨fun k n _ => if n = 6 then
        (.ok (strm "<< /Subtype /Form >>"
          (if k % 2 = 0 then "0 0 1 1 re f" else "0 0 2 2 re S").toUTF8), k + 1)
      else (.error (.malformed 0 "missing"), k),
     fun k _ st => (.ok st.data, k)⟩
  let (c, u) := both lim flip res (rep 6 "/Fm Do ") 0
  let strokes := c.items.toList.filter fun | .strokePath .. => true | _ => false
  if !same c u || strokes.length != 3 then
    failures := failures + 1; report s!"stream key: output differs ({strokes.length} strokes)"
  -- 5. Charging change (documented): a budget for three decodes only.
  let small : Filter.Budget := ⟨3 * size + size / 2⟩
  let (c, u) := both lim (budgetSrc lim flateDoc) res (rep 10 "/Fm Do ") small
  if c.forms != 10 || u.forms != 3 || u.warnings < 7 || c.warnings != 0 then
    failures := failures + 1
    report s!"budget: cached {c.forms} forms {c.warnings} warnings, uncached {u.forms} / {u.warnings}"
  -- 6. Timing: 20,000 Dos of the Flate form.
  let big := rep 20000 "/Fm Do "
  let ops := (Ops.tokenize lim big.toUTF8).ops
  let t0 ← IO.monoMsNow
  let c := runPage (mkEnv lim (budgetSrc lim flateDoc)) (dictS res) ops (Filter.Budget.init lim) ()
  let n0 := c.items.size
  let t1 ← IO.monoMsNow
  let u := runPageUncached (mkEnv lim (budgetSrc lim flateDoc)) (dictS res) ops
    (Filter.Budget.init lim) ()
  let n1 := u.items.size
  let t2 ← IO.monoMsNow
  if n0 != n1 then failures := failures + 1; report s!"timing run: {n0} vs {n1} items"
  IO.println s!"  run-cache: 20000 Do of a Flate form: cached {t1 - t0} ms, uncached {t2 - t1} ms"
  return failures

end SafePdf.Tests.RunCache
