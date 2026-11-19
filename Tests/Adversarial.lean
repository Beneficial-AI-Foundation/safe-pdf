import SafePdf

/-!
# Adversarial regression suite (task 2.7)

Plan.md §5.2 (last line: "Bogk & Schöpl's crafted DoS file and mutations of it become
permanent regression tests"), §7 item 3 ("All must fail *fast and cleanly*"), §6 Phase 2 M2
("Bogk-style cyclic files all rejected in bounded time").

For every `Tests/adversarial/*.pdf` the suite runs the Phase 2 entry points:

* `Core.Xref.Chain.loadChain` (the `/Prev` chain),
* `Repair.repair` and `Repair.scanObjects` (the repair scan),
* `Core.Open.openFile` (strict, else repair, cycles final), `OpenDoc.getObject` of every
  scanned object when it opens, and `SafePdf.parse` (task 2.13:
  the M2 clause "Bogk-style cyclic files all rejected" is checked on these two, the entry
  points a viewer uses; the cyclic files must fail with `Error.cycle`, not open repaired),
* `parseIndirectAt` at every `N G obj` offset found by `scanObjects`, and `parseObjectAt`
  at the body of each such object,
* for `length-*` files, `Core.Xref.Length.parseIndirectResolved` at every such offset, with a
  lookup built from `Chain.mergeChain` of `loadChain`'s revisions, or (when `loadChain` fails,
  e.g. on xref streams before task 2.4) from the repaired section.

Every call is timed with `IO.monoNanosNow`; the result is matched on before the clock is read
again, so the measurement covers the whole (strict) evaluation. A call over `callBoundNs`
(2 s) or a file (or mutation variant) over `fileBoundNs` (5 s) in total fails the suite.
Outcomes are checked against the table `expectations` (one row per file × entry point); an
entry point without a row must only terminate within the bounds. A row that is never
exercised (e.g. the scan no longer finds the object it names) is a failure too.

## Mutations (Plan.md §5.2 "mutations of it")

A deterministic set derived from the cyclic files, all length-preserving unless noted:

* `xref-prev-cycle.pdf`, `xref-prev-self.pdf`: each `/Prev` digit incremented (mod 10), the
  `/Prev` values swapped, each `/Prev` pointed at every xref offset, every object header,
  offsets inside objects, the trailers, `startxref`, `0`, the end of input and beyond;
  `startxref` pointed at every xref offset; each `/Prev` blanked out; `%%EOF` deleted;
  truncation at 25/50/75 %. A variant in which `startxref` and every `/Prev` point at an
  xref table (and every table has a `/Prev`) has no terminating revision, so `loadChain`
  must fail with an `Error.cycle` "xref /Prev cycle", and so must `openFile` (no repair);
  for the others any result is accepted (bounded time only).
* `length-self-ref.pdf`: the `/Length 4 0 R` reference renumbered to `k 0 R` (`k = 1..9`) and
  `4 1 R`; `parseIndirectResolved` of object 4 must fail with `Error.cycle` "cyclic /Length"
  exactly when `k = 4`.

Paths are relative to the current directory: run `lake exe tests` from the repo root.
-/

namespace SafePdf.Tests.Adversarial

open SafePdf SafePdf.Core.Xref

/-- Directory of the adversarial corpus. -/
def advDir : System.FilePath := "Tests" / "adversarial"

/-- Bound on a single entry-point call, in nanoseconds (2 s). -/
def callBoundNs : Nat := 2000000000

/-- Bound on all calls for one file or one mutation variant, in nanoseconds (5 s). -/
def fileBoundNs : Nat := 5000000000

/-! ## Rendering results -/

/-- An error as one line. -/
def errS : Error → String
  | .malformed o m => s!"malformed@{o}: {m}"
  | .limitExceeded k => s!"limitExceeded {reprStr k}"
  | .unsupported w => s!"unsupported: {w}"
  | .cycle o w => s!"cycle@{o}: {w}"

/-- An xref entry, compactly. -/
def entS : XrefEntry → String
  | .free n g => s!"f{n}/{g}"
  | .inUse o g => s!"@{o}/{g}"
  | .compressed s i => s!"c{s}#{i}"

/-- The entries of a section, compactly. -/
def entriesS (es : List (Nat × XrefEntry)) : String :=
  ",".intercalate (es.map fun (n, e) => s!"{n}:{entS e}")

/-- Summary of a `loadChain` result: revision offsets and the merged entries. -/
def chainS (revs : List Chain.Revision) : String :=
  s!"revs={revs.map Chain.Revision.offset} entries={entriesS (Chain.mergeChain revs).entries}"

/-- Summary of a `repair` result: the entries and the trailer root. -/
def repairS (r : XrefSection × Trailer) : String :=
  s!"entries={entriesS r.1.entries} root={r.2.root?}"

/-- Summary of an opened document: how it was opened and its size. -/
def openS (d : Core.Open.OpenDoc) : String :=
  s!"{if d.repaired then "repaired" else "strict"} revs={d.revisions} objects={d.objectCount}"

/-- Summary of a parsed document. -/
def docS (d : Document) : String :=
  s!"{if d.repaired then "repaired" else "strict"} root={d.root}"

/-- Summary of an indirect-object parse. -/
def indS (r : IndirectObject × Nat) : String :=
  s!"obj {r.1.num} {r.1.gen} end {r.2}"

/-- `true` iff `sub` (non-empty) occurs in `s`. -/
def hasSub (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- Nanoseconds as milliseconds with three decimals. -/
def fmtMs (ns : Nat) : String :=
  let us := ns / 1000
  let frac := toString (us % 1000)
  s!"{us / 1000}.{"".pushn '0' (3 - frac.length)}{frac} ms"

/-! ## Expectations -/

/-- The expected outcome of one entry point on one input. -/
inductive Expect where
  /-- Success, any value. -/
  | ok
  /-- Success with exactly this summary. -/
  | okEq (summary : String)
  /-- Any error. -/
  | err
  /-- An error whose rendering contains this text. -/
  | errMsg (sub : String)
  /-- `Error.limitExceeded` of this kind. -/
  | errLimit (k : LimitKind)
  /-- `Error.cycle` whose rendering contains this text (task 2.13). -/
  | errCycle (sub : String)
  /-- Any result: only termination within the time bounds is checked. -/
  | any

/-- Human-readable expectation. -/
def Expect.describe : Expect → String
  | .ok => "ok"
  | .okEq s => s!"ok {s}"
  | .err => "any error"
  | .errMsg s => s!"error containing \"{s}\""
  | .errLimit k => s!"limitExceeded {reprStr k}"
  | .errCycle s => s!"cycle error containing \"{s}\""
  | .any => "any result"

/-- Whether a summarised result meets the expectation. -/
def Expect.accepts : Expect → Except Error String → Bool
  | .ok, .ok _ => true
  | .okEq s, .ok t => s == t
  | .err, .error _ => true
  | .errMsg sub, .error e => hasSub (errS e) sub
  | .errLimit k, .error (.limitExceeded k') => k == k'
  | .errCycle sub, .error e@(.cycle _ _) => hasSub (errS e) sub
  | .any, _ => true
  | _, _ => false

/-- Merged / repaired entries of `minimal-valid.pdf`: the same offsets both ways. -/
def minimalEntries : String :=
  "0:f0/65535,1:@15/0,2:@64/0,3:@121/0,4:@247/0,5:@334/0"

/-- **The expected-outcomes table**: per file, `(entry point, expectation)`. Entry-point keys
are `loadChain`, `repair`, `scanObjects`, `openFile`, `parse`, `getObject obj N` (through
the opened document), `parseIndirectAt obj N`, `parseObjectAt obj N` and
`parseIndirectResolved obj N`. Missing rows mean `Expect.any`. -/
def expectations : String → List (String × Expect)
  | "minimal-valid.pdf" =>
    [("loadChain", .okEq s!"revs=[404] entries={minimalEntries}"),
     ("repair", .okEq s!"entries={minimalEntries} root=(some (1, 0))"),
     ("openFile", .okEq "strict revs=1 objects=6"), ("parse", .okEq "strict root=(1, 0)"),
     ("scanObjects",
      .okEq "[(1, (0, 15)), (2, (0, 64)), (3, (0, 121)), (4, (0, 247)), (5, (0, 334))]"),
     ("parseIndirectAt obj 1", .ok), ("parseIndirectAt obj 2", .ok),
     ("parseIndirectAt obj 3", .ok), ("parseIndirectAt obj 4", .ok),
     ("parseIndirectAt obj 5", .ok)]
  -- the Bogk & Schöpl hang: two tables whose /Prev point at each other. The strict path
  -- rejects it with a cycle error, which is final (task 2.13, M2): openFile and parse return
  -- it although the repair scan on its own would recover the objects.
  | "xref-prev-cycle.pdf" =>
    [("loadChain", .errCycle "xref /Prev cycle"), ("repair", .ok),
     ("openFile", .errCycle "xref /Prev cycle"), ("parse", .errCycle "xref /Prev cycle")]
  -- a cycle of length 1
  | "xref-prev-self.pdf" =>
    [("loadChain", .errCycle "xref /Prev cycle"), ("repair", .ok),
     ("openFile", .errCycle "xref /Prev cycle"), ("parse", .errCycle "xref /Prev cycle")]
  -- the plain object parser does not resolve indirect /Length (error); the resolving one
  -- detects the self-reference
  | "length-self-ref.pdf" =>
    [("loadChain", .ok), ("repair", .ok),
     ("parseIndirectAt obj 4", .err),
     ("parseIndirectResolved obj 4", .errCycle "cyclic /Length"),
     -- the root is sound, so the file opens strictly; the cycle is final where it is met:
     -- resolving object 4 (the page contents) through the opened document
     ("openFile", .okEq "strict revs=1 objects=6"), ("parse", .okEq "strict root=(1, 0)"),
     ("getObject obj 4", .errCycle "cyclic /Length")]
  -- The file's xref stream is structurally valid, so loadChain succeeds since task 2.4a;
  -- the attack is the /Length cycle 4 → 6 (in object stream 5) → stream 5 → 4, which only
  -- appears when objects are resolved: resolving object 4's /Length must fail.
  | "length-mutual.pdf" =>
    [("loadChain", .ok), ("repair", .ok),
     ("parseIndirectAt obj 4", .err), ("parseIndirectAt obj 5", .err),
     ("parseIndirectResolved obj 4", .err),
     -- opens strictly (the root is sound); resolving 4 or 5 fails. Not yet reported as a
     -- cycle: a /Length into an object stream is still `unsupported` in `Core.Xref.Length`.
     ("openFile", .okEq "strict revs=1 objects=8"), ("parse", .okEq "strict root=(1, 0)"),
     ("getObject obj 4", .err), ("getObject obj 5", .err)]
  -- Structure-level attacks for Phases 4/5 (page tree, XObject nesting): the xref and the
  -- root are sound, so the files open strictly; the cycles are for the page-tree and content
  -- layers to reject.
  | "pages-kids-cycle.pdf" =>
    [("openFile", .okEq "strict revs=1 objects=6"), ("parse", .okEq "strict root=(1, 0)")]
  | "xobject-recursive.pdf" =>
    [("openFile", .okEq "strict revs=1 objects=7"), ("parse", .okEq "strict root=(1, 0)")]
  -- xref stream whose entry places object 5 in object stream 5 (task 2.4a rejects it; a
  -- cycle error since task 2.13, so openFile and parse do not fall back to repair)
  | "objstm-self-container.pdf" =>
    [("loadChain", .errCycle "own object stream"), ("repair", .ok),
     ("openFile", .errCycle "own object stream"), ("parse", .errCycle "own object stream")]
  -- the 100,000-deep array must hit the depth limit, not the native stack
  | "deep-nesting.pdf" =>
    [("loadChain", .ok), ("repair", .ok),
     ("parseIndirectAt obj 6", .errLimit .objectDepth),
     ("parseObjectAt obj 6", .errLimit .objectDepth),
     ("openFile", .okEq "strict revs=1 objects=7"), ("parse", .okEq "strict root=(1, 0)"),
     ("getObject obj 6", .errLimit .objectDepth)]
  | _ => []

/-- The files the table is about; each must exist in the corpus. -/
def knownFiles : List String :=
  ["minimal-valid.pdf", "xref-prev-cycle.pdf", "xref-prev-self.pdf", "length-self-ref.pdf",
   "length-mutual.pdf", "pages-kids-cycle.pdf", "xobject-recursive.pdf",
   "objstm-self-container.pdf", "deep-nesting.pdf"]

/-! ## Timed calls -/

/-- Running totals for one file or variant group. -/
structure Acc where
  failures : Nat := 0
  calls : Nat := 0
  maxCallNs : Nat := 0
  totalNs : Nat := 0

/-- Run `f ()` between two clock readings; the result is matched on (hence fully evaluated,
Lean being strict) before the second reading. -/
@[noinline] def timeIt {α : Type} (f : Unit → Except Error α) : IO (Except Error α × Nat) := do
  let t0 ← IO.monoNanosNow
  match f () with
  | .ok v => do
    let t1 ← IO.monoNanosNow
    pure (.ok v, t1 - t0)
  | .error e => do
    let t1 ← IO.monoNanosNow
    pure (.error e, t1 - t0)

/-- Render a summarised result. -/
def showR : Except Error String → String
  | .ok s => s!"ok {s}"
  | .error e => s!"error {errS e}"

/-- Run one entry point, check its expectation and the per-call time bound, update `st`. -/
def call {α : Type} (st : IO.Ref Acc) (ctx entry : String) (exp : Expect) (summ : α → String)
    (f : Unit → Except Error α) : IO (Except Error α) := do
  let (r, ns) ← timeIt f
  let rs : Except Error String := match r with
    | .ok v => .ok (summ v)
    | .error e => .error e
  let mut bad := 0
  if !exp.accepts rs then
    IO.println s!"  FAIL {ctx} / {entry}: expected {exp.describe}, got {showR rs}"
    bad := bad + 1
  if ns > callBoundNs then
    IO.println s!"  FAIL {ctx} / {entry}: took {fmtMs ns} (bound {fmtMs callBoundNs})"
    bad := bad + 1
  if (← IO.getEnv "SAFEPDF_ADV_VERBOSE").isSome then
    IO.println s!"    {ctx} / {entry}: {showR rs} [{fmtMs ns}]"
  st.modify fun a =>
    { a with
      failures := a.failures + bad
      calls := a.calls + 1
      maxCallNs := max a.maxCallNs ns
      totalNs := a.totalNs + ns }
  return r

/-! ## Byte helpers -/

/-- Every offset at which `pat` occurs. -/
def findAll (b : ByteArray) (pat : String) : List Nat :=
  let p := pat.toUTF8.toList
  (List.range b.size).filter (Parse.matchesAt b p)

/-- The position just after the `obj` keyword of the header at `off` (searched in the next
40 bytes). -/
def bodyPos (b : ByteArray) (off : Nat) : Option Nat :=
  ((List.range 40).find? fun i => Parse.matchesAt b "obj".toUTF8.toList (off + i)).map
    (off + · + 3)

/-- The decimal number of at most `w` digits at `p`. -/
def readNum (b : ByteArray) (p w : Nat) : Nat := (Parse.readDigits b w p 0).1

/-- The number of decimal digits at `p` (at most 20). -/
def digitCount (b : ByteArray) (p : Nat) : Nat := (Parse.readDigits b 20 p 0).2 - p

/-- Overwrite the `w` bytes at `p` with `v`, zero-padded; `none` if `v` needs more digits. -/
def setNum (b : ByteArray) (p w v : Nat) : Option ByteArray :=
  let s := toString v
  if s.length > w then none
  else some (b.extract 0 p ++ ("".pushn '0' (w - s.length) ++ s).toUTF8 ++ b.extract (p + w) b.size)

/-- Offsets of `xref` keywords at the start of a line (excludes `startxref`). -/
def xrefOffsets (b : ByteArray) : List Nat :=
  (findAll b "xref").filter fun i => i == 0 || b[i - 1]? == some 10 || b[i - 1]? == some 13

/-- Start offsets of the `/Prev` values. -/
def prevPositions (b : ByteArray) : List Nat := (findAll b "/Prev ").map (· + 6)

/-- Start offset of the `startxref` value (after `startxref` and one EOL byte). -/
def startxrefPos (b : ByteArray) : Option Nat := (findAll b "startxref").getLast?.map (· + 10)

/-! ## Per-file runs -/

/-- A `lookup` for `parseIndirectResolved` and the fuel (object count) from a section. -/
def lookupOf (sec : XrefSection) : (Nat → Option XrefEntry) × Nat :=
  (fun k => Chain.lookupEntry k sec.entries, sec.entries.length)

/-- Run every entry point on one corpus file. Returns the number of failures. -/
def runFile (name : String) (bytes : ByteArray) : IO Nat := do
  let st ← IO.mkRef ({} : Acc)
  let rows := expectations name
  let used ← IO.mkRef ([] : List String)
  let ex := fun (k : String) => do
    used.modify (k :: ·)
    return (rows.lookup k).getD Expect.any
  let lim := Limits.default
  let chain ← call st name "loadChain" (← ex "loadChain") chainS
    (fun _ => Chain.loadChain lim bytes)
  let rep ← call st name "repair" (← ex "repair") repairS (fun _ => Repair.repair lim bytes)
  let opened ← call st name "openFile" (← ex "openFile") openS
    (fun _ => Core.Open.openFile lim bytes)
  let _ ← call st name "parse" (← ex "parse") docS (fun _ => SafePdf.parse bytes)
  let objs ← call st name "scanObjects" (← ex "scanObjects") (fun l => s!"{l}")
    (fun _ => .ok (Repair.scanObjects lim bytes))
  let objs := match objs with
    | .ok l => l
    | .error _ => []
  -- object resolution through the opened document (cycles below the root surface here)
  match opened with
  | .ok d =>
    for (n, g, _) in objs do
      let k := s!"getObject obj {n}"
      let _ ← call st name k (← ex k) (fun _ => "body") (fun _ => d.getObject lim n g)
  | .error _ => pure ()
  for (n, _, off) in objs do
    let k := s!"parseIndirectAt obj {n}"
    let _ ← call st name k (← ex k) indS (fun _ => parseIndirectAt lim bytes off)
    match bodyPos bytes off with
    | some p =>
      let k := s!"parseObjectAt obj {n}"
      let _ ← call st name k (← ex k) (fun r => s!"end {r.2}") (fun _ => parseObjectAt lim bytes p)
    | none => pure ()
  if name.startsWith "length-" then
    let sec? : Option XrefSection := match chain, rep with
      | .ok revs, _ => some (Chain.mergeChain revs)
      | .error _, .ok (s, _) => some s
      | .error _, .error _ => none
    match sec? with
    | none =>
      IO.println s!"  FAIL {name}: no xref data (loadChain and repair both failed) for /Length"
      st.modify fun a => { a with failures := a.failures + 1 }
    | some sec =>
      let (lookup, fuel) := lookupOf sec
      for (n, _, off) in objs do
        let k := s!"parseIndirectResolved obj {n}"
        let _ ← call st name k (← ex k) indS
          (fun _ => Length.parseIndirectResolved lookup lim bytes fuel off)
  let usedKeys ← used.get
  for (k, _) in rows do
    if !usedKeys.contains k then
      IO.println s!"  FAIL {name} / {k}: expectation row never exercised"
      st.modify fun a => { a with failures := a.failures + 1 }
  let a ← st.get
  let mut f := a.failures
  if a.totalNs > fileBoundNs then
    IO.println s!"  FAIL {name}: total {fmtMs a.totalNs} (bound {fmtMs fileBoundNs})"
    f := f + 1
  IO.println s!"  {name}: {a.calls} calls, {rows.length} expectation rows, total {fmtMs a.totalNs}, max call {fmtMs a.maxCallNs}, {f} failures"
  return f

/-! ## Mutations -/

/-- One mutated input. -/
structure Variant where
  label : String
  bytes : ByteArray
  /-- `loadChain` and `openFile` must fail with an `Error.cycle` `/Prev` cycle error. -/
  prevCycle : Bool := false
  /-- Run `parseIndirectResolved` on this object number, and whether it must be a
  "cyclic /Length" error. -/
  lengthObj : Option (Nat × Bool) := none

/-- A variant of a `/Prev` file is *closed* when it still has a `/Prev` at every original
position (one per table), every `/Prev` value and the `startxref` value are xref-table
offsets of the original, and the xref tables are untouched (length-preserving edits of the
values only): then no revision terminates the chain, so `loadChain` must report a cycle. -/
def closedPrev (orig m : ByteArray) : Bool :=
  let xo := xrefOffsets orig
  let ps := prevPositions orig
  m.size == orig.size && ps.length == xo.length && xrefOffsets m == xo &&
    ps.all (fun p => Parse.matchesAt m "/Prev ".toUTF8.toList (p - 6) &&
      xo.contains (readNum m p (digitCount orig p))) &&
    match startxrefPos orig with
    | some sp => xo.contains (readNum m sp (digitCount orig sp))
    | none => false

/-- The mutation set of a file with `/Prev` chains (`xref-prev-*.pdf`). -/
def prevVariants (b : ByteArray) : List Variant := Id.run do
  let ps := prevPositions b
  let xo := xrefOffsets b
  let objs := (Repair.scanObjects Limits.default b).map (·.2.2)
  let mut out : List Variant := []
  let mk := fun (label : String) (m : ByteArray) =>
    ({ label, bytes := m, prevCycle := closedPrev b m } : Variant)
  -- each /Prev digit incremented mod 10
  for p in ps do
    for j in List.range (digitCount b p) do
      match b[p + j]? with
      | some d =>
        let d' : UInt8 := 48 + (d - 48 + 1) % 10
        out := mk s!"/Prev@{p} digit {j} -> {Char.ofNat d'.toNat}" (b.set! (p + j) d') :: out
      | none => pure ()
  -- swap /Prev values (the cycle file has two)
  if ps.length == 2 then
    match ps with
    | [p, q] =>
      let w := digitCount b p
      let w' := digitCount b q
      match setNum b p w (readNum b q w') >>= fun m => setNum m q w' (readNum b p w) with
      | some m => out := mk "swap /Prev values" m :: out
      | none => pure ()
    | _ => pure ()
  -- each /Prev pointed at interesting offsets
  let sxKw := (findAll b "startxref").getLast?.toList
  let targets : List Nat :=
    ([0, 1] ++ xo ++ xo.map (· + 1) ++ xo.map (· - 1) ++ objs ++ objs.map (· + 4) ++
      objs.map (· + 10) ++ findAll b "trailer" ++ sxKw ++ [b.size - 1, b.size, b.size + 1,
      9999999999]).eraseDups
  for p in ps do
    for t in targets do
      match setNum b p (digitCount b p) t with
      | some m => out := mk s!"/Prev@{p} := {t}" m :: out
      | none => pure ()
  -- startxref pointed at every xref table
  match startxrefPos b with
  | some sp =>
    for t in xo do
      match setNum b sp (digitCount b sp) t with
      | some m => out := mk s!"startxref := {t}" m :: out
      | none => pure ()
  | none => pure ()
  -- each /Prev blanked out (length-preserving)
  for p in ps do
    let w := 6 + digitCount b p
    let m := b.extract 0 (p - 6) ++ ("".pushn ' ' w).toUTF8 ++ b.extract (p - 6 + w) b.size
    out := mk s!"/Prev@{p} removed" m :: out
  -- %%EOF deleted
  match (findAll b "%%EOF").getLast? with
  | some e => out := mk "%%EOF deleted" (b.extract 0 e ++ b.extract (e + 5) b.size) :: out
  | none => pure ()
  -- truncations
  for pct in [25, 50, 75] do
    out := mk s!"truncated at {pct}%" (b.extract 0 (b.size * pct / 100)) :: out
  return out.reverse

/-- The mutation set of `length-self-ref.pdf`: the `/Length k g R` reference renumbered. -/
def lengthVariants (b : ByteArray) (selfObj : Nat) : List Variant := Id.run do
  let mut out : List Variant := []
  for occ in findAll b "/Length " do
    let p := occ + 8
    if digitCount b p == 1 && Parse.matchesAt b " 0 R".toUTF8.toList (p + 1) then
      for k in List.range 9 do
        let k := k + 1
        match setNum b p 1 k with
        | some m =>
          out := { label := s!"/Length {k} 0 R", bytes := m,
                   lengthObj := some (selfObj, k == selfObj) } :: out
        | none => pure ()
      match setNum b p 1 selfObj >>= fun m => setNum m (p + 2) 1 1 with
      | some m =>
        out := { label := s!"/Length {selfObj} 1 R", bytes := m,
                 lengthObj := some (selfObj, true) } :: out
      | none => pure ()
  return out.reverse

/-- Run `loadChain`, `repair`, `openFile` and (if requested) `parseIndirectResolved` on one
variant. -/
def runVariant (st : IO.Ref Acc) (file : String) (v : Variant) : IO Unit := do
  let ctx := s!"{file} [{v.label}]"
  let lim := Limits.default
  let before ← st.get
  let chain ← call st ctx "loadChain" (if v.prevCycle then .errCycle "xref /Prev cycle" else .any)
    chainS (fun _ => Chain.loadChain lim v.bytes)
  let _ ← call st ctx "repair" .any repairS (fun _ => Repair.repair lim v.bytes)
  let _ ← call st ctx "openFile" (if v.prevCycle then .errCycle "xref /Prev cycle" else .any)
    openS (fun _ => Core.Open.openFile lim v.bytes)
  match v.lengthObj with
  | none => pure ()
  | some (n, cyc) =>
    match chain with
    | .error _ =>
      IO.println s!"  FAIL {ctx}: loadChain failed, cannot resolve /Length"
      st.modify fun a => { a with failures := a.failures + 1 }
    | .ok revs =>
      let sec := Chain.mergeChain revs
      let (lookup, fuel) := lookupOf sec
      match lookup n with
      | some (.inUse off _) =>
        let _ ← call st ctx s!"parseIndirectResolved obj {n}"
          (if cyc then .errCycle "cyclic /Length" else .any) indS
          (fun _ => Length.parseIndirectResolved lookup lim v.bytes fuel off)
      | _ =>
        IO.println s!"  FAIL {ctx}: object {n} not in use in the xref"
        st.modify fun a => { a with failures := a.failures + 1 }
  let after ← st.get
  if after.totalNs - before.totalNs > fileBoundNs then
    IO.println s!"  FAIL {ctx}: total {fmtMs (after.totalNs - before.totalNs)} (bound {fmtMs fileBoundNs})"
    st.modify fun a => { a with failures := a.failures + 1 }

/-- Run a mutation set and print its one-line summary. Returns the number of failures. -/
def runMutations (file : String) (vs : List Variant) (minCycles : Nat) : IO Nat := do
  let st ← IO.mkRef ({} : Acc)
  for v in vs do
    runVariant st file v
  let a ← st.get
  let cycles := (vs.filter fun v => v.prevCycle || (v.lengthObj.map (·.2)).getD false).length
  let mut f := a.failures
  -- guard against the generator silently degenerating
  if vs.isEmpty || cycles < minCycles then
    IO.println s!"  FAIL mutations of {file}: {vs.length} variants, {cycles} cycle variants (expected ≥ {minCycles})"
    f := f + 1
  IO.println s!"  mutations of {file}: {vs.length} variants ({cycles} must report a cycle), {a.calls} calls, total {fmtMs a.totalNs}, max call {fmtMs a.maxCallNs}, {f} failures"
  return f

/-! ## Entry point -/

/-- Run the suite; returns the number of failures. -/
def run : IO Nat := do
  let entries ← advDir.readDir
  let names := (entries.toList.map (·.fileName)).filter (·.endsWith ".pdf")
    |>.mergeSort (fun a b => decide (a < b) || a == b)
  let mut failures := 0
  for k in knownFiles do
    if !names.contains k then
      IO.println s!"  FAIL {k}: listed in the expectations table but missing from {advDir}"
      failures := failures + 1
  for name in names do
    let bytes ← IO.FS.readBinFile (advDir / name)
    failures := failures + (← runFile name bytes)
  -- mutations of the cyclic files
  for (name, minCycles) in [("xref-prev-cycle.pdf", 4), ("xref-prev-self.pdf", 1)] do
    if names.contains name then
      let bytes ← IO.FS.readBinFile (advDir / name)
      failures := failures + (← runMutations name (prevVariants bytes) minCycles)
  if names.contains "length-self-ref.pdf" then
    let bytes ← IO.FS.readBinFile (advDir / "length-self-ref.pdf")
    failures := failures + (← runMutations "length-self-ref.pdf" (lengthVariants bytes 4) 2)
  return failures

end SafePdf.Tests.Adversarial
