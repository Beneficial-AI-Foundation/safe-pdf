import SafePdf.Shell.Views.Common
import SafePdf.Shell.Views.Summary
import SafePdf.Shell.Views.Objects

/-!
# `xref`, `revisions` and `repair` views (task 2.8)

The Phase 2 inspector views of milestone M2 (Plan.md §6 Phase 2, milestone table: "Xref
resolution trace, revision history, repair-path report on real files"):

* `xref` — the revision chain as the strict loader walks it (newest first): for each section
  its offset, how it was reached (`startxref`, `/Prev`, `/XRefStm`), its kind (classic table,
  hybrid table, xref stream), entry counts by type and its trailer keys; then the merged
  section; on a strict error, the error and the step at which it happened.
* `revisions` — revision history, oldest first: per section the object numbers it added,
  changed (redefined) or freed, with counts and a capped listing.
* `repair` — the repair path (`Repair.repair`; since task 12.7h the section of the document
  `Core.Open.repairOpen` builds, which for an encrypted file adds the object-stream members
  found after `withCrypt`), run whether or not the strict path succeeds:
  objects found, parse attempts and failures of the scan, the repaired root, whether the
  repaired document validates, and a capped diff against the strict merged xref.

**The trace.** `traceChain` re-walks the chain with the same public building blocks as
`Core.Xref.Chain.walk` (`parseSection`, `hybridStm`, the same cycle, range and revision-budget
checks), keeping the revisions parsed before an error so the views can say where the error
happened. It is fuel-bounded by `limits.maxRevisions + 1` steps. The authoritative result is
still `Core.Xref.Chain.loadChain`, which every view also runs; a disagreement between the two
is reported (`trace mismatch`), never hidden.

All listings are capped (`maxRevsListed`, `maxListed`, `maxKeys`); the work is linear in the
size of the sections per revision (sorted merges, no quadratic lookups), plus one repair scan
and one `Repair.scanRaw` for the attempt counters.
-/

namespace SafePdf.Shell.Views.Xref

open SafePdf.Shell
open SafePdf.Core.Xref (XrefEntry XrefSection Trailer)

/-! ## Caps -/

/-- How many revisions the `xref` and `revisions` views print individually. -/
def maxRevsListed : Nat := 64

/-- How many object numbers (or diff items) are listed per category. -/
def maxListed : Nat := 20

/-- How many trailer keys are printed per revision. -/
def maxKeys : Nat := 24

/-- Longest name (in characters) printed for a trailer key. -/
def maxKeyChars : Nat := 64

/-! ## Tracing the chain -/

/-- How the walk reached a section. -/
inductive Via where
  /-- The offset after `startxref`. -/
  | startxref
  /-- The `/Prev` of the previous (newer) section. -/
  | prev
  /-- The `/XRefStm` of a hybrid file's classic table. -/
  | xrefStm
  deriving BEq

/-- Text of a `Via`. -/
def Via.text : Via → String
  | .startxref => "startxref"
  | .prev => "/Prev"
  | .xrefStm => "/XRefStm"

/-- One parsed section of the chain. -/
structure RevInfo where
  /-- Byte offset of the `xref` keyword or of the xref stream's `n g obj`. -/
  offset : Nat
  /-- How the walk got here. -/
  via : Via
  /-- `true` for a classic table, `false` for an xref stream. -/
  isTable : Bool
  /-- The parsed section. -/
  sec : XrefSection
  /-- Its trailer (the stream dictionary for an xref stream). -/
  trailer : Trailer

/-- Where a strict walk failed: the offset it tried, how it got there, and the error. -/
structure TraceError where
  /-- The offset being followed (`none` when no `startxref` offset was found). -/
  offset : Option Nat
  /-- How the walk got to it. -/
  via : Via
  /-- The error. -/
  error : Error

/-- The result of `traceChain`. -/
structure Trace where
  /-- The `startxref` offset, if found. -/
  startxref : Option Nat
  /-- The sections parsed, newest first (a hybrid table is followed by its stream). -/
  revs : List RevInfo
  /-- The error that stopped the walk, if any. -/
  error : Option TraceError

/-- Follow the chain from `off` (reached via `via`). `visited` holds the offsets parsed so
far; `acc` the sections, oldest-parsed first is last (i.e. newest first, reversed at the
end). At most `fuel` steps. Mirrors `Core.Xref.Chain.step`/`walk`. -/
def traceWalk (limits : Limits) (bytes : ByteArray) :
    Nat → Nat → Via → List Nat → List RevInfo → List RevInfo × Option TraceError
  | 0, off, via, _, acc => (acc, some ⟨some off, via, .limitExceeded .revisions⟩)
  | fuel + 1, off, via, visited, acc =>
    let fail (e : Error) := (acc, some (TraceError.mk (some off) via e))
    if bytes.size ≤ off then fail (.malformed off "xref /Prev offset beyond end of input")
    else if visited.contains off then fail (.malformed off "xref /Prev cycle")
    else if limits.maxRevisions ≤ visited.length then fail (.limitExceeded .revisions)
    else
      match Core.Xref.Chain.parseSection limits bytes off with
      | .error e => fail e
      | .ok (sec, tr) =>
        let isTable := Core.Xref.matchAt bytes off Core.Xref.kwXref
        let r : RevInfo := ⟨off, via, isTable, sec, tr⟩
        let next (acc' : List RevInfo) (visited' : List Nat) :=
          match tr.prev? with
          | none => (acc', none)
          | some p => traceWalk limits bytes fuel p .prev visited' acc'
        match Core.Xref.Chain.hybridStm bytes off tr with
        | none => next (r :: acc) (off :: visited)
        | some s =>
          let failS (e : Error) := (r :: acc, some (TraceError.mk (some s) .xrefStm e))
          if bytes.size ≤ s then failS (.malformed s "xref /XRefStm offset beyond end of input")
          else if s == off || visited.contains s then failS (.malformed s "xref /XRefStm cycle")
          else if limits.maxRevisions ≤ visited.length + 1 then failS (.limitExceeded .revisions)
          else
            match Core.Xref.Stream.parseXrefStream limits bytes s with
            | .error e => failS e
            | .ok (sec2, tr2) =>
              next (⟨s, .xrefStm, false, sec2, tr2⟩ :: r :: acc) (s :: off :: visited)

/-- Trace the strict chain of `bytes` (see the module doc). -/
def traceChain (limits : Limits) (bytes : ByteArray) : Trace :=
  match Core.Xref.findStartxref bytes with
  | .error e => ⟨none, [], some ⟨none, .startxref, e⟩⟩
  | .ok off =>
    let (revs, err) := traceWalk limits bytes (limits.maxRevisions + 1) off .startxref [] []
    ⟨some off, revs.reverse, err⟩

/-! ## Counting -/

/-- Entry counts of a section by type. -/
structure EntryCounts where
  /-- Free entries. -/
  free : Nat := 0
  /-- In-use entries (byte offsets). -/
  inUse : Nat := 0
  /-- Entries in object streams. -/
  compressed : Nat := 0
  /-- Highest object number, if any entry. -/
  maxNum : Option Nat := none

/-- Count the entries of `es` by type. -/
def countEntries (es : List (Nat × XrefEntry)) : EntryCounts :=
  es.foldl (init := {}) fun c (n, e) =>
    let c := { c with maxNum := some (max n (c.maxNum.getD 0)) }
    match e with
    | .free _ _ => { c with free := c.free + 1 }
    | .inUse _ _ => { c with inUse := c.inUse + 1 }
    | .compressed _ _ => { c with compressed := c.compressed + 1 }

/-- Text of entry counts. -/
def EntryCounts.text (c : EntryCounts) : String :=
  let top := match c.maxNum with
    | some n => s!", highest object {n}"
    | none => ""
  s!"{c.inUse + c.free + c.compressed} entries ({c.inUse} in use, {c.compressed} compressed, {c.free} free){top}"

/-- JSON fields of entry counts. -/
def EntryCounts.json (c : EntryCounts) : List (String × String) :=
  [ ("entries", toString (c.inUse + c.free + c.compressed)), ("inUse", toString c.inUse),
    ("compressed", toString c.compressed), ("free", toString c.free),
    ("maxObject", match c.maxNum with | some n => toString n | none => "null") ]

/-! ## Rendering helpers -/

/-- A trailer key, `/Name`, truncated to `maxKeyChars`. -/
def keyText (n : Name) : String :=
  let s := Objects.nameText n
  if s.length ≤ maxKeyChars then s else (String.ofList (s.toList.take maxKeyChars)) ++ "…"

/-- The first `maxKeys` trailer keys, and how many there are. -/
def trailerKeys (t : Trailer) : List String × Nat :=
  ((t.dict.take maxKeys).map (keyText ·.1), t.dict.length)

/-- `none` → `-`. -/
def optText (o : Option Nat) : String :=
  match o with
  | some n => toString n
  | none => "-"

/-- `none` → JSON `null`. -/
def optJson (o : Option Nat) : String :=
  match o with
  | some n => toString n
  | none => "null"

/-- A JSON array of already-rendered values. -/
def jsonArray (xs : List String) : String := "[" ++ ", ".intercalate xs ++ "]"

/-- A capped list of numbers as text: `1 2 3 … (+N more)`. -/
def capText (xs : List Nat) (total : Nat) : String :=
  let more := if total > xs.length then s!" … (+{total - xs.length} more)" else ""
  " ".intercalate (xs.map toString) ++ more

/-- Kind of a section, as text. -/
def RevInfo.kind (r : RevInfo) : String :=
  if r.isTable then
    match r.trailer.xrefStm? with
    | some s => s!"hybrid table (XRefStm {s})"
    | none => "table"
  else if r.via == .xrefStm then "xref stream (hybrid XRefStm)"
  else "xref stream"

/-- Kind of a section, as a JSON token. -/
def RevInfo.kindJson (r : RevInfo) : String :=
  if r.isTable then (if r.trailer.xrefStm?.isSome then "hybrid" else "table") else "stream"

/-- Text of an error location. -/
def TraceError.text (e : TraceError) : String :=
  match e.offset with
  | some o => s!"{renderError e.error} (following {e.via.text} to offset {o})"
  | none => s!"{renderError e.error} (locating startxref)"

/-- JSON of an error location. -/
def TraceError.json (e : TraceError) : String :=
  jsonObject [ ("error", jsonString (renderError e.error)), ("via", jsonString e.via.text),
    ("offset", optJson e.offset) ]

/-- The authoritative strict chain and whether the trace agrees with it. -/
def checkTrace (limits : Limits) (bytes : ByteArray) (t : Trace) :
    Except Error (List Core.Xref.Chain.Revision) × Bool :=
  let chain := Core.Xref.Chain.loadChain limits bytes
  let agrees := match chain, t.error with
    | .ok revs, none => revs.map Core.Xref.Chain.Revision.offset == t.revs.map (·.offset)
    | .error _, some _ => true
    | _, _ => false
  (chain, agrees)

/-! ## `xref` view -/

/-- Everything the `xref` view prints for one file. -/
structure XrefReport where
  /-- The trace. -/
  trace : Trace
  /-- `loadChain`'s verdict. -/
  chain : Except Error (List Core.Xref.Chain.Revision)
  /-- Whether the trace agrees with `loadChain`. -/
  agrees : Bool
  /-- Counts of the merged section, when the chain loaded. -/
  merged : Option EntryCounts

/-- Compute the `xref` report (pure). -/
def xrefReport (limits : Limits) (bytes : ByteArray) : XrefReport :=
  let t := traceChain limits bytes
  let (chain, agrees) := checkTrace limits bytes t
  let merged := match chain with
    | .ok revs => some (countEntries (Core.Xref.Chain.mergeChain revs).entries)
    | .error _ => none
  ⟨t, chain, agrees, merged⟩

/-- Text lines for one revision of the `xref` view. -/
def revText (idx : Nat) (r : RevInfo) : List String :=
  let (keys, nkeys) := trailerKeys r.trailer
  let more := if nkeys > keys.length then s!" … (+{nkeys - keys.length})" else ""
  let root := match r.trailer.root? with
    | some (n, g) => s!"{n} {g} R"
    | none => "-"
  [ s!"  #{idx} offset {r.offset} via {r.via.text}: {r.kind}"
  , s!"      {(countEntries r.sec.entries).text}"
  , s!"      /Size {r.trailer.size}  /Prev {optText r.trailer.prev?}  /Root {root}  /XRefStm {optText r.trailer.xrefStm?}  encrypted {r.trailer.encrypted}"
  , s!"      keys: {" ".intercalate keys}{more}" ]

/-- JSON of one revision of the `xref` view. -/
def revJson (idx : Nat) (r : RevInfo) : String :=
  let (keys, nkeys) := trailerKeys r.trailer
  let root := match r.trailer.root? with
    | some (n, g) => jsonString s!"{n} {g} R"
    | none => "null"
  jsonObject ([ ("index", toString idx), ("offset", toString r.offset),
      ("via", jsonString r.via.text), ("kind", jsonString r.kindJson) ] ++
    (countEntries r.sec.entries).json ++
    [ ("size", toString r.trailer.size), ("prev", optJson r.trailer.prev?), ("root", root),
      ("xrefStm", optJson r.trailer.xrefStm?), ("encrypted", toString r.trailer.encrypted),
      ("keys", jsonArray (keys.map jsonString)), ("keyCount", toString nkeys) ])

/-- `xs` with indices, capped at `maxRevsListed`. -/
def indexed {α : Type} (xs : List α) : List (Nat × α) :=
  (List.range xs.length).zip xs |>.take maxRevsListed

/-- Text of the `xref` view (no timing, deterministic: used by the golden tests). -/
def xrefText (path : String) (rep : XrefReport) : List String :=
  let t := rep.trace
  let revs := (indexed t.revs).flatMap fun (i, r) => revText i r
  let moreRevs := if t.revs.length > maxRevsListed
    then [s!"  … (+{t.revs.length - maxRevsListed} more sections)"] else []
  [ s!"file:       {path}"
  , s!"startxref:  {optText t.startxref}"
  , s!"sections:   {t.revs.length} parsed (newest first)" ] ++ revs ++ moreRevs ++
  (match t.error with
   | some e => [s!"stopped:    {e.text}"]
   | none => []) ++
  [ match rep.chain with
    | .ok revs => s!"strict:     ok, {revs.length} section(s)"
    | .error e => s!"strict:     error: {renderError e}" ] ++
  (match rep.merged with
   | some c => [s!"merged:     {c.text}"]
   | none => []) ++
  (if rep.agrees then [] else ["warning:    trace mismatch: the trace disagrees with loadChain"])

/-- JSON of the `xref` view. -/
def xrefJson (path : String) (rep : XrefReport) (nanos : Nat) : String :=
  let t := rep.trace
  jsonObject
    [ ("path", jsonString path), ("startxref", optJson t.startxref),
      ("sectionCount", toString t.revs.length),
      ("sections", jsonArray ((indexed t.revs).map fun (i, r) => revJson i r)),
      ("stopped", match t.error with | some e => e.json | none => "null"),
      ("strictOk", toString (match rep.chain with | .ok _ => true | .error _ => false)),
      ("strictError", match rep.chain with
        | .ok _ => "null" | .error e => jsonString (renderError e)),
      ("merged", match rep.merged with
        | some c => jsonObject c.json | none => "null"),
      ("traceAgrees", toString rep.agrees), ("xrefMs", formatMs nanos) ]

/-- Time a pure computation. -/
def timed {α : Type} (f : Unit → α) : IO (α × Nat) := do
  let t0 ← IO.monoNanosNow
  let a ← IO.lazyPure f
  let t1 ← IO.monoNanosNow
  pure (a, t1 - t0)

/-- The `xref` view. -/
def xrefView : View where
  name := "xref"
  description := "strict xref chain trace: per section offset, kind, entry counts, trailer; merged section; where a strict error happened"
  run cfg i := do
    let (rep, nanos) ← timed fun _ => xrefReport cfg.limits i.bytes
    if cfg.json then IO.println (xrefJson i.path rep nanos)
    else
      (xrefText i.path rep).forM IO.println
      IO.println s!"time:       {formatMs nanos} ms"

/-! ## `revisions` view -/

/-- What one revision did, relative to the older ones. -/
structure RevDelta where
  /-- Object numbers not defined by any older section (count, first `maxListed` reversed). -/
  added : Nat × List Nat := (0, [])
  /-- Object numbers redefined in use (or compressed) over an older non-free entry. -/
  changed : Nat × List Nat := (0, [])
  /-- Object numbers defined in use (or compressed) over an older free entry. -/
  reused : Nat × List Nat := (0, [])
  /-- Object numbers made free over an older non-free entry. -/
  freed : Nat × List Nat := (0, [])
  /-- Free entries over an older free entry (e.g. object 0 in every update). -/
  stillFree : Nat := 0

/-- Record `n` in a capped counter. -/
def bump (c : Nat × List Nat) (n : Nat) : Nat × List Nat :=
  (c.1 + 1, if c.2.length < maxListed then n :: c.2 else c.2)

/-- Classify entry `e` of object `n` given the older effective entry `old`. -/
def RevDelta.add (d : RevDelta) (n : Nat) (e : XrefEntry) (old : Option XrefEntry) : RevDelta :=
  match old, e with
  | none, _ => { d with added := bump d.added n }
  | some (.free _ _), .free _ _ => { d with stillFree := d.stillFree + 1 }
  | some (.free _ _), _ => { d with reused := bump d.reused n }
  | some _, .free _ _ => { d with freed := bump d.freed n }
  | some _, _ => { d with changed := bump d.changed n }

/-- Classify the (sorted) entries `xs` of a revision against the (sorted) merged entries of
the older revisions `ys`: one linear merge. -/
def classify : List (Nat × XrefEntry) → List (Nat × XrefEntry) → RevDelta → RevDelta
  | [], _, d => d
  | (n, e) :: xs, [], d => classify xs [] (d.add n e none)
  | (n, e) :: xs, (m, f) :: ys, d =>
    if n < m then classify xs ((m, f) :: ys) (d.add n e none)
    else if m < n then classify ((n, e) :: xs) ys d
    else classify xs ys (d.add n e (some f))
termination_by xs ys => xs.length + ys.length

/-- Per revision (given newest first), its delta, returned oldest first with chain indices. -/
def history (revs : List RevInfo) : List (Nat × RevInfo × RevDelta) :=
  let n := revs.length
  let oldestFirst := ((List.range n).zip revs).reverse
  let (_, out) := oldestFirst.foldl (init := (([] : List (Nat × XrefEntry)), ([] : List _)))
    fun (merged, out) (i, r) =>
      let d := classify r.sec.entries merged {}
      (Core.Xref.Chain.mergeTwo r.sec.entries merged, (i, r, d) :: out)
  out.reverse

/-- Text of a capped counter. -/
def capLine (label : String) (c : Nat × List Nat) : List String :=
  if c.1 == 0 then [] else [s!"      {label} {c.1}: {capText c.2.reverse c.1}"]

/-- JSON of a capped counter. -/
def capJson (c : Nat × List Nat) : String :=
  jsonObject [ ("count", toString c.1), ("first", jsonArray (c.2.reverse.map toString)) ]

/-- The deltas to print: at most `maxRevsListed`, the oldest ones. -/
def historyListed (t : Trace) : List (Nat × RevInfo × RevDelta) :=
  (history t.revs).take maxRevsListed

/-- Text of the `revisions` view (deterministic). -/
def revisionsText (path : String) (t : Trace) (rep : XrefReport) : List String :=
  let h := historyListed t
  let lines := h.flatMap fun (i, r, d) =>
    [ s!"  #{i} offset {r.offset}: {r.kind}, {r.sec.entries.length} entries" ] ++
    capLine "added  " d.added ++ capLine "changed" d.changed ++ capLine "reused " d.reused ++
    capLine "freed  " d.freed ++
    (if d.stillFree == 0 then [] else [s!"      still free {d.stillFree}"])
  let more := if t.revs.length > h.length
    then [s!"  … (+{t.revs.length - h.length} newer sections)"] else []
  [ s!"file:       {path}"
  , s!"sections:   {t.revs.length} (oldest first; #0 is the newest)" ] ++ lines ++ more ++
  (match t.error with
   | some e => [s!"stopped:    {e.text}"]
   | none => []) ++
  (if rep.agrees then [] else ["warning:    trace mismatch: the trace disagrees with loadChain"])

/-- JSON of the `revisions` view. -/
def revisionsJson (path : String) (t : Trace) (rep : XrefReport) (nanos : Nat) : String :=
  let h := historyListed t
  jsonObject
    [ ("path", jsonString path), ("sectionCount", toString t.revs.length),
      ("revisions", jsonArray (h.map fun (i, r, d) => jsonObject
        [ ("index", toString i), ("offset", toString r.offset),
          ("kind", jsonString r.kindJson), ("entries", toString r.sec.entries.length),
          ("added", capJson d.added), ("changed", capJson d.changed), ("reused", capJson d.reused),
          ("freed", capJson d.freed), ("stillFree", toString d.stillFree) ])),
      ("stopped", match t.error with | some e => e.json | none => "null"),
      ("traceAgrees", toString rep.agrees), ("revisionsMs", formatMs nanos) ]

/-- The `revisions` view. -/
def revisionsView : View where
  name := "revisions"
  description := "revision history, oldest first: object numbers each xref section added, changed, reused or freed (capped)"
  run cfg i := do
    let (rep, nanos) ← timed fun _ =>
      let rep := xrefReport cfg.limits i.bytes
      -- Force the history inside the timed region.
      let h := historyListed rep.trace
      (rep, h.length)
    let rep := rep.1
    if cfg.json then IO.println (revisionsJson i.path rep.trace rep nanos)
    else
      (revisionsText i.path rep.trace rep).forM IO.println
      IO.println s!"time:       {formatMs nanos} ms"

/-! ## `repair` view -/

/-- Diff of the repaired section against the strict merged one. -/
structure Diff where
  /-- Same object number, both in use, same offset and generation. -/
  same : Nat := 0
  /-- In use in strict, not found by the scan (capped list: `(num, offset)`). -/
  onlyStrict : Nat × List (Nat × Nat) := (0, [])
  /-- Compressed in strict, not found by the scan (expected: repair does not read object
  streams). -/
  onlyStrictCompressed : Nat := 0
  /-- Found by the scan, free or absent in strict (capped list: `(num, offset)`). -/
  onlyRepair : Nat × List (Nat × Nat) := (0, [])
  /-- Found by the scan, compressed in strict. -/
  repairOverCompressed : Nat := 0
  /-- Both in use, different offset or generation (capped: `(num, strict, repair)`). -/
  mismatch : Nat × List (Nat × Nat × Nat) := (0, [])

/-- Record in a capped counter. -/
def bumpL {α : Type} (c : Nat × List α) (x : α) : Nat × List α :=
  (c.1 + 1, if c.2.length < maxListed then x :: c.2 else c.2)

/-- One strict-only entry. -/
def Diff.strictOnly (d : Diff) (n : Nat) : XrefEntry → Diff
  | .inUse o _ => { d with onlyStrict := bumpL d.onlyStrict (n, o) }
  | .compressed _ _ => { d with onlyStrictCompressed := d.onlyStrictCompressed + 1 }
  | .free _ _ => d

/-- One repair-only entry (the repaired section has only in-use entries and object 0). -/
def Diff.repairOnly (d : Diff) (n : Nat) : XrefEntry → Diff
  | .inUse o _ => { d with onlyRepair := bumpL d.onlyRepair (n, o) }
  | _ => d

/-- One object number in both. -/
def Diff.both (d : Diff) (n : Nat) (s r : XrefEntry) : Diff :=
  match s, r with
  | .inUse so sg, .inUse ro rg =>
    if so == ro && sg == rg then { d with same := d.same + 1 }
    else { d with mismatch := bumpL d.mismatch (n, so, ro) }
  | .free _ _, .inUse ro _ => { d with onlyRepair := bumpL d.onlyRepair (n, ro) }
  | .compressed _ _, .inUse _ _ => { d with repairOverCompressed := d.repairOverCompressed + 1 }
  | _, _ => d

/-- Linear diff of two sorted entry lists (strict, repaired). -/
def diff : List (Nat × XrefEntry) → List (Nat × XrefEntry) → Diff → Diff
  | [], [], d => d
  | (n, e) :: xs, [], d => diff xs [] (d.strictOnly n e)
  | [], (m, f) :: ys, d => diff [] ys (d.repairOnly m f)
  | (n, e) :: xs, (m, f) :: ys, d =>
    if n < m then diff xs ((m, f) :: ys) (d.strictOnly n e)
    else if m < n then diff ((n, e) :: xs) ys (d.repairOnly m f)
    else diff xs ys (d.both n e f)
termination_by xs ys => xs.length + ys.length

/-- Everything the `repair` view prints for one file. -/
structure RepairReport where
  /-- The repaired document's section and trailer (`Core.Open.repairOpen`, so for an
  encrypted file with the R6 entries found after `withCrypt`), else `Repair.repair`'s result. -/
  repaired : Except Error (XrefSection × Trailer)
  /-- Header hits, parse attempts and failed attempts of the scan (`Repair.scanRaw`). -/
  hits : Nat
  /-- Parse attempts. -/
  attempts : Nat
  /-- Failed attempts. -/
  failures : Nat
  /-- Whether the repaired document opens and validates (`Core.Open.repairOpen`, with
  decryption). -/
  validates : Except Error Unit
  /-- The strict merged section, or the strict error. -/
  strict : Except Error XrefSection
  /-- The diff, when both sections exist. -/
  diff : Option Diff

/-- Compute the `repair` report (pure). -/
def repairReport (limits : Limits) (bytes : ByteArray) : RepairReport :=
  let (raw, attempts, failures) := Repair.scanRaw limits bytes
  -- the repaired document (task 12.7h): for an encrypted file its section includes the
  -- object-stream members R6 finds after `withCrypt` (`OpenDoc.withObjStmEnc`)
  let opened := Core.Open.repairOpen limits bytes
  let repaired := match opened with
    | .ok d => .ok (d.xref, d.trailer)
    | .error _ => Repair.repair limits bytes
  let validates : Except Error Unit := match repaired with
    | .error e => .error e
    | .ok _ =>
      match opened with
      | .ok _ => .ok ()
      | .error e => .error e
  let strict := match Core.Xref.Chain.loadChain limits bytes with
    | .ok revs => .ok (Core.Xref.Chain.mergeChain revs)
    | .error e => .error e
  let d := match strict, repaired with
    | .ok s, .ok (r, _) => some (diff s.entries r.entries {})
    | _, _ => none
  ⟨repaired, raw.length, attempts, failures, validates, strict, d⟩

/-- Text of the `repair` view (deterministic). -/
def repairText (path : String) (limits : Limits) (r : RepairReport) : List String :=
  let budget := if r.failures ≥ limits.maxRepairFailures
    then s!" (failure budget {limits.maxRepairFailures} exhausted)" else ""
  let res := match r.repaired with
    | .error e => [s!"repair:     error: {renderError e}"]
    | .ok (sec, tr) =>
      let root := match tr.root? with
        | some (n, g) => s!"{n} {g} R"
        | none => "-"
      let (keys, _) := trailerKeys tr
      [ s!"repair:     ok, {sec.entries.length - 1} object(s), /Size {tr.size}, /Root {root}, encrypted {tr.encrypted}"
      , s!"trailer:    {" ".intercalate keys}" ]
  let valid := match r.validates with
    | .ok () => "validates:  yes (/Root resolves to a dictionary)"
    | .error e => s!"validates:  no: {renderError e}"
  let strict := match r.strict with
    | .ok s => s!"strict:     ok, {s.entries.length} merged entries"
    | .error e => s!"strict:     error: {renderError e}"
  let pairs (xs : List (Nat × Nat)) : String :=
    " ".intercalate (xs.reverse.map fun (n, o) => s!"{n}@{o}")
  let more {α : Type} (c : Nat × List α) : String :=
    if c.1 > c.2.length then s!" … (+{c.1 - c.2.length} more)" else ""
  let diffLines := match r.diff with
    | none => ["diff:       n/a (needs both strict and repaired sections)"]
    | some d =>
      [ s!"diff:       {d.same} same, {d.mismatch.1} offset/generation mismatch(es), {d.onlyStrict.1} only in strict, {d.onlyRepair.1} only in repair, {d.onlyStrictCompressed} compressed (not scanned), {d.repairOverCompressed} found over compressed" ] ++
      (if d.mismatch.1 == 0 then [] else
        [s!"  mismatch (num strict→repair): {" ".intercalate (d.mismatch.2.reverse.map fun (n, s, o) => s!"{n}:{s}→{o}")}{more d.mismatch}"]) ++
      (if d.onlyStrict.1 == 0 then [] else
        [s!"  only strict (num@offset): {pairs d.onlyStrict.2}{more d.onlyStrict}"]) ++
      (if d.onlyRepair.1 == 0 then [] else
        [s!"  only repair (num@offset): {pairs d.onlyRepair.2}{more d.onlyRepair}"])
  [ s!"file:       {path}"
  , s!"scan:       {r.hits} header hit(s), {r.attempts} parse attempt(s), {r.failures} failed{budget}" ] ++
  res ++ [ valid, strict ] ++ diffLines

/-- JSON of the `repair` view. -/
def repairJson (path : String) (r : RepairReport) (nanos : Nat) : String :=
  let pairs (c : Nat × List (Nat × Nat)) : String :=
    jsonObject [ ("count", toString c.1), ("first", jsonArray (c.2.reverse.map fun (n, o) =>
      jsonObject [("num", toString n), ("offset", toString o)])) ]
  let res := match r.repaired with
    | .error e => [ ("repairOk", "false"), ("repairError", jsonString (renderError e)) ]
    | .ok (sec, tr) =>
      [ ("repairOk", "true"), ("objects", toString (sec.entries.length - 1)),
        ("size", toString tr.size),
        ("root", match tr.root? with
          | some (n, g) => jsonString s!"{n} {g} R" | none => "null"),
        ("encrypted", toString tr.encrypted) ]
  jsonObject ([ ("path", jsonString path), ("headerHits", toString r.hits),
      ("attempts", toString r.attempts), ("failures", toString r.failures) ] ++ res ++
    [ ("validates", match r.validates with | .ok () => "true" | .error _ => "false"),
      ("validateError", match r.validates with
        | .ok () => "null" | .error e => jsonString (renderError e)),
      ("strictOk", match r.strict with | .ok _ => "true" | .error _ => "false"),
      ("diff", match r.diff with
        | none => "null"
        | some d => jsonObject
          [ ("same", toString d.same),
            ("mismatch", jsonObject [ ("count", toString d.mismatch.1),
              ("first", jsonArray (d.mismatch.2.reverse.map fun (n, s, o) =>
                jsonObject [("num", toString n), ("strict", toString s),
                  ("repair", toString o)])) ]),
            ("onlyStrict", pairs d.onlyStrict), ("onlyRepair", pairs d.onlyRepair),
            ("onlyStrictCompressed", toString d.onlyStrictCompressed),
            ("repairOverCompressed", toString d.repairOverCompressed) ]),
      ("repairMs", formatMs nanos) ])

/-- The `repair` view. -/
def repairView : View where
  name := "repair"
  description := "run the repair scan regardless of strict success: objects found, failures, root, validation, diff vs strict xref (capped)"
  run cfg i := do
    let (r, nanos) ← timed fun _ => repairReport cfg.limits i.bytes
    if cfg.json then IO.println (repairJson i.path r nanos)
    else
      (repairText i.path cfg.limits r).forM IO.println
      IO.println s!"time:       {formatMs nanos} ms"

end SafePdf.Shell.Views.Xref
