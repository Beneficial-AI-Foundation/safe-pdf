import SafePdf.Shell.Views.Common
import SafePdf.Shell.Views.Summary

/-!
# `resolve` view (task 2.11)

Resolves every in-use cross-reference entry of an opened document (classic `inUse` entries
with their generation, object-stream `compressed` entries with generation 0) and reports how
many succeed, how many fail, and the first few errors. Since task 4.5 the fetches go through
`Core.Open.Session.getObject`, threading the session the document was opened in
(`SafePdf.Document.session`): every object-stream decode (each container once, cached) and
every `/Length` resolution through an object stream is charged to the one document budget
(`Limits.maxDecodedTotalBytes`); with enough budget the results are those of
`Core.Open.OpenDoc.getObject` (`Core.Open.Session.getObject_eq`). Free entries are counted
but not fetched (they resolve to `null` by definition). This is the corpus dashboard's "all
in-use objects resolve" check (Plan.md §6 Phase 2, milestone M2).
-/

namespace SafePdf.Shell.Views.Resolve

open SafePdf.Shell
open SafePdf.Core.Xref (XrefEntry)

/-- How many errors are listed individually. -/
def maxListed : Nat := 5

/-- Counters of one resolution run. -/
structure Counts where
  /-- In-use entries (classic offsets). -/
  inUse : Nat := 0
  /-- Entries in object streams. -/
  compressed : Nat := 0
  /-- Free entries (not fetched). -/
  free : Nat := 0
  /-- Fetches that succeeded. -/
  ok : Nat := 0
  /-- Fetches that failed. -/
  errors : Nat := 0
  /-- The first `maxListed` failures, newest first: object number, generation, error. -/
  firstErrors : List (Nat × Nat × String) := []

/-- Record one fetch. -/
def Counts.record (c : Counts) (num gen : Nat) (r : Except Error IndirectBody) : Counts :=
  match r with
  | .ok _ => { c with ok := c.ok + 1 }
  | .error e =>
    { c with errors := c.errors + 1,
             firstErrors := if c.firstErrors.length < maxListed
               then (num, gen, renderError e) :: c.firstErrors else c.firstErrors }

/-- Resolve every in-use entry of `d`, in the document's session (one budget, one cache). -/
def resolveAll (limits : Limits) (d : Document) : Counts :=
  (d.doc.index.foldl (init := (({} : Counts), d.session)) fun (c, s) (num, e) =>
    match e with
    | .free _ _ => ({ c with free := c.free + 1 }, s)
    | .inUse _ g =>
      let (r, s) := s.getObject limits num g
      (({ c with inUse := c.inUse + 1 }).record num g r, s)
    | .compressed _ _ =>
      let (r, s) := s.getObject limits num 0
      (({ c with compressed := c.compressed + 1 }).record num 0 r, s)).1

/-- Text form. -/
def text (i : Input) (c : Option Counts) (nanos : Nat) : List String :=
  let head := [ s!"file:       {i.path}", s!"open:       {Summary.openMode i.result}" ]
  match i.result, c with
  | .ok _, some c =>
    head ++
    [ s!"entries:    {c.inUse} in use, {c.compressed} in object streams, {c.free} free"
    , s!"resolved:   {c.ok} ok, {c.errors} error(s)" ] ++
    (c.firstErrors.reverse.map fun (n, g, e) => s!"  {n} {g}: {e}") ++
    [ s!"time:       {formatMs nanos} ms" ]
  | .error e, _ => head ++ [ s!"error:      {renderError e}" ]
  | .ok _, none => head

/-- Single-line JSON form. -/
def json (i : Input) (c : Option Counts) (nanos : Nat) : String :=
  let errs (c : Counts) : String :=
    "[" ++ ", ".intercalate (c.firstErrors.reverse.map fun (n, g, e) =>
      jsonObject [("num", toString n), ("gen", toString g), ("error", jsonString e)]) ++ "]"
  let base := [ ("path", jsonString i.path), ("open", jsonString (Summary.openMode i.result)) ]
  match i.result, c with
  | .ok _, some c =>
    jsonObject (base ++
      [ ("inUse", toString c.inUse), ("compressed", toString c.compressed),
        ("free", toString c.free), ("resolvedOk", toString c.ok),
        ("resolveErrors", toString c.errors), ("firstErrors", errs c),
        ("resolveMs", formatMs nanos) ])
  | .error e, _ => jsonObject (base ++ [ ("error", jsonString (renderError e)) ])
  | .ok _, none => jsonObject base

/-- The `resolve` view. -/
def view : View where
  name := "resolve"
  description := "fetch every in-use xref entry (budgeted session); counts ok/error, first errors"
  run cfg i := do
    let (c, nanos) ← match i.result with
      | .ok d => do
        let t0 ← IO.monoNanosNow
        let c ← IO.lazyPure fun _ => resolveAll cfg.limits d
        let t1 ← IO.monoNanosNow
        pure (some c, t1 - t0)
      | .error _ => pure (none, 0)
    if cfg.json then IO.println (json i c nanos)
    else (text i c nanos).forM IO.println

end SafePdf.Shell.Views.Resolve
