import SafePdf.Shell.Views.Common
import SafePdf.Shell.Views.Summary

/-!
# `streams` view: decoded-stream viewer (task 3.7)

Plan.md §6 Phase 3 (filters) and the M3 row of the MVP / visibility track ("decoded-stream
viewer"). For every stream object of an opened document it runs the verified filter
pipeline (`Core.Filter.decodeStreamB`) and reports what came out.

**Enumeration.** Every `inUse` cross-reference entry is fetched with
`Core.Open.Session.getObject`; the stream bodies are reported. Entries in object streams
(`compressed`) are counted but not fetched: an object inside an object stream can never be a
stream (ISO 32000-2 §7.5.7), so fetching them would only cost object-stream decodes.

**Indirect `/Filter` and `/DecodeParms`.** `decodeStream` returns `unsupported` for an
indirect reference in either entry (the core never resolves references on its own). This
shell resolves one level first: a top-level reference, and references among the elements
of an array, are replaced by the direct object `getObject` returns (a stream or an error
leaves the reference in place, so `decodeStream` still reports it). Streams that needed this
are flagged `resolved` and counted in the summary.

**Budget** (tasks 3.13, 4.5). Decoding goes through `Core.Filter.decodeStreamB` from the
session the document was opened in (`SafePdf.Document.session`, from `SafePdf.parseWith` =
`Core.Open.Session.open`: what is left of `maxDecodedTotalBytes` after opening, and the object
streams decoded while opening), so every byte a filter stage allocates is charged,
intermediate stages and failed attempts included (rules B1–B5 of `Core.Filter`); fetches go
through `Core.Open.Session.getObject`, which charges (and caches) any object-stream decode
needed to resolve an indirect `/Filter` or `/DecodeParms`, and (task 4.5) the object-stream
decodes of an indirect `/Length` resolution (`Core.Xref.Length.parseIndirectResolvedB`). When
a stream does not fit the remaining budget it is reported as `resource limit exceeded: total
decoded size`, and every later stream is skipped with the marker `skipped: decoded-bytes
budget exhausted` (JSON `"skipped": "budget"`); with nothing left, later streams are skipped
as well. The open and the decodes charged here are therefore bounded by
`maxDecodedTotalBytes` together. (`decodeAll`, used by the golden tests, still starts from a
fresh session, `Core.Open.Session.ofDoc`.)

**Per stream.** Object number and generation, `/Type` and `/Subtype` when they are names,
the `/Filter` chain (names), whether `/DecodeParms` is present, the raw length, then the
decoded length, or the image placeholder (`image <codec>`: the chain ends in an image codec,
whose input bytes are reported but not decoded), or the error; and the decode time.
**Summary.** Counts by filter chain, errors by kind (the error text without its offset),
total raw and decoded bytes, the maximum per-stream time.

**JSON** (`--json`): one line per stream,
`{"num": N, "gen": G, "type": "/T"|null, "subtype": "/S"|null, "filters": ["FlateDecode"],
"decodeParms": B, "resolved": B, "raw": R, "decoded": D, "codec": "dct"|null, "ms": "0.012"}`
with `"error": "message", "errorKind": "malformed"|"unsupported"|"cycle"|"limit"` in place of
`decoded`/`codec` on failure, or `"skipped": "budget"`; then one line
`{"summary": {...}}`. Fetch failures of non-stream objects are only counted.

**Dumping one stream (differential testing, task 3.6b).** The CLI has no view arguments, so
two environment variables, read by this view only, select and dump one stream:

* `SAFEPDF_STREAM=N` — report only object `N` (all generations of the entry). With `--json`
  its line also carries `"hex": "<lowercase hex>"` of the decoded bytes (for an image
  placeholder: the bytes handed to the codec), capped at the first `hexCap` = 1 MiB of
  decoded data, with `"hexTruncated": true` when cut. In text mode a 64-byte hex preview is
  printed.
* `SAFEPDF_STREAM_OUT=<path>` (only together with `SAFEPDF_STREAM`) — also write the full
  decoded bytes, uncapped beyond the decoding limits, to `<path>`. A stream that fails to
  decode writes nothing. A write failure is reported on stderr and makes the view print
  `dump: error`.

A non-numeric `SAFEPDF_STREAM` is reported on stderr and ignored.
-/

namespace SafePdf.Shell.Views.Streams

open SafePdf.Shell
open SafePdf.Core.Xref (XrefEntry)
open SafePdf.Core.Filter (Decoded ImageCodec)

/-! ## Records -/

/-- How decoding one stream ended. -/
inductive Outcome where
  /-- `decodeStream` returned a result. -/
  | decoded (d : Decoded)
  /-- `decodeStream` (or the total budget) failed. -/
  | failed (e : Error)
  /-- Not decoded: the total decoded-bytes budget was already exhausted. -/
  | skipped

/-- What the view reports about one stream (no timing). -/
structure Rec where
  /-- Object number. -/
  num : Nat
  /-- Generation number. -/
  gen : Nat
  /-- `/Type` as `/Name`, when it is a name. -/
  type : Option String
  /-- `/Subtype` as `/Name`, when it is a name. -/
  subtype : Option String
  /-- The `/Filter` chain as names (after one-level resolution); `?` for a non-name. -/
  filters : List String
  /-- `/DecodeParms` present (and not `null`). -/
  hasParms : Bool
  /-- An indirect `/Filter` or `/DecodeParms` (or element) was resolved first. -/
  resolved : Bool
  /-- Raw (encoded) data length. -/
  raw : Nat
  /-- The decode result. -/
  outcome : Outcome

/-- The number of bytes a record's outcome contributes to the decoded total. -/
def Rec.decodedBytes (r : Rec) : Nat :=
  match r.outcome with
  | .decoded d => d.bytes.size
  | _ => 0

/-! ## Helpers -/

/-- `/Name` text of a name object. -/
def nameStr (n : Name) : String := "/" ++ Core.Filter.nameText n

/-- A dictionary entry as `/Name` text, when it is a name. -/
def nameEntry (d : Dict) (k : String) : Option String :=
  match d.get? (Name.ofString k) with
  | some (.name n) => some (nameStr n)
  | _ => none

/-- Short name of an image codec. -/
def codecName : ImageCodec → String
  | .dct => "dct"
  | .jpx => "jpx"
  | .jbig2 => "jbig2"
  | .ccitt => "ccitt"

/-- Resolve one indirect reference to the direct object it names, fetching through the
session (`Core.Open.Session.getObject`: an object-stream decode is charged to the budget and
cached). `(o, true)` when a reference was replaced; a stream body or a fetch error leaves the
reference in place. -/
def resolveRef (sess : Core.Open.Session) (limits : Limits) :
    PdfObject → PdfObject × Bool × Core.Open.Session
  | .ref n g =>
    match sess.getObject limits n g with
    | (.ok (.obj o), sess') => (o, true, sess')
    | (_, sess') => (.ref n g, false, sess')
  | o => (o, false, sess)

/-- Resolve one level of indirection in a `/Filter` or `/DecodeParms` value: the value
itself, then (if it is an array) each of its elements. -/
def resolveValue (sess : Core.Open.Session) (limits : Limits) (v : PdfObject) :
    PdfObject × Bool × Core.Open.Session :=
  let (v1, r1, sess) := resolveRef sess limits v
  match v1 with
  | .array items =>
    let (out, any, sess) := items.foldl (init := (([] : List PdfObject), r1, sess))
      fun (acc, any, sess) it =>
        let (o, r, sess) := resolveRef sess limits it
        (o :: acc, any || r, sess)
    (.array out.reverse, any, sess)
  | _ => (v1, r1, sess)

/-- The stream dictionary with `/Filter` and `/DecodeParms` resolved one level. -/
def resolveDict (sess : Core.Open.Session) (limits : Limits) (d : Dict) :
    Dict × Bool × Core.Open.Session :=
  let keyF := Name.ofString "Filter"
  let keyP := Name.ofString "DecodeParms"
  let (out, any, sess) := d.foldl (init := (([] : Dict), false, sess)) fun (acc, any, sess) (k, v) =>
    if k == keyF || k == keyP then
      let (v', r, sess) := resolveValue sess limits v
      ((k, v') :: acc, any || r, sess)
    else ((k, v) :: acc, any, sess)
  (out.reverse, any, sess)

/-- The `/Filter` chain as display names. -/
def filterList (d : Dict) : List String :=
  let one : PdfObject → String
    | .name n => Core.Filter.nameText n
    | .ref n g => s!"{n} {g} R"
    | _ => "?"
  match d.get? (Name.ofString "Filter") with
  | none => []
  | some (.array items) => items.map one
  | some o => [one o]

/-- Display key of a filter chain, e.g. `ASCIIHexDecode,FlateDecode` or `(none)`. -/
def chainKey (fs : List String) : String :=
  if fs.isEmpty then "(none)" else ",".intercalate fs

/-- Short kind of an error, for JSON. -/
def errorKind : Error → String
  | .malformed _ _ => "malformed"
  | .limitExceeded _ => "limit"
  | .unsupported _ => "unsupported"
  | .cycle _ _ => "cycle"
  | .encryption _ => "encryption"

/-- An error's text without its byte offset, for grouping. -/
def errorKey : Error → String
  | .malformed _ msg => s!"malformed: {msg}"
  | .cycle _ what => s!"cycle: {what}"
  | e => renderError e

/-! ## Decoding with a budget -/

/-- Decode one stream body with `Core.Filter.decodeStreamB` from the session's budget
(task 3.13), returning the record and the session (budget charged, cache updated by the
`/Filter` resolution). `exhausted` means an earlier stream already ran out of budget. -/
def decodeBody (sess : Core.Open.Session) (limits : Limits) (exhausted : Bool)
    (num gen : Nat) (s : Stream) : Rec × Core.Open.Session :=
  let (d, resolved, sess) := resolveDict sess limits s.dict
  let base : Rec :=
    { num, gen, type := nameEntry d "Type", subtype := nameEntry d "Subtype",
      filters := filterList d, hasParms := (d.get? (Name.ofString "DecodeParms")).isSome,
      resolved, raw := s.data.size, outcome := .skipped }
  if exhausted || sess.budget.remaining = 0 then (base, sess)
  else
    let (r, budget) := Core.Filter.decodeStreamB limits sess.budget d s.data
    let outcome : Outcome := match r with
      | .ok r => .decoded r
      | .error e => .failed e
    ({ base with outcome }, { sess with budget })

/-- Did this record exhaust the total budget? -/
def Rec.exhausts (r : Rec) : Bool :=
  match r.outcome with
  | .failed (.limitExceeded .decodedTotalBytes) => true
  | _ => false

/-- Counters that are not per-stream. -/
structure Scan where
  /-- In-use entries fetched. -/
  fetched : Nat := 0
  /-- Fetches that failed (not counted as streams). -/
  fetchErrors : Nat := 0
  /-- Entries in object streams (not fetched: never streams). -/
  compressed : Nat := 0

/-- Decoding state threaded through the entries. -/
structure State where
  /-- The session: document, budget, object-stream cache. -/
  sess : Core.Open.Session
  /-- The budget ran out. -/
  exhausted : Bool := false
  /-- Entry counters. -/
  scan : Scan := {}

/-- Step for one stream record: the session after it, and whether the budget ran out. -/
def State.after (st : State) (r : Rec) (sess : Core.Open.Session) : State :=
  { st with sess, exhausted := st.exhausted || r.exhausts }

/-- The in-use entries to look at: all, or only object `only`. -/
def entries (doc : Core.Open.OpenDoc) (only : Option Nat) : Array (Nat × XrefEntry) :=
  match only with
  | none => doc.index
  | some n => doc.index.filter (·.1 == n)

/-- Pure run over all entries (no timing) from the session `sess0` (task 4.5). -/
def decodeAllS (limits : Limits) (sess0 : Core.Open.Session) (only : Option Nat := none) :
    Array Rec × Scan :=
  let st0 : State := { sess := sess0 }
  let (recs, st) := (entries sess0.doc only).foldl (init := ((#[] : Array Rec), st0))
    fun (recs, st) (num, e) =>
      match e with
      | .compressed _ _ =>
        (recs, { st with scan := { st.scan with compressed := st.scan.compressed + 1 } })
      | .free _ _ => (recs, st)
      | .inUse _ g =>
        let st := { st with scan := { st.scan with fetched := st.scan.fetched + 1 } }
        match st.sess.getObject limits num g with
        | (.error _, sess) =>
          (recs, { st with sess, scan := { st.scan with fetchErrors := st.scan.fetchErrors + 1 } })
        | (.ok (.obj _), sess) => (recs, { st with sess })
        | (.ok (.stream s), sess) =>
          let (r, sess) := decodeBody sess limits st.exhausted num g s
          (recs.push r, st.after r sess)
  (recs, st.scan)

/-- Pure run over all entries (no timing): used by the golden tests. The budget starts full
(`Core.Open.Session.ofDoc`). -/
def decodeAll (limits : Limits) (doc : Core.Open.OpenDoc) (only : Option Nat := none) :
    Array Rec × Scan :=
  decodeAllS limits (Core.Open.Session.ofDoc limits doc) only

/-! ## Rendering -/

/-- Increment the count of `k` in an association list (first-seen order). -/
def bump (k : String) : List (String × Nat) → List (String × Nat)
  | [] => [(k, 1)]
  | (k', n) :: rest => if k' == k then (k', n + 1) :: rest else (k', n) :: bump k rest

/-- Sort counts: descending count, then key. -/
def sortCounts (l : List (String × Nat)) : List (String × Nat) :=
  l.mergeSort fun a b => a.2 > b.2 || (a.2 == b.2 && a.1 ≤ b.1)

/-- Aggregate figures over the records. -/
structure Totals where
  /-- Streams reported. -/
  streams : Nat := 0
  /-- Fully decoded. -/
  decoded : Nat := 0
  /-- Image placeholders. -/
  images : Nat := 0
  /-- Failures. -/
  errors : Nat := 0
  /-- Skipped (budget). -/
  skipped : Nat := 0
  /-- Streams that needed one-level resolution. -/
  resolved : Nat := 0
  /-- Raw bytes. -/
  rawBytes : Nat := 0
  /-- Decoded bytes (placeholders: bytes handed to the codec). -/
  decodedBytes : Nat := 0
  /-- Counts by chain. -/
  byChain : List (String × Nat) := []
  /-- Counts by error. -/
  byError : List (String × Nat) := []

/-- Aggregate the records. -/
def totals (recs : Array Rec) : Totals :=
  recs.foldl (init := {}) fun t r =>
    let t := { t with streams := t.streams + 1, rawBytes := t.rawBytes + r.raw,
                      decodedBytes := t.decodedBytes + r.decodedBytes,
                      resolved := t.resolved + (if r.resolved then 1 else 0),
                      byChain := bump (chainKey r.filters) t.byChain }
    match r.outcome with
    | .decoded (.data _) => { t with decoded := t.decoded + 1 }
    | .decoded (.image _ _ _) => { t with images := t.images + 1 }
    | .failed e => { t with errors := t.errors + 1, byError := bump (errorKey e) t.byError }
    | .skipped => { t with skipped := t.skipped + 1 }

/-- The result part of a record's text line. -/
def outcomeText : Outcome → String
  | .decoded (.data b) => s!"decoded {b.size}"
  | .decoded (.image c _ b) => s!"image {codecName c} ({b.size} bytes to codec)"
  | .failed e => s!"error: {renderError e}"
  | .skipped => "skipped: decoded-bytes budget exhausted"

/-- One text line per stream; `ms` is the decode time, if shown. -/
def recText (r : Rec) (ms : Option String) : String :=
  let ty := match r.type, r.subtype with
    | some t, some s => s!"  {t} {s}"
    | some t, none => s!"  {t}"
    | none, some s => s!"  {s}"
    | none, none => ""
  let parms := if r.hasParms then " +parms" else ""
  let res := if r.resolved then " (resolved)" else ""
  let time := match ms with | some m => s!"  {m} ms" | none => ""
  s!"  {r.num} {r.gen}{ty}  [{chainKey r.filters}]{parms}{res}  raw {r.raw} -> {outcomeText r.outcome}{time}"

/-- Text form; `times` holds per-record nanoseconds (empty: no times shown). -/
def text (path : String) (result : Except Error Document) (recs : Array Rec) (sc : Scan)
    (times : Array Nat) : List String :=
  let head := [ s!"file:       {path}", s!"open:       {Summary.openMode result}" ]
  match result with
  | .error e => head ++ [ s!"error:      {renderError e}" ]
  | .ok _ =>
    let t := totals recs
    let showT := times.size == recs.size && !times.isEmpty
    let lines := (List.range recs.size).filterMap fun i =>
      recs[i]?.map fun r => recText r (if showT then times[i]?.map formatMs else none)
    head ++
    [ s!"entries:    {sc.fetched} fetched, {sc.fetchErrors} fetch error(s), {sc.compressed} in object streams (skipped)"
    , s!"streams:    {t.streams}: {t.decoded} decoded, {t.images} image placeholder(s), {t.errors} error(s), {t.skipped} skipped; {t.resolved} needed indirect /Filter or /DecodeParms resolution" ] ++
    lines ++
    [ "chains:" ] ++ (sortCounts t.byChain).map (fun (k, n) => s!"  {n}  {k}") ++
    [ "errors:" ] ++ (sortCounts t.byError).map (fun (k, n) => s!"  {n}  {k}") ++
    [ s!"bytes:      {t.rawBytes} raw, {t.decodedBytes} decoded" ] ++
    (if showT then [ s!"max time:   {formatMs (times.foldl max 0)} ms" ] else [])

/-- A JSON array of strings. -/
def jsonStrings (l : List String) : String :=
  "[" ++ ", ".intercalate (l.map jsonString) ++ "]"

/-- An optional JSON string. -/
def jsonOpt : Option String → String
  | some s => jsonString s
  | none => "null"

/-- Lowercase hex of the first `n` bytes of `b`. -/
def hexPrefix (b : ByteArray) (n : Nat) : String := Id.run do
  let mut s := ""
  for i in [0:min n b.size] do
    let x := (b[i]?.getD 0).toNat
    s := (s.push (hexDigit (x / 16))).push (hexDigit (x % 16))
  return s

/-- One JSON line per stream; `hex` adds the (capped) decoded bytes. -/
def recJson (r : Rec) (nanos : Nat) (hex : Option Nat) : String :=
  let base :=
    [ ("num", toString r.num), ("gen", toString r.gen), ("type", jsonOpt r.type),
      ("subtype", jsonOpt r.subtype), ("filters", jsonStrings r.filters),
      ("decodeParms", toString r.hasParms), ("resolved", toString r.resolved),
      ("raw", toString r.raw) ]
  let res : List (String × String) :=
    match r.outcome with
    | .decoded d =>
      let codec := match d with
        | .image c _ _ => jsonString (codecName c)
        | .data _ => "null"
      [ ("decoded", toString d.bytes.size), ("codec", codec) ] ++
      (match hex with
        | some cap =>
          [ ("hex", jsonString (hexPrefix d.bytes cap)),
            ("hexTruncated", toString (decide (d.bytes.size > cap))) ]
        | none => [])
    | .failed e => [ ("error", jsonString (renderError e)), ("errorKind", jsonString (errorKind e)) ]
    | .skipped => [ ("skipped", jsonString "budget") ]
  jsonObject (base ++ res ++ [ ("ms", jsonString (formatMs nanos)) ])

/-- The JSON summary line. -/
def summaryJson (path : String) (result : Except Error Document) (recs : Array Rec) (sc : Scan)
    (times : Array Nat) : String :=
  let base := [ ("path", jsonString path), ("open", jsonString (Summary.openMode result)) ]
  let counts (l : List (String × Nat)) : String :=
    jsonObject ((sortCounts l).map fun (k, n) => (k, toString n))
  let fields :=
    match result with
    | .error e => base ++ [ ("error", jsonString (renderError e)) ]
    | .ok _ =>
      let t := totals recs
      base ++
      [ ("fetched", toString sc.fetched), ("fetchErrors", toString sc.fetchErrors),
        ("compressed", toString sc.compressed), ("streams", toString t.streams),
        ("decoded", toString t.decoded), ("images", toString t.images),
        ("errors", toString t.errors), ("skipped", toString t.skipped),
        ("resolved", toString t.resolved), ("rawBytes", toString t.rawBytes),
        ("decodedBytes", toString t.decodedBytes), ("byChain", counts t.byChain),
        ("byError", counts t.byError), ("maxMs", jsonString (formatMs (times.foldl max 0))) ]
  jsonObject [ ("summary", jsonObject fields) ]

/-! ## The view -/

/-- Cap on the hex dump in `--json` with `SAFEPDF_STREAM`: 1 MiB of decoded data. -/
def hexCap : Nat := 1 <<< 20

/-- Run over all entries with per-stream timing (same logic as `decodeAllS`), from the session
`sess0` (the parse's session, task 4.5). -/
def decodeAllTimed (limits : Limits) (sess0 : Core.Open.Session) (only : Option Nat) :
    IO (Array Rec × Scan × Array Nat) := do
  let mut st : State := { sess := sess0 }
  let mut recs : Array Rec := #[]
  let mut times : Array Nat := #[]
  for (num, e) in entries sess0.doc only do
    match e with
    | .compressed _ _ => st := { st with scan := { st.scan with compressed := st.scan.compressed + 1 } }
    | .free _ _ => pure ()
    | .inUse _ g =>
      st := { st with scan := { st.scan with fetched := st.scan.fetched + 1 } }
      match st.sess.getObject limits num g with
      | (.error _, sess) =>
        st := { st with sess, scan := { st.scan with fetchErrors := st.scan.fetchErrors + 1 } }
      | (.ok (.obj _), sess) => st := { st with sess }
      | (.ok (.stream s), sess) =>
        let exhausted := st.exhausted
        let t0 ← IO.monoNanosNow
        -- `lazyPure` evaluates the (strict) record when this action runs, between the two
        -- clock reads.
        let (r, sess) ← IO.lazyPure fun _ => decodeBody sess limits exhausted num g s
        let t1 ← IO.monoNanosNow
        recs := recs.push r
        times := times.push (t1 - t0)
        st := st.after r sess
  return (recs, st.scan, times)

/-- The `streams` view. -/
def view : View where
  name := "streams"
  description := "decode every stream (filter chains, lengths, errors, times); SAFEPDF_STREAM=N dumps one"
  run cfg i := do
    let only ← match ← IO.getEnv "SAFEPDF_STREAM" with
      | none => pure none
      | some s =>
        match s.trimAscii.toString.toNat? with
        | some n => pure (some n)
        | none =>
          IO.eprintln s!"inspect: SAFEPDF_STREAM='{s}' is not an object number; ignored"
          pure none
    let outPath ← if only.isSome then IO.getEnv "SAFEPDF_STREAM_OUT" else pure none
    let (recs, sc, times) ← match i.result with
      | .ok d => decodeAllTimed cfg.limits d.session only
      | .error _ => pure (#[], {}, #[])
    -- Dump the selected stream's decoded bytes to a file.
    let mut dumpLine : Option String := none
    if let some p := outPath then
      match recs.toList.findSome? (fun r => match r.outcome with
          | .decoded d => some d.bytes
          | _ => none) with
      | some b =>
        try
          IO.FS.writeBinFile p b
          dumpLine := some s!"dump:       {b.size} bytes to {p}"
        catch e =>
          IO.eprintln s!"inspect: cannot write {p}: {e}"
          dumpLine := some "dump:       error"
      | none => dumpLine := some "dump:       nothing decoded; no file written"
    if cfg.json then
      let hex := if only.isSome then some hexCap else none
      for k in [0:recs.size] do
        if let some r := recs[k]? then
          IO.println (recJson r (times[k]?.getD 0) hex)
      IO.println (summaryJson i.path i.result recs sc times)
    else
      (text i.path i.result recs sc times).forM IO.println
      if only.isSome then
        for r in recs do
          match r.outcome with
          | .decoded d => IO.println s!"hex[{r.num} {r.gen}]: {hexPrefix d.bytes 64}{if d.bytes.size > 64 then "…" else ""}"
          | _ => pure ()
      if let some l := dumpLine then IO.println l

end SafePdf.Shell.Views.Streams
