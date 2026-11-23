import SafePdf

/-!
# Decompression-bomb suite (task 3.6a; milestone M3)

Plan.md §6 Phase 3 (M3: "decompression-bomb suite (nested streams, 10⁶:1 ratios) all rejected
within limits"), §4 S3 (output ≤ limit or error), §7 item 3 (adversarial inputs "must fail
*fast and cleanly*").

The corpus `Tests/adversarial/bombs/` is written by `generate.py` there (see its README):

* raw streams `NAME.bin` with their stream dictionary `NAME.dict` (PDF text), decoded with
  `Core.Filter.decodeStream` (strict);
* `NAME.pdf`: the same stream as the page contents (object 4) of a one-page PDF, run through
  `Core.Open.openFile` (must open strictly), `OpenDoc.getObject 4 0` (the raw stream) and
  `decodeStream` on its dictionary and data;
* `objstm-bomb.pdf`, `objstm-bomb-root.pdf`, `xref-bomb.pdf`: bombs inside the file structure,
  run through `Chain.loadChain`, `openFile` and `getObject`.

Every row is checked under two limit sets:

* `small`: `Limits.default` with `maxDecodedStreamBytes` = 1 MiB (always run; fast);
* `default`: `Limits.default` (256 MiB per stream). Rejecting a bomb under it costs decoding
  up to 256 MiB first, so this mode runs only when `SAFEPDF_BOMBS_DEFAULT=1` is set.

Every call is timed (the result is matched on before the clock is read again) and must finish
within `boundNs` of its mode. Per-row timing lines are printed in default mode, and in small
mode with `SAFEPDF_BOMBS_VERBOSE=1`.

`Limits.maxDecodedTotalBytes` (per-document accounting) is not exercised: `decodeStream`
decodes one stream and does not account across streams (`Core/Filter.lean` header).

Paths are relative to the current directory: run `lake exe tests` from the repo root.
-/

namespace SafePdf.Tests.Bombs

open SafePdf SafePdf.Core

/-- Directory of the bomb corpus. -/
def bombDir : System.FilePath := "Tests" / "adversarial" / "bombs"

/-- One MiB. -/
def MiB : Nat := 1 <<< 20

/-- The small test limit: 1 MiB per decoded stream. -/
def smallLimits : Limits := { Limits.default with maxDecodedStreamBytes := MiB }

/-- The two limit modes. -/
inductive Mode where
  | small
  | default
  deriving BEq

/-- The limits of a mode. -/
def Mode.limits : Mode → Limits
  | .small => smallLimits
  | .default => Limits.default

/-- The mode's name. -/
def Mode.name : Mode → String
  | .small => "small(1MiB)"
  | .default => "default(256MiB)"

/-- Per-call time bound of a mode, in nanoseconds: 2 s for the small limit; 10 s for the
default limit (it decodes up to 256 MiB first). Measured (compiled, Apple silicon): Flate
rejections ≈ 1 s, RunLength/ASCII85/8-filter chains ≈ 2 s, the 256 MiB Flate control 3.1 s,
LZW bombs ≈ 2.4–2.8 s since task 3.12 (they took 150–300 s before: the output buffer was
shared and copied on every append). -/
def Mode.boundNs : Mode → Nat
  | .small => 2000000000
  | .default => 10000000000

/-! ## Expectations -/

/-- The expected outcome of one call. -/
inductive Expect where
  /-- Success with exactly this many decoded bytes. -/
  | okSize (n : Nat)
  /-- Success (any value). -/
  | ok
  /-- `Error.limitExceeded .decodedStreamBytes`. -/
  | limit
  /-- `Error.limitExceeded` of any kind, or `Error.unsupported`: a chain of 9 filters exceeds
  `Filter.maxFilters` = 8, which is `unsupported` before task 3.9 and `limitExceeded` after. -/
  | limitOrUnsupported
  deriving BEq

/-- Human-readable expectation. -/
def Expect.describe : Expect → String
  | .okSize n => s!"ok, {n} bytes"
  | .ok => "ok"
  | .limit => "limitExceeded decodedStreamBytes"
  | .limitOrUnsupported => "limitExceeded or unsupported"

/-- An error as one line. -/
def errS : Error → String
  | .malformed o m => s!"malformed@{o}: {m}"
  | .limitExceeded k => s!"limitExceeded {reprStr k}"
  | .unsupported w => s!"unsupported: {w}"
  | .cycle o w => s!"cycle@{o}: {w}"

/-- Whether a result (summarised to a size) meets the expectation. -/
def Expect.accepts : Expect → Except Error Nat → Bool
  | .okSize n, .ok m => n == m
  | .ok, .ok _ => true
  | .limit, .error (.limitExceeded .decodedStreamBytes) => true
  | .limitOrUnsupported, .error (.limitExceeded _) => true
  | .limitOrUnsupported, .error (.unsupported _) => true
  | _, _ => false

/-- A result as one line. -/
def showR : Except Error Nat → String
  | .ok n => s!"ok {n} bytes"
  | .error e => s!"error {errS e}"

/-- The expected outcome of decoding raw stream `name` under `mode`. Bombs fail under both;
the `-1m` controls succeed under both except `-plus1` under the small limit; the `-256m`
controls fail under the small limit and sit at / one byte over the default one. -/
def expectRaw (name : String) (mode : Mode) : Expect :=
  match name, mode with
  | "chain-9", _ => .limitOrUnsupported
  | "control-flate-1m", _ => .okSize MiB
  | "control-rl-1m", _ => .okSize MiB
  | "control-flate-1m-plus1", .small => .limit
  | "control-flate-1m-plus1", .default => .okSize (MiB + 1)
  | "control-rl-1m-plus1", .small => .limit
  | "control-rl-1m-plus1", .default => .okSize (MiB + 1)
  -- PNG predictor, rows of tag + 1 byte: the 1 MiB Flate output shrinks to 512 KiB
  -- (predictors never amplify, `Predictor.decode_size_le`)
  | "control-predictor-1m", _ => .okSize (MiB / 2)
  | "control-flate-256m", .small => .limit
  | "control-flate-256m", .default => .okSize (256 * MiB)
  | "control-flate-256m-plus1", _ => .limit
  | _, _ => .limit

/-- The raw streams of the corpus (each has `.bin` and `.dict`; a `.pdf` unless noted in
`noPdf`). -/
def rawNames : List String :=
  ["flate-1g", "flate-nested", "flate-nested-3", "lzw-kwkwk", "lzw-full-table", "runlength",
   "ascii85-z", "chain-8", "chain-9", "predictor",
   "control-flate-1m", "control-flate-1m-plus1", "control-rl-1m", "control-rl-1m-plus1",
   "control-predictor-1m", "control-flate-256m", "control-flate-256m-plus1"]

/-- Raw streams without a PDF wrapper. -/
def noPdf : List String := ["control-flate-256m", "control-flate-256m-plus1"]

/-! ## Timed calls -/

/-- Run `f ()` between two clock readings; the result is matched on (hence fully evaluated)
before the second reading. -/
@[noinline] def timeIt {α : Type} (f : Unit → Except Error α) : IO (Except Error α × Nat) := do
  let t0 ← IO.monoNanosNow
  match f () with
  | .ok v => do
    let t1 ← IO.monoNanosNow
    pure (.ok v, t1 - t0)
  | .error e => do
    let t1 ← IO.monoNanosNow
    pure (.error e, t1 - t0)

/-- Nanoseconds as milliseconds with one decimal. -/
def fmtMs (ns : Nat) : String :=
  let t := ns / 100000
  s!"{t / 10}.{t % 10} ms"

/-- Check one summarised result against its expectation and the time bound, print a line
(always on failure; when `verbose` otherwise). Returns the number of failures. -/
def check (mode : Mode) (verbose : Bool) (ctx : String) (exp : Expect) (r : Except Error Nat)
    (ns : Nat) : IO Nat := do
  let mut bad := 0
  if !exp.accepts r then
    IO.println s!"  FAIL [{mode.name}] {ctx}: expected {exp.describe}, got {showR r}"
    bad := bad + 1
  if ns > mode.boundNs then
    IO.println s!"  FAIL [{mode.name}] {ctx}: took {fmtMs ns} (bound {fmtMs mode.boundNs})"
    bad := bad + 1
  if verbose then
    IO.println s!"    [{mode.name}] {ctx}: {showR r} [{fmtMs ns}]"
  return bad

/-- Decode with `decodeStream` (strict), timed, summarised to the output size. -/
def decodeTimed (lim : Limits) (d : Dict) (raw : ByteArray) : IO (Except Error Nat × Nat) := do
  let (r, ns) ← timeIt fun _ => Filter.decodeStream lim d raw (strict := true)
  return (r.map (·.bytes.size), ns)

/-- Parse a `.dict` file (`<< … >>`). -/
def readDict (path : System.FilePath) : IO (Option Dict) := do
  let b ← IO.FS.readBinFile path
  match parseObjectAt Limits.default b 0 with
  | .ok (.dict d, _) => return some d
  | _ => return none

/-! ## Rows -/

/-- Raw stream `name`: `decodeStream` on `.bin` with `.dict`, then through the PDF
(`openFile` strict, `getObject 4 0`, `decodeStream`). -/
def runRaw (mode : Mode) (verbose : Bool) (name : String) : IO Nat := do
  let lim := mode.limits
  let exp := expectRaw name mode
  let mut f := 0
  let raw ← IO.FS.readBinFile (bombDir / s!"{name}.bin")
  match ← readDict (bombDir / s!"{name}.dict") with
  | none =>
    IO.println s!"  FAIL {name}.dict: not a dictionary"
    return 1
  | some d =>
    let (r, ns) ← decodeTimed lim d raw
    f := f + (← check mode verbose s!"{name}.bin decodeStream ({raw.size} B)" exp r ns)
  if noPdf.contains name then return f
  let pdf ← IO.FS.readBinFile (bombDir / s!"{name}.pdf")
  let (o, ns) ← timeIt fun _ => Open.openFile lim pdf
  match o with
  | .error e =>
    IO.println s!"  FAIL [{mode.name}] {name}.pdf openFile: {errS e} [{fmtMs ns}]"
    return f + 1
  | .ok doc =>
    if doc.repaired then
      IO.println s!"  FAIL [{mode.name}] {name}.pdf openFile: opened by repair, expected strict"
      f := f + 1
    let (g, ns2) ← timeIt fun _ => doc.getObject lim 4 0
    match g with
    | .ok (.stream st) =>
      let (r, ns3) ← decodeTimed lim st.dict st.data
      f := f + (← check mode verbose
        s!"{name}.pdf decodeStream of getObject 4 0 (openFile {fmtMs ns}, getObject {fmtMs ns2})" exp r ns3)
    | .ok _ =>
      IO.println s!"  FAIL [{mode.name}] {name}.pdf getObject 4 0: not a stream"
      f := f + 1
    | .error e =>
      IO.println s!"  FAIL [{mode.name}] {name}.pdf getObject 4 0: {errS e}"
      f := f + 1
    return f

/-- Summarise a document-level result: `0` bytes for success (the size is not meaningful). -/
def docR {α : Type} (r : Except Error α) : Except Error Nat := r.map fun _ => 0

/-- The structural bombs. Outcomes are the same under both limits.

* `objstm-bomb.pdf`: the root is a plain object, so the file opens strictly; object 6 lives
  in object stream 4, which inflates to 320 MiB: `getObject 6 0` must be `limitExceeded`.
* `objstm-bomb-root.pdf`: the catalog lives in the bomb object stream. The strict path fails
  validating the root (`limitExceeded`, not a cycle), so `openFile` tries repair, which
  resolves the root through the same object stream and fails the same way; `openFile`
  returns the strict error (rule P4): `limitExceeded`.
* `xref-bomb.pdf`: the only xref section is an xref stream inflating to 320 MiB:
  `loadChain` must be `limitExceeded`. Objects 1–3 are plain and the catalog is sound, so
  `openFile` falls back to repair (rule P3) and opens the document **repaired** — the clean
  strict→repair path — without decoding the bomb again. -/
def runStructural (mode : Mode) (verbose : Bool) : IO Nat := do
  let lim := mode.limits
  let mut f := 0
  -- objstm-bomb.pdf
  let b ← IO.FS.readBinFile (bombDir / "objstm-bomb.pdf")
  let (o, ns) ← timeIt fun _ => Open.openFile lim b
  match o with
  | .ok doc =>
    f := f + (← check mode verbose "objstm-bomb.pdf openFile" .ok (docR o) ns)
    if doc.repaired then
      IO.println s!"  FAIL [{mode.name}] objstm-bomb.pdf: opened by repair, expected strict"
      f := f + 1
    let (g, ns) ← timeIt fun _ => doc.getObject lim 6 0
    f := f + (← check mode verbose "objstm-bomb.pdf getObject 6 0" .limit (docR g) ns)
  | .error _ => f := f + (← check mode verbose "objstm-bomb.pdf openFile" .ok (docR o) ns)
  -- objstm-bomb-root.pdf
  let b ← IO.FS.readBinFile (bombDir / "objstm-bomb-root.pdf")
  let (o, ns) ← timeIt fun _ => Open.openFile lim b
  f := f + (← check mode verbose "objstm-bomb-root.pdf openFile" .limit (docR o) ns)
  -- xref-bomb.pdf
  let b ← IO.FS.readBinFile (bombDir / "xref-bomb.pdf")
  let (c, ns) ← timeIt fun _ => Xref.Chain.loadChain lim b
  f := f + (← check mode verbose "xref-bomb.pdf loadChain" .limit (docR c) ns)
  let (o, ns) ← timeIt fun _ => Open.openFile lim b
  f := f + (← check mode verbose "xref-bomb.pdf openFile" .ok (docR o) ns)
  match o with
  | .ok doc =>
    if !doc.repaired then
      IO.println s!"  FAIL [{mode.name}] xref-bomb.pdf: expected a repaired document"
      f := f + 1
  | .error _ => pure ()
  return f

/-- Run every row under one mode; print a summary line. -/
def runMode (mode : Mode) (verbose : Bool) : IO Nat := do
  let t0 ← IO.monoNanosNow
  let mut f := 0
  for n in rawNames do
    f := f + (← runRaw mode verbose n)
  f := f + (← runStructural mode verbose)
  let t1 ← IO.monoNanosNow
  IO.println s!"  bombs [{mode.name}]: {rawNames.length} raw streams, {rawNames.length - noPdf.length + 3} PDFs, total {fmtMs (t1 - t0)}, {f} failures"
  return f

/-! ## Entry point -/

/-- Run the suite; returns the number of failures. The default-limit mode runs only with
`SAFEPDF_BOMBS_DEFAULT=1`. -/
def run : IO Nat := do
  let verbose := (← IO.getEnv "SAFEPDF_BOMBS_VERBOSE").isSome
  let mut f ← runMode .small verbose
  if (← IO.getEnv "SAFEPDF_BOMBS_DEFAULT") == some "1" then
    f := f + (← runMode .default true)
  else
    IO.println "  bombs [default(256MiB)]: skipped (set SAFEPDF_BOMBS_DEFAULT=1)"
  return f

end SafePdf.Tests.Bombs
