import SafePdf
import SafePdf.Core.Write.Annots
import SafePdf.Shell.App.Xfdf
import SafePdf.Shell.App.Select
import SafePdf.Shell.Worker.Protocol

/-!
# Scaling suite (task 13.3; Plan.md §6 Phase 13, §7)

Every probe builds an input in memory at `n` and at `2n`, times one public entry point
(`Api.openBytes`, `Api.pageText`, `Api.pageLinks`, `Api.outline`, `Api.renderPage`,
`Core.Write.Annots.writeMarks` = `Incremental.writeAnnots`, the XFDF reader and writer, the
search over a page index, the worker protocol decoder) and fails when `t(2n) > 3 × t(n)`.
A linear entry point gives about 2×, a quadratic one 4×, so 3× separates them.
Input construction is not timed. Each probe's result is also checked (`ok`: the entry point
accepted the input and gave the expected shape), so a probe that quietly hits a `Limits`
bound and returns `limitExceeded` at both sizes fails instead of passing on a flat time.

## Noise handling (machine load varies, other builds run in parallel)

* **Minimum of three.** A timing is the minimum of three runs of the entry point (the
  minimum, not the mean: load only ever adds time).
* **Calibration.** The probe starts at its `n0` and doubles `n` (up to `maxN`) until one run
  takes at least `floorMs` = 30 ms, so a fast machine measures larger inputs and the
  timer's resolution and scheduler jitter stay small against `t(n)`. Calibration runs are
  discarded.
* **Second round.** When the ratio exceeds 3, both sizes are measured again (three more
  runs each) and the minimum over all six runs is used. Only a probe that fails twice fails.
* **Floor.** If `t(n)` is still under 30 ms at `maxN` (the input is capped by a `Limits`
  bound), the comparison uses `max t(n) 30 ms`; the row is marked `(below floor)`.
* **Known probes.** `known := "13.x"` turns a failure into a printed `WARN` naming the
  ledger row; a known probe that passes prints a `NOTE` to remove the tag. A known probe
  never counts as a failure. M13 needs no tagged probe.

The table has one row per probe: entry point, `n`, `t(n)`, `t(2n)`, the ratio and the status.
Excluded from `scripts/compiled-vs-interpreted.sh` (wall-clock figures, like `adversarial`).
-/

namespace SafePdf.Tests.Scaling

open SafePdf SafePdf.Core

/-! ## Timing harness -/

/-- Smallest `t(n)` (milliseconds) a measurement should have. -/
def floorMs : Nat := 30

/-- `t(2n) > ratioMax × t(n)` fails (quadratic gives 4). -/
def ratioMax : Nat := 3

/-- One probe. -/
structure Probe where
  /-- Name of the probe. -/
  name : String
  /-- The public entry point under test. -/
  entry : String
  /-- Starting `n` of the calibration. -/
  n0 : Nat
  /-- Largest `n` the calibration reaches (a bound of `Limits` or the generator). -/
  maxN : Nat
  /-- Builds the input for `n` (untimed) and returns the timed action: whether the entry
  point accepted the input as expected, and a checksum of its result. -/
  setup : Nat → IO (IO (Bool × Nat))
  /-- Ledger row of a known super-linear probe. -/
  known : Option String := none

/-- Hides `input` from the compiler until the timed action runs, so the work cannot be
floated out of the timed region. -/
def prep {α : Type} (input : α) (run : α → Bool × Nat) : IO (IO (Bool × Nat)) := do
  let r ← IO.mkRef input
  return do
    let x ← r.get
    pure (run x)

/-- Nanoseconds of one run; the result is demanded before the clock is read again. -/
def timeOnce (act : IO (Bool × Nat)) : IO (Nat × Bool) := do
  let t0 ← IO.monoNanosNow
  let (ok, v) ← act
  if v == 0xFFFFFFFFFFFFFFF then IO.println "?"
  let t1 ← IO.monoNanosNow
  return (t1 - t0, ok)

/-- Minimum of `k` runs, and whether every run was `ok`. -/
def minOf (act : IO (Bool × Nat)) (k : Nat) : IO (Nat × Bool) := do
  let mut best := 0
  let mut all := true
  for i in [0:k] do
    let (t, ok) ← timeOnce act
    best := if i == 0 then t else min best t
    all := all && ok
  return (best, all)

/-- Milliseconds with one decimal. -/
def ms (ns : Nat) : String :=
  let t := ns / 100000
  s!"{t / 10}.{t % 10}"

/-- A ratio with two decimals. -/
def ratioS (a b : Nat) : String :=
  let r := a * 100 / max b 1
  s!"{r / 100}.{if r % 100 < 10 then "0" else ""}{r % 100}"

/-- One measured probe. -/
structure Row where
  /-- The size. -/
  n : Nat
  /-- `t(n)` in ns. -/
  t1 : Nat
  /-- `t(2n)` in ns. -/
  t2 : Nat
  /-- Both inputs accepted. -/
  ok : Bool

/-- Verdict of a pair of timings. -/
def pass (t1 t2 : Nat) : Bool := t2 ≤ ratioMax * max t1 (floorMs * 1000000)

/-- Calibrates `n`, measures `n` and `2n`, repeats once when the ratio fails. -/
def measure (p : Probe) : IO Row := do
  let mut n := p.n0
  let mut act ← p.setup n
  repeat
    let (t, _) ← minOf act 1
    if t ≥ floorMs * 1250000 || n * 2 > p.maxN then break
    n := n * 2
    act ← p.setup n
  let act2 ← p.setup (2 * n)
  let (a, oka) ← minOf act 3
  let (b, okb) ← minOf act2 3
  if pass a b then return ⟨n, a, b, oka && okb⟩
  let (a', oka') ← minOf act 3
  let (b', okb') ← minOf act2 3
  return ⟨n, min a a', min b b', oka && okb && oka' && okb'⟩

/-- Runs one probe, prints its row; 1 on failure. -/
def runProbe (p : Probe) : IO Nat := do
  let r ← measure p
  let below := r.t1 < floorMs * 1000000
  let okT := pass r.t1 r.t2
  let status :=
    if !r.ok then "FAIL (entry point refused the input or returned an unexpected shape)"
    else if okT then (if below then "ok (below floor)" else "ok")
    else match p.known with
      | some k => s!"WARN known {k}: super-linear"
      | none => "FAIL super-linear"
  let note := match p.known with
    | some k => if r.ok && okT then s!"  NOTE: known {k} probe is within {ratioMax}x at this n (check `n` and 2n series before removing the tag)" else ""
    | none => ""
  IO.println s!"  {p.name} [{p.entry}] n={r.n} t(n)={ms r.t1} ms t(2n)={ms r.t2} ms ratio={ratioS r.t2 r.t1} {status}{note}"
  (← IO.getStdout).flush
  if !r.ok then return 1
  if okT then return 0
  return if p.known.isSome then 0 else 1

/-! ## Building inputs -/

/-- `f 0 ++ f 1 ++ … ++ f (n-1)`. -/
def gen (n : Nat) (f : Nat → String) : String := Id.run do
  let mut s := ""
  for i in [0:n] do
    s := s ++ f i
  return s

/-- Zero-padded decimal. -/
def pad (w n : Nat) : String :=
  let s := toString n
  String.ofList (List.replicate (w - s.length) '0') ++ s

/-- `N 0 obj … endobj` for object `k`. -/
def objBytes (k : Nat) (body : ByteArray) : ByteArray :=
  s!"{k} 0 obj\n".toUTF8 ++ body ++ "\nendobj\n".toUTF8

/-- A stream object body. -/
def streamBody (dictExtra : String) (data : ByteArray) : ByteArray :=
  s!"<< {dictExtra} /Length {data.size} >>\nstream\n".toUTF8 ++ data ++ "\nendstream".toUTF8

/-- A PDF whose objects `1 …` are `bodies`, with a classic xref table; also the offset of
the `xref` keyword. Root is object 1. -/
def mkPdfX (bodies : Array ByteArray) : ByteArray × Nat := Id.run do
  let mut out := "%PDF-1.7\n".toUTF8
  let mut offs : Array Nat := #[]
  for b in bodies do
    offs := offs.push out.size
    out := out ++ objBytes offs.size b
  let xr := out.size
  let mut x := s!"xref\n0 {bodies.size + 1}\n0000000000 65535 f \n"
  for o in offs do
    x := x ++ s!"{pad 10 o} 00000 n \n"
  x := x ++ s!"trailer\n<< /Size {bodies.size + 1} /Root 1 0 R >>\nstartxref\n{xr}\n%%EOF\n"
  return (out ++ x.toUTF8, xr)

/-- `mkPdfX` without the offset. -/
def mkPdf (bodies : Array ByteArray) : ByteArray := (mkPdfX bodies).1

/-- Big-endian bytes of `v` in `w` bytes. -/
def be (w v : Nat) : ByteArray := Id.run do
  let mut b := ByteArray.empty
  for i in [0:w] do
    b := b.push (UInt8.ofNat ((v >>> (8 * (w - 1 - i))) % 256))
  return b

/-- A PDF with an xref **stream**: `plain` objects `1 …`, then (when `packed` is not empty)
an object stream holding the `packed` bodies, then the xref stream. Root is object 1. -/
def mkPdfXS (plain packed : Array ByteArray) : ByteArray := Id.run do
  let p := plain.size
  let c := packed.size
  let osNum := p + 1
  let firstPacked := p + 2
  let xrNum := if c == 0 then p + 1 else p + c + 2
  let mut offs : Array Nat := #[]
  let mut out := "%PDF-1.7\n".toUTF8
  for b in plain do
    offs := offs.push out.size
    out := out ++ objBytes offs.size b
  let mut ent := be 1 0 ++ be 4 0 ++ be 4 65535
  for o in offs do
    ent := ent ++ be 1 1 ++ be 4 o ++ be 4 0
  if c > 0 then
    let mut hdr := ""
    let mut body := ByteArray.empty
    for i in [0:c] do
      hdr := hdr ++ s!"{firstPacked + i} {body.size} "
      body := body ++ packed[i]?.getD ByteArray.empty ++ " ".toUTF8
    let h := hdr.toUTF8
    ent := ent ++ be 1 1 ++ be 4 out.size ++ be 4 0
    out := out ++ objBytes osNum (streamBody s!"/Type /ObjStm /N {c} /First {h.size}" (h ++ body))
    for i in [0:c] do
      ent := ent ++ be 1 2 ++ be 4 osNum ++ be 4 i
  ent := ent ++ be 1 1 ++ be 4 out.size ++ be 4 0
  let xr := out.size
  out := out ++ objBytes xrNum
    (streamBody s!"/Type /XRef /Size {xrNum + 1} /W [1 4 4] /Root 1 0 R" ent)
  return out ++ s!"startxref\n{xr}\n%%EOF\n".toUTF8

/-- Box of a page wide enough for `n` glyphs in one line. -/
def wideBox : String := "[0 0 100000000 100]"

/-- Box of a page for painting probes. -/
def smallBox : String := "[0 0 200 200]"

/-- The standard one-page document: Helvetica is object 5, `extra` objects follow from 6. -/
def page1 (box content : String) (resources : String := "/Font << /F1 5 0 R >>")
    (catalogExtra : String := "") (pageExtra : String := "") (extra : Array ByteArray := #[]) :
    ByteArray :=
  mkPdf (#[
    s!"<< /Type /Catalog /Pages 2 0 R {catalogExtra} >>".toUTF8,
    "<< /Type /Pages /Kids [3 0 R] /Count 1 >>".toUTF8,
    s!"<< /Type /Page /Parent 2 0 R /MediaBox {box} /Contents 4 0 R /Resources << {resources} >> {pageExtra} >>".toUTF8,
    streamBody "" content.toUTF8,
    "<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica >>".toUTF8] ++ extra)

/-! ## Probe constructors -/

/-- Opens the bytes with `lim` and reads the page count. -/
def openP (name : String) (n0 maxN : Nat) (mk : Nat → ByteArray) (pages : Nat → Nat := fun _ => 1)
    (lim : Limits := {}) (repaired : Bool := false) (known : Option String := none) : Probe where
  name := name
  entry := "Api.openBytes"
  n0 := n0
  maxN := maxN
  known := known
  setup n := prep (mk n) fun bytes =>
    match Api.openBytes bytes { limits := lim } with
    | .ok d => (d.pageCount == pages n && d.repaired == repaired, d.pageCount + 1)
    | .error _ => (false, 0)

/-- Opens the document once (untimed) and times `act` on it. -/
def onDoc (name entry : String) (n0 maxN : Nat) (mk : Nat → ByteArray)
    (act : Nat → Api.Document → Bool × Nat) (lim : Limits := {}) (known : Option String := none) :
    Probe where
  name := name
  entry := entry
  n0 := n0
  maxN := maxN
  known := known
  setup n := match Api.openBytes (mk n) { limits := lim } with
    | .ok d => prep d (act n)
    | .error _ => pure (pure (false, 0))

/-- Page text: `expect n` glyphs. -/
def textP (name : String) (n0 maxN : Nat) (mk : Nat → ByteArray) (expect : Nat → Nat := id)
    (known : Option String := none) : Probe :=
  onDoc name "Api.pageText" n0 maxN mk (known := known) fun n d =>
    match Api.pageText d 0 with
    | .ok t => (t.glyphs.size == expect n, t.glyphs.size + t.lines.size + 1)
    | .error _ => (false, 0)

/-- Rendering at zoom 1. -/
def renderP (name : String) (n0 maxN : Nat) (mk : Nat → ByteArray) (known : Option String := none) :
    Probe :=
  onDoc name "Api.renderPage" n0 maxN mk (known := known) fun _ d =>
    match Api.renderPage d 0 1 with
    | .ok img => (img.data.size == 4 * img.w * img.h, img.data.size + 1)
    | .error _ => (false, 0)

/-- Content of a text page: `BT /F1 10 Tf 0 50 Td …body… ET`. -/
def textPage (body : String) (resources : String := "/Font << /F1 5 0 R >>")
    (extra : Array ByteArray := #[]) : ByteArray :=
  page1 wideBox s!"BT /F1 10 Tf 0 50 Td {body} ET" resources (extra := extra)

/-- Content of a painting page. -/
def paintPage (body : String) (resources : String := "") (extra : Array ByteArray := #[]) :
    ByteArray :=
  page1 smallBox body resources (extra := extra)

/-- Grid position of item `i` inside the 200 × 200 page. -/
def gx (i : Nat) : Nat := (i * 7) % 190
/-- Grid position of item `i` inside the 200 × 200 page. -/
def gy (i : Nat) : Nat := (i * 13 / 7) % 190

/-! ## Probes that were linear when measured (2026-11-25) and the wave-1 fixes -/

/-- A catalog with `n` keys and a page tree of `n` kids. -/
def kidsDoc (n : Nat) : ByteArray :=
  mkPdf (#[
    "<< /Type /Catalog /Pages 2 0 R >>".toUTF8,
    s!"<< /Type /Pages /Kids [{gen n fun i => s!"{i + 3} 0 R "}] /Count {n} >>".toUTF8] ++
    (Array.range n).map fun _ =>
      "<< /Type /Page /Parent 2 0 R /MediaBox [0 0 10 10] >>".toUTF8)

/-- The base document plus `n` incremental revisions rewriting the font object. -/
def revisionsDoc (n : Nat) : ByteArray := Id.run do
  let (base, xr) := mkPdfX #[
    "<< /Type /Catalog /Pages 2 0 R >>".toUTF8,
    "<< /Type /Pages /Kids [3 0 R] /Count 1 >>".toUTF8,
    "<< /Type /Page /Parent 2 0 R /MediaBox [0 0 10 10] >>".toUTF8]
  let mut out := base
  let mut prev := xr
  for i in [0:n] do
    let off := out.size
    out := out ++ objBytes 3 s!"<< /Type /Page /Parent 2 0 R /MediaBox [0 0 10 10] /R {i} >>".toUTF8
    let xo := out.size
    out := out ++ s!"xref\n3 1\n{pad 10 off} 00000 n \ntrailer\n<< /Size 4 /Root 1 0 R /Prev {prev} >>\nstartxref\n{xo}\n%%EOF\n".toUTF8
    prev := xo
  return out

/-- The probes measured linear before 13.3 and the two wave-1 fixes (13.1, 13.2). -/
def baseline : List Probe := [
  openP "objects" 2000 1000000 (fun n =>
    page1 smallBox "" (extra := (Array.range n).map fun i => s!"<< /N {i} >>".toUTF8)),
  openP "page-tree-kids" 500 100000 kidsDoc (pages := id) (known := some "13.22"),
  textP "tj-ops" 1000 1000000 (fun n => textPage (gen n fun _ => "(a) Tj ")),
  textP "tj-array" 1000 1000000 (fun n => textPage s!"[{gen n fun _ => "(a) -1 "}] TJ"),
  textP "long-string" 1000 4000000 (fun n => textPage s!"({String.ofList (List.replicate n 'a')}) Tj"),
  textP "bdc-emc" 1000 1000000 (fun n => textPage (gen n fun _ => "/Span <</MCID 0>> BDC (a) Tj EMC ")),
  openP "revisions" 100 100000 revisionsDoc (lim := { maxRevisions := 1000000 }) (known := some "13.23"),
  onDoc "link-annots" "Api.pageLinks" 256 2048
    (fun n => page1 smallBox "" (pageExtra := s!"/Annots [{gen n fun i => s!"{i + 6} 0 R "}]")
      (extra := (Array.range n).map fun _ =>
        "<< /Type /Annot /Subtype /Link /Rect [0 0 10 10] /Dest [3 0 R /Fit] >>".toUTF8))
    (fun n d => match Api.pageLinks d 0 with
      | .ok ls => (ls.length == n, ls.length + 1)
      | .error _ => (false, 0)),
  renderP "small-paths" 500 1000000 (fun n =>
    paintPage (gen n fun i => s!"{gx i} {gy i} m {gx i + 3} {gy i} l {gx i} {gy i + 3} l f ")),
  renderP "rect-fills" 500 1000000 (fun n =>
    paintPage (gen n fun i => s!"{gx i} {gy i} 5 5 re f ")),
  renderP "strokes" 500 1000000 (fun n =>
    paintPage (gen n fun i => s!"{gx i} {gy i} m {gx i + 5} {gy i + 5} l S ")),
  renderP "bezier-strokes" 500 1000000 (fun n =>
    paintPage (gen n fun i => s!"{gx i} {gy i} m {gx i + 2} {gy i + 5} {gx i + 5} {gy i + 5} {gx i + 6} {gy i} c S ")),
  renderP "clipped-fills" 500 1000000 (fun n =>
    paintPage (gen n fun i => s!"q {gx i} {gy i} 10 10 re W n 0 0 200 200 re f Q ")),
  renderP "stacked-clips" 200 1000000 (fun n =>
    paintPage (s!"q " ++ gen n (fun i => s!"{i % 50} 0 200 200 re W n ") ++ "0 0 200 200 re f Q")),
  -- 13.1: one path of n segments (quadratic before wave 1)
  renderP "one-path-segments" 500 60000 (fun n =>
    paintPage (s!"0 0 m " ++ gen n (fun i => s!"{gx i} {gy i} l ") ++ "S")),
  -- 13.2: a dictionary of n keys (quadratic before wave 1)
  openP "dict-keys" 1000 1000000 (fun n =>
    page1 smallBox "" (catalogExtra := gen n fun i => s!"/K{i} {i} ")),
  textP "inline-dict-keys" 1000 1000000 (fun n =>
    page1 wideBox s!"BT /F1 10 Tf 0 50 Td (a) Tj ET q BI /W 1 /H 1 /BPC 8 /CS /G {gen n fun i => s!"/K{i} {i} "} ID \x00 EI Q")
    (expect := fun _ => 1) ]

/-! ## Probes added by 13.3 (`not yet probed`) -/

/-- Resources of `n` entries in category `cat`, entry `i` being `entry i`. -/
def resDict (cat : String) (n : Nat) (entry : Nat → String) : String :=
  s!"/{cat} << {gen n fun i => s!"/R{i} {entry i} "}>>"

/-- `n` distinct objects `Helvetica`, numbered from 6. -/
def fontObjs (n : Nat) : Array ByteArray :=
  (Array.range n).map fun _ => "<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica >>".toUTF8

/-- Unused objects `<< /N i >>`. -/
def unusedBodies (n : Nat) : Array ByteArray :=
  (Array.range n).map fun i => s!"<< /N {i} >>".toUTF8

/-- The three objects every one-page xref-stream document starts with. -/
def head3 (pageExtra : String := "") : Array ByteArray := #[
  "<< /Type /Catalog /Pages 2 0 R >>".toUTF8,
  "<< /Type /Pages /Kids [3 0 R] /Count 1 >>".toUTF8,
  s!"<< /Type /Page /Parent 2 0 R /MediaBox [0 0 10 10] {pageExtra} >>".toUTF8]

/-- `n` unused objects described by an xref stream (no object stream). -/
def xrefStmDoc (n : Nat) : ByteArray := mkPdfXS (head3 ++ unusedBodies n) #[]

/-- `n` unused objects inside an object stream. -/
def objStmDoc (n : Nat) : ByteArray := mkPdfXS head3 (unusedBodies n)

/-- `n` link annotations inside an object stream, each fetched by `pageLinks`. -/
def objStmLinksDoc (n : Nat) : ByteArray :=
  mkPdfXS (head3 (s!"/Annots [{gen n fun i => s!"{i + 5} 0 R "}]"))
    ((Array.range n).map fun _ =>
      "<< /Type /Annot /Subtype /Link /Rect [0 0 10 10] /Dest [3 0 R /Fit] >>".toUTF8)

/-- The outline of `n` flat items. -/
def outlineDoc (n : Nat) : ByteArray :=
  page1 smallBox "" (catalogExtra := "/Outlines 6 0 R") (extra :=
    #[s!"<< /Type /Outlines /First 7 0 R /Last {n + 6} 0 R /Count {n} >>".toUTF8] ++
    (Array.range n).map fun i =>
      s!"<< /Title (Item {i}) /Parent 6 0 R {if i > 0 then s!"/Prev {i + 6} 0 R " else ""}{if i + 1 < n then s!"/Next {i + 8} 0 R " else ""}/Dest [3 0 R /Fit] >>".toUTF8)

/-- A broken file (no xref, no trailer) of `n` objects, to run the repair scan. -/
def repairDoc (n : Nat) : ByteArray := Id.run do
  let mut s := "%PDF-1.7\n"
  s := s ++ "1 0 obj\n<< /Type /Catalog /Pages 2 0 R >>\nendobj\n"
  s := s ++ "2 0 obj\n<< /Type /Pages /Kids [3 0 R] /Count 1 >>\nendobj\n"
  s := s ++ "3 0 obj\n<< /Type /Page /Parent 2 0 R /MediaBox [0 0 10 10] >>\nendobj\n"
  for i in [0:n] do
    s := s ++ s!"{i + 4} 0 obj\n<< /N {i} >>\nendobj\n"
  return s.toUTF8

/-- `n` highlight marks on page 0 for the writer. -/
def marksOf (n : Nat) : List Write.Annots.Mark :=
  (List.range n).map fun i =>
    let x : Rat := gx i
    let y : Rat := gy i
    { page := 0, kind := .highlight, quads := [Write.Annots.Quad.ofBox x y (x + 10) (y + 10)],
      rect := ⟨x, y, x + 10, y + 10⟩, color := (1, 1, 0), id := i + 1,
      date := "D:20260101000000Z" }

open SafePdf.Shell.App in
/-- A store of `n` highlights on page 0. -/
def storeOf (n : Nat) : Marks.Store := Id.run do
  let mut s : Marks.Store := {}
  for i in [0:n] do
    let x : Rat := ((i % 1000 * 20 : Nat) : Rat)
    let y : Rat := ((i / 1000 * 20 : Nat) : Rat)
    match s.addHighlight 0 .yellow [⟨x, y, x + 10, y + 10⟩] with
    | some (s', _) => s := s'
    | none => pure ()
  return s

open SafePdf.Shell.App in
/-- The XFDF import limits, raised so that the probe sizes are not refused. -/
def bigXfdf : Xfdf.Limits :=
  { maxBytes := 1 <<< 30, maxNodes := 1 <<< 30, maxMarks := 1 <<< 30 }

open SafePdf.Shell.App in
/-- Probes of the shell's own code over a store or an XFDF text. -/
def shellProbes : List Probe := [
  { name := "xfdf-export", entry := "Xfdf.toXfdf", n0 := 200, maxN := 100000, known := some "13.28",
    setup := fun n => prep (storeOf n) fun s =>
      let x := Xfdf.toXfdf s (fun _ => none) "D:20260101000000Z"
      (x.length > n, x.length) },
  { name := "xfdf-import", entry := "Xfdf.readXfdf", n0 := 200, maxN := 100000, known := some "13.28",
    setup := fun n => prep (Xfdf.toXfdf (storeOf n) (fun _ => none) "D:20260101000000Z").toUTF8
      fun b => match Xfdf.readXfdf bigXfdf b with
        | .ok rep =>
          let (s, ids, _) := Xfdf.importItems {} rep.items
          (ids.length == n, s.marks.size + 1)
        | .error _ => (false, 0) } ]

/-- The text of a page of `n` glyphs "abab…" (untimed). -/
def abPage (n : Nat) : Except Api.Error Text.PageText := do
  let doc := textPage s!"({String.ofList ((List.range n).map fun i => if i % 2 == 0 then 'a' else 'b')}) Tj"
  let d ← Api.openBytes doc
  Api.pageTextCore d 0

/-- The cells of the reading order of a page of `n` glyphs (the first half of
`PageIndex.ofText`). -/
def searchCellsP (known : Option String := none) : Probe where
  name := "search-cells"
  entry := "Select.cellsOf + cellsHidden"
  n0 := 1000
  maxN := 2000000
  known := known
  setup n := match abPage n with
    | .error _ => pure (pure (false, 0))
    | .ok pt => prep pt fun pt =>
        let cs := Shell.App.Select.cellsOf {} pt.lines
        let hs := Shell.App.Select.cellsHidden {} pt.lines
        (cs.size == n && hs.size == n, cs.size + hs.size + 1)

open SafePdf.Shell.App.Select in
/-- `n` synthetic cells "a", "b", … (untimed). -/
def synthCells (n : Nat) : Array Cell :=
  (Array.range n).map fun i => { text := if i % 2 == 0 then "a" else "b", sep := "", box := default, line := 0 }

open SafePdf.Shell.App.Select in
/-- The normalised search text of `n` cells (the second half of `PageIndex.ofText`). -/
def searchNormP (known : Option String := none) : Probe where
  name := "search-normalize"
  entry := "Select.normChars"
  n0 := 1000
  maxN := 4000000
  known := known
  setup n := prep (synthCells n) fun cs =>
    let hay := normChars cs
    (hay.size == n, hay.size + 1)

open SafePdf.Shell.App.Select in
/-- The hits of two queries ("ab", "a") in a page index of `n` characters "abab…". -/
def searchHitsP (known : Option String := none) : Probe where
  name := "search-hits"
  entry := "Select.PageIndex.hits"
  n0 := 1000
  maxN := 4000000
  known := known
  setup n :=
    let hay : Array (Char × Nat) := (Array.range n).map fun i => (if i % 2 == 0 then 'a' else 'b', i)
    prep ({ cells := #[], hay, lineDirs := #[] } : PageIndex) fun ix =>
      let h1 := ix.hits (normQuery "ab")
      let h2 := ix.hits (normQuery "a")
      (h1.size == n / 2 && h2.size == (n + 1) / 2, h1.size + h2.size + 1)

/-- A list of `n` numbers through the worker protocol's list codec. -/
def workerP : Probe where
  name := "worker-list-decode"
  entry := "Protocol.decodeBody (Codec.list nat)"
  n0 := 1000
  maxN := 4000000
  setup n :=
    let c := Shell.Worker.Protocol.Codec.list Shell.Worker.Protocol.Codec.nat
      Shell.Worker.Protocol.Codec.nat_ne
    let xs := (List.range n).map fun i => i * 1000
    prep (c.enc xs) fun b =>
      match Shell.Worker.Protocol.decodeBody c b with
      | .ok ys => (ys.length == n, ys.length + 1)
      | .error _ => (false, 0)

/-- The probes of this task. -/
def newProbes : List Probe := [
  textP "font-lookups" 200 100000 (fun n =>
    textPage (gen n fun i => s!"/R{i} 10 Tf (a) Tj ") (resources := resDict "Font" n fun _ => "5 0 R"))
    (expect := id) (known := some "13.24"),
  renderP "xobject-lookups" 200 100000 (fun n =>
    paintPage (gen n fun i => s!"/R{i} Do ")
      (resources := resDict "XObject" n fun _ => "6 0 R")
      (extra := #[streamBody "/Type /XObject /Subtype /Form /BBox [0 0 1 1]" "0 0 1 1 re f".toUTF8]))
    (known := some "13.24"),
  renderP "extgstate-lookups" 200 100000 (fun n =>
    paintPage (gen n fun i => s!"/R{i} gs 0 0 5 5 re f ")
      (resources := resDict "ExtGState" n fun _ => "<< /CA 0.5 >>"))
    (known := some "13.24"),
  renderP "colorspace-lookups" 200 100000 (fun n =>
    paintPage (gen n fun i => s!"/R{i} cs 0.5 sc 0 0 5 5 re f ")
      (resources := resDict "ColorSpace" n fun _ => "[/CalGray << /WhitePoint [0.95 1 1.09] >>]"))
    (known := some "13.24"),
  textP "distinct-fonts" 100 20000 (fun n =>
    textPage (gen n fun i => s!"/R{i} 10 Tf (a) Tj ")
      (resources := resDict "Font" n fun i => s!"{i + 6} 0 R") (extra := fontObjs n))
    (expect := id) (known := some "13.24"),
  openP "objstm-members" 200 1000000 objStmDoc,
  onDoc "objstm-fetch" "Api.pageLinks" 256 2048 objStmLinksDoc (known := some "13.25") fun n d =>
    match Api.pageLinks d 0 with
    | .ok ls => (ls.length == n, ls.length + 1)
    | .error _ => (false, 0),
  openP "xref-stream-entries" 500 2000000 xrefStmDoc,
  onDoc "outline-items" "Api.outline" 500 100000 outlineDoc (known := some "13.26") fun n d =>
    let o := Api.outline d
    (o.length == n, o.length + 1),
  onDoc "dests-names" "Api.pageLinks" 256 2048 (known := some "13.24")
    (fun n => page1 smallBox "" (pageExtra := s!"/Annots [{gen n fun i => s!"{i + 6} 0 R "}]")
      (catalogExtra := s!"/Dests << {gen n fun i => s!"/N{i} [3 0 R /Fit] "}>>")
      (extra := (Array.range n).map fun i =>
        s!"<< /Type /Annot /Subtype /Link /Rect [0 0 10 10] /Dest /N{i} >>".toUTF8))
    (fun n d => match Api.pageLinks d 0 with
      | .ok ls => (ls.length == n, ls.length + 1)
      | .error _ => (false, 0)),
  searchCellsP, searchNormP (known := some "13.27"), searchHitsP,
  renderP "inline-images" 200 100000 (fun n =>
    paintPage (gen n fun i => s!"q 5 0 0 5 {gx i} {gy i} cm BI /W 1 /H 1 /BPC 8 /CS /G ID \x00 EI Q ")),
  renderP "path-under-full-q-stack" 500 60000 (fun n =>
    paintPage (gen 255 (fun _ => "q ") ++ "0 0 m " ++ gen n (fun i => s!"{gx i} {gy i} l ") ++ "f")),
  onDoc "write-marks" "Annots.writeMarks" 32 4096 (fun _ => page1 smallBox "")
    (fun n d => match Write.Annots.writeMarks d.limits d.doc (marksOf n) with
      | .ok b => (b.size > 0, b.size)
      | .error _ => (false, 0)),
  openP "repair-scan" 1000 1000000 repairDoc (repaired := true),
  workerP ] ++ shellProbes

/-- Every probe. -/
def probes : List Probe := baseline ++ newProbes

/-- Runs the suite: the number of failing probes. -/
def run : IO Nat := do
  let mut f := 0
  IO.println s!"  scaling: t(2n) <= {ratioMax} x t(n), min of 3 runs, n calibrated to t(n) >= {floorMs} ms"
  for p in probes do
    f := f + (← runProbe p)
  return f

end SafePdf.Tests.Scaling
