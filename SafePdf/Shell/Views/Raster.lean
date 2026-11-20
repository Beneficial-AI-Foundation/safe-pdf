import SafePdf.Shell.Views.Common
import SafePdf.Shell.Views.Summary
import SafePdf.Shell.Views.Pages

/-!
# `raster` view: full-page rasterisation, image files and per-page timing (task 7.4)

Plan.md §6 Phase 7 (exit M7: "≥ 95% of corpus pages within perceptual threshold; median page
< 100 ms compiled"; "Faithfulness: pixel-differential vs MuPDF/pdf.js (perceptual diff)") and
the M7 row of the MVP / visibility track. The differential comparator
`Tests/differential/pixels.py` reads this view's `--json` output and the image files it writes;
`docs/raster.md` describes the metric and the measurements.

Each page is rendered by the verified full-page renderer
`Core.Raster.Glyph.renderDocPage limits doc page zoom .r0 budget` (content decode, display
list with real font advances, glyph outlines, images, shadings, transparency) at
`zoom = DPI / 72` pixels per page unit. The page's own `/Rotate` is applied (user rotation
`.r0`) and the CropBox is the visible area, as `mutool draw` does. Every page gets a **fresh
decoded-bytes budget** (`Filter.Budget.init`): pages are rendered independently, as a viewer
renders them on demand, so a large early page cannot starve a later one and the time of a page
does not depend on the pages before it.

Environment:
* `SAFEPDF_PAGE=N` (1-based) renders only page `N` (default: every page, document order);
* `SAFEPDF_DPI=D` resolution in dots per inch, a positive integer (default 72; MuPDF's
  `mutool draw` default is also 72);
* `SAFEPDF_RASTER_DIR=dir` writes each rendered page to `dir/page-N.ppm` (binary PPM `P6`,
  RGB, alpha dropped — the page is painted onto opaque white). Without it pages are only
  rendered and timed;
* `SAFEPDF_RASTER_FORMAT=png` writes `dir/page-N.png` instead: 8-bit RGB, one zlib stream of
  stored (uncompressed) DEFLATE blocks (`Core.Filter.Deflate.zlibStored`), filter type 0 on
  every row, CRC-32 computed here. Any other value (or none) means PPM.

**Timing.** The render time of a page is wall-clock time (`IO.monoNanosNow`) around the pure
`renderDocPage` call, which runs inside `IO.lazyPure`; the result is matched (its pixel buffer
size is read) before the clock is read again, so the computation cannot float past the second
clock read (ledger gotcha "timing a pure call"). Writing the file is not included. The
inspector is a compiled executable, so these are compiled times.

## Text form

A header (`file`, `open`, `pages`, `dpi`), one line per page
`page N: WxH px, T ms[ -> FILE][ (error: …)]`, then a `total:` line with the number of pages
rendered, failed, the median and maximum page time and the sum.

## `--json`

One object per rendered page
`{"page","width","height","dpi","ms","nanos","status","error","file"}` (`status` is `"ok"` or
`"error"`, `error` is `null` or a message, `file` is `null` when no directory is set, `ms` a
JSON number with three decimals), then
`{"summary": {"path","open","pages","rendered","errors","dpi","parseMs","medianMs","maxMs",
"totalMs"}}`, or `{"summary": {"path","open","error"}}` when the document does not open.
-/

namespace SafePdf.Shell.Views.Raster

open SafePdf.Shell
open SafePdf.Core.Doc
open SafePdf.Core.Filter (Budget)
open SafePdf.Core.Raster (Clip.Image)

/-! ## Image files -/

/-- The RGB bytes of an RGBA image, rows top to bottom; with `filterBytes` every row is
preceded by a PNG filter-type byte `0`. -/
def rgbBytes (img : Clip.Image) (filterBytes : Bool) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (img.h * (3 * img.w + 1))
  for y in [0:img.h] do
    if filterBytes then out := out.push 0
    let row := 4 * img.w * y
    for x in [0:img.w] do
      let i := row + 4 * x
      out := out.push (img.data[i]?.getD 255)
      out := out.push (img.data[i + 1]?.getD 255)
      out := out.push (img.data[i + 2]?.getD 255)
  return out

/-- A binary PPM (`P6`, maxval 255) of an RGBA image (alpha dropped). -/
def ppmBytes (img : Clip.Image) : ByteArray :=
  s!"P6\n{img.w} {img.h}\n255\n".toUTF8 ++ rgbBytes img false

/-- The CRC-32 table (reflected polynomial `0xEDB88320`, ISO 3309 / PNG §5.5). -/
def crcTable : Array UInt32 :=
  (Array.range 256).map fun n =>
    (List.range 8).foldl (fun (c : UInt32) _ =>
      if c &&& 1 == 1 then (0xEDB88320 : UInt32) ^^^ (c >>> 1) else c >>> 1) n.toUInt32

/-- CRC-32 of `bs` (PNG chunk checksum). -/
def crc32 (bs : ByteArray) : UInt32 :=
  let c := bs.foldl (fun c b =>
    (crcTable[((c ^^^ b.toUInt32) &&& 0xFF).toNat]?.getD 0) ^^^ (c >>> 8)) 0xFFFFFFFF
  c ^^^ 0xFFFFFFFF

/-- Four big-endian bytes. -/
def be32 (n : Nat) : ByteArray :=
  ⟨#[(n / 16777216 % 256).toUInt8, (n / 65536 % 256).toUInt8, (n / 256 % 256).toUInt8,
    (n % 256).toUInt8]⟩

/-- One PNG chunk: length, type, data, CRC-32 of type and data. -/
def pngChunk (type : String) (data : ByteArray) : ByteArray :=
  let td := type.toUTF8 ++ data
  be32 data.size ++ td ++ be32 (crc32 td).toNat

/-- An 8-bit RGB PNG of an RGBA image (alpha dropped), stored DEFLATE blocks. -/
def pngBytes (img : Clip.Image) : ByteArray :=
  let sig : ByteArray := ⟨#[137, 80, 78, 71, 13, 10, 26, 10]⟩
  let ihdr := be32 img.w ++ be32 img.h ++ ⟨#[8, 2, 0, 0, 0]⟩
  sig ++ pngChunk "IHDR" ihdr ++
    pngChunk "IDAT" (SafePdf.Core.Filter.Deflate.zlibStored (rgbBytes img true)) ++
    pngChunk "IEND" ByteArray.empty

/-- Output image format. -/
inductive Format where
  /-- Binary PPM `P6`. -/
  | ppm
  /-- PNG, stored DEFLATE. -/
  | png

/-- File extension of a format. -/
def Format.ext : Format → String
  | .ppm => "ppm"
  | .png => "png"

/-- File bytes of an image in a format. -/
def Format.encode : Format → Clip.Image → ByteArray
  | .ppm => ppmBytes
  | .png => pngBytes

/-! ## Rendering and timing -/

/-- What the view records for one page. -/
structure PageOut where
  /-- 1-based page number. -/
  number : Nat
  /-- Width in pixels (0 on error). -/
  width : Nat := 0
  /-- Height in pixels (0 on error). -/
  height : Nat := 0
  /-- Wall-clock render time in nanoseconds. -/
  nanos : Nat := 0
  /-- Render error, if any. -/
  error : Option Error := none
  /-- The file written, if any. -/
  file : Option String := none

/-- Render page `k` (0-based) with a fresh budget, timing the pure call. Returns the record and
the image (on success). -/
def renderTimed (limits : Limits) (doc : Doc) (k : Nat) (zoom : Rat) :
    IO (PageOut × Option Clip.Image) := do
  if h : k < doc.pages.size then
    let page := doc.pages[k]
    let t0 ← IO.monoNanosNow
    let r ← IO.lazyPure fun _ =>
      (SafePdf.Core.Raster.Glyph.renderDocPage limits doc page zoom .r0 (Budget.init limits)).1
    -- `lazyPure` runs the render when this action runs (as `Inspect.load` times the parse);
    -- matching on the result in `IO` before reading the clock again keeps the evaluation of
    -- the image between the two clock reads.
    let size ← match r with
      | .ok img => pure img.data.size
      | .error _ => pure 0
    let t1 ← IO.monoNanosNow
    let nanos := t1 - t0
    if size % 4 != 0 then IO.eprintln s!"inspect: page {k + 1}: odd buffer size {size}"
    match r with
    | .ok img => return ({ number := k + 1, width := img.w, height := img.h, nanos }, some img)
    | .error e => return ({ number := k + 1, nanos, error := some e }, none)
  else
    return ({ number := k + 1, error := some (.malformed 0 "page index out of range") }, none)

/-- Median of a list of naturals (lower median; `0` for the empty list). -/
def median (xs : List Nat) : Nat :=
  let s := xs.toArray.qsort (· < ·)
  s[(s.size - 1) / 2]?.getD 0

/-- Milliseconds with three decimals as a JSON number. -/
def msJson (nanos : Nat) : String := formatMs nanos

/-- JSON line of one page. -/
def pageJson (dpi : Nat) (p : PageOut) : String :=
  jsonObject
    [ ("page", toString p.number), ("width", toString p.width), ("height", toString p.height),
      ("dpi", toString dpi), ("ms", msJson p.nanos), ("nanos", toString p.nanos),
      ("status", jsonString (if p.error.isSome then "error" else "ok")),
      ("error", match p.error with
        | some e => jsonString (renderError e)
        | none => "null"),
      ("file", match p.file with
        | some f => jsonString f
        | none => "null") ]

/-- Text line of one page. -/
def pageText (p : PageOut) : String :=
  let f := match p.file with
    | some f => s!" -> {f}"
    | none => ""
  let e := match p.error with
    | some e => s!" (error: {renderError e})"
    | none => ""
  s!"page {p.number}: {p.width}x{p.height} px, {formatMs p.nanos} ms{f}{e}"

/-- Parse a positive natural from an environment variable; `dflt` when unset or invalid (with a
warning on stderr). -/
def envNat (name : String) (dflt : Nat) : IO (Option Nat) := do
  match ← IO.getEnv name with
  | none => return some dflt
  | some s =>
    match s.trimAscii.toString.toNat? with
    | some n => return some n
    | none =>
      IO.eprintln s!"inspect: {name}='{s}' is not a number"
      return none

/-- The `raster` view. -/
def view : View where
  name := "raster"
  description := "render pages to pixels and time them (SAFEPDF_PAGE=N, SAFEPDF_DPI=D (72), SAFEPDF_RASTER_DIR=dir writes page-N.ppm, SAFEPDF_RASTER_FORMAT=png)"
  run cfg i := do
    match Pages.docOf cfg.limits i.result with
    | .error e =>
      if cfg.json then
        IO.println (jsonObject [ ("summary", jsonObject
          [ ("path", jsonString i.path), ("open", jsonString (Summary.openMode i.result)),
            ("error", jsonString (renderError e)) ]) ])
      else
        IO.println s!"file:       {i.path}\nopen:       {Summary.openMode i.result}\nerror:      {renderError e}"
    | .ok doc =>
      let some dpi ← envNat "SAFEPDF_DPI" 72 | return
      if dpi == 0 || dpi > 2400 then
        IO.eprintln s!"inspect: SAFEPDF_DPI must be in 1..2400"
        return
      let zoom : Rat := (dpi : Rat) / 72
      let fmt : Format := if (← IO.getEnv "SAFEPDF_RASTER_FORMAT") == some "png" then .png else .ppm
      let dir ← IO.getEnv "SAFEPDF_RASTER_DIR"
      if let some d := dir then IO.FS.createDirAll d
      let indices ← match ← IO.getEnv "SAFEPDF_PAGE" with
        | none => pure (List.range doc.pages.size)
        | some s =>
          match s.trimAscii.toString.toNat? with
          | some n =>
            if n == 0 || n > doc.pages.size then
              IO.eprintln s!"inspect: {i.path}: page {n} out of range (1..{doc.pages.size})"
              pure []
            else pure [n - 1]
          | none =>
            IO.eprintln s!"inspect: SAFEPDF_PAGE='{s}' is not a page number; rendering all pages"
            pure (List.range doc.pages.size)
      if !cfg.json then
        IO.println s!"file:       {i.path}\nopen:       {Summary.openMode i.result}\npages:      {doc.pages.size}\ndpi:        {dpi}"
      let mut outs : Array PageOut := #[]
      for k in indices do
        let (p, img?) ← renderTimed cfg.limits doc k zoom
        let mut p := p
        if let (some d, some img) := (dir, img?) then
          let path := (d : System.FilePath) / s!"page-{k + 1}.{fmt.ext}"
          IO.FS.writeBinFile path (fmt.encode img)
          p := { p with file := some path.toString }
        if cfg.json then IO.println (pageJson dpi p) else IO.println (pageText p)
        outs := outs.push p
      let times := outs.toList.map (·.nanos)
      let errs := (outs.filter (·.error.isSome)).size
      let med := median times
      let mx := times.foldl max 0
      let tot := times.foldl (· + ·) 0
      if cfg.json then
        IO.println (jsonObject [ ("summary", jsonObject
          [ ("path", jsonString i.path), ("open", jsonString (Summary.openMode i.result)),
            ("pages", toString doc.pages.size), ("rendered", toString (outs.size - errs)),
            ("errors", toString errs), ("dpi", toString dpi),
            ("parseMs", msJson i.parseNanos), ("medianMs", msJson med), ("maxMs", msJson mx),
            ("totalMs", msJson tot) ]) ])
      else
        IO.println s!"total:      {outs.size - errs} page(s) rendered, {errs} failed, median {formatMs med} ms, max {formatMs mx} ms, sum {formatMs tot} ms"

end SafePdf.Shell.Views.Raster
