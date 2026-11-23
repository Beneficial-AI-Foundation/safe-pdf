import SafePdf

/-!
# Optional content in the renderer and text extraction (task 9.r11a)

Plan.md §6 Phase 9 (optional content, ledger rows 9.r11a/9.r11b), ISO 32000-2 §8.11. One
200 × 200 page built here, drawn through the public API (`Api.renderPage`, `Api.pageText`)
under several `/OCProperties`, checks `Core.Doc.OptionalContent` and the runner's
optional content filter (`Core.Content.Run.ocTrack`, `doStep`, `Annot.ocHidden`):

* marked content `BDC /OC /name … EMC` with a group ON (painted) and OFF (not painted);
* membership dictionaries: `/P` `AnyOn` (default), `AllOn`, `AnyOff`, `AllOff` over two groups
  and over a single group;
* `/VE` visibility expressions: precedence over `/P`, nested `/And`/`/Or`/`/Not`;
* nesting: a hidden sequence inside a visible one, `BMC` of another tag inside a hidden
  sequence (its `EMC` does not end the hidden one), content after the hidden sequence closes,
  an unbalanced `EMC`;
* a group not listed in `/OCGs` and a missing `/Properties` name: visible;
* form XObjects and image XObjects with `/OC` (OFF: not painted; ON: painted);
* annotations with `/OC` (OFF: not drawn; ON: drawn);
* text in a hidden sequence: not painted and **not extracted**; visible text extracted;
* configurations: `/D /OFF`; `/BaseState /OFF` with `/ON`; `/BaseState /OFF` alone; a caller's
  state with the OFF group turned ON (`Config.setGroup`, the later layers panel) shows
  everything; no `/OCProperties`: everything painted (and the corpus papers that use `BDC /OC`
  without `/OCProperties`, arXiv 1207.7235/1706.03762/2412.19437, are unchanged).
-/

namespace SafePdf.Tests.OptionalContent

open SafePdf.Core
open SafePdf.Core.Doc.OptionalContent (Config State)

/-- Reports a failed check; 1 on failure. -/
def check (what : String) (ok : Bool) : IO Nat := do
  if ok then return 0
  IO.println s!"  FAIL optional-content: {what}"
  return 1

/-- A PDF whose objects `1 …` are the given bodies, with a correct xref table. -/
def mkPdf (objs : List String) : ByteArray := Id.run do
  let mut body := "%PDF-1.7\n"
  let mut offs : List Nat := []
  let mut i := 1
  for o in objs do
    offs := offs ++ [body.utf8ByteSize]
    body := body ++ s!"{i} 0 obj\n{o}\nendobj\n"
    i := i + 1
  let row (o : Nat) : String :=
    let s := toString o
    String.ofList (List.replicate (10 - s.length) '0') ++ s ++ " 00000 n \n"
  let x := body.utf8ByteSize
  let rows := String.join (offs.map row)
  (body ++ s!"xref\n0 {objs.length + 1}\n0000000000 65535 f \n" ++ rows ++
    s!"trailer\n<< /Size {objs.length + 1} /Root 1 0 R >>\nstartxref\n{x}\n%%EOF\n").toUTF8

/-- A stream object. -/
def strm (dict body : String) : String :=
  s!"<< {dict} /Length {body.utf8ByteSize} >>\nstream\n{body}\nendstream"

/-- Lower-left corner of test square `i` (7 per row, 25 pt apart). -/
def corner (i : Nat) : Nat × Nat := (10 + 25 * (i % 7), 10 + 25 * (i / 7))

/-- A red 10 × 10 square at test position `i`. -/
def sq (i : Nat) : String :=
  let (x, y) := corner i
  s!"1 0 0 rg {x} {y} 10 10 re f"

/-- The test cases: name, content (drawing at its own position), painted under the default
configuration (group 5 ON, group 6 OFF). -/
def cases : List (String × (Nat → String) × Bool) := [
  ("BDC ON group", fun i => s!"/OC /L1 BDC {sq i} EMC", true),
  ("BDC OFF group", fun i => s!"/OC /L2 BDC {sq i} EMC", false),
  ("OCMD AnyOn [on off]", fun i => s!"/OC /MAnyOn BDC {sq i} EMC", true),
  ("OCMD AllOn [on off]", fun i => s!"/OC /MAllOn BDC {sq i} EMC", false),
  ("OCMD AnyOff [on off]", fun i => s!"/OC /MAnyOff BDC {sq i} EMC", true),
  ("OCMD AllOff [on off]", fun i => s!"/OC /MAllOff BDC {sq i} EMC", false),
  ("OCMD AllOff off", fun i => s!"/OC /MAllOffOne BDC {sq i} EMC", true),
  ("VE [/Not off] wins over /P AllOn", fun i => s!"/OC /MVeNot BDC {sq i} EMC", true),
  ("VE [/And on [/Or off [/Not off]]]", fun i => s!"/OC /MVeNest BDC {sq i} EMC", true),
  ("VE [/And on [/Not on]]", fun i => s!"/OC /MVeFalse BDC {sq i} EMC", false),
  ("nested: OFF inside ON", fun i => s!"/OC /L1 BDC /OC /L2 BDC {sq i} EMC EMC", false),
  ("BMC inside OFF keeps it hidden", fun i => s!"/OC /L2 BDC /Span BMC EMC {sq i} EMC", false),
  ("after the OFF sequence closes", fun i => s!"/OC /L2 BDC EMC {sq i}", true),
  ("group not in /OCGs", fun i => s!"/OC /U BDC {sq i} EMC", true),
  ("missing /Properties name", fun i => s!"/OC /Nope BDC {sq i} EMC", true),
  ("form /OC OFF", fun i => let (x, y) := corner i; s!"q 1 0 0 1 {x} {y} cm /FmOff Do Q", false),
  ("form /OC ON", fun i => let (x, y) := corner i; s!"q 1 0 0 1 {x} {y} cm /FmOn Do Q", true),
  ("image /OC OFF", fun i => let (x, y) := corner i; s!"q 10 0 0 10 {x} {y} cm /ImOff Do Q", false),
  ("image /OC ON", fun i => let (x, y) := corner i; s!"q 10 0 0 10 {x} {y} cm /ImOn Do Q", true),
  ("unbalanced EMC", fun i => s!"EMC EMC {sq i}", true),
  ("form inside OFF sequence", fun i =>
    let (x, y) := corner i; s!"/OC /L2 BDC q 1 0 0 1 {x} {y} cm /FmOn Do Q EMC", false),
  ("annotation /OC OFF", fun _ => "", false),
  ("annotation /OC ON", fun _ => "", true)]

/-- Index of the first annotation case. -/
def annotCase : Nat := 21

/-- The page content: every case, then the visible and the hidden text. -/
def content : String :=
  " ".intercalate ((cases.zipIdx.map fun ((_, f, _), i) => f i) ++
    ["BT /F1 12 Tf 10 170 Td (SHOWNTEXT) Tj ET",
     "/OC /L2 BDC BT /F1 12 Tf 10 150 Td (HIDDENTEXT) Tj ET EMC",
     "/OC /L2 BDC BT /F1 12 Tf 110 150 Td (MORE) Tj ET EMC"])

/-- The fixture; `props` is the catalog's `/OCProperties` (empty: none). Objects: 5 group
"on", 6 group "off", 7/8 forms (`/OC` 6, 5), 9/10 images (`/OC` 6, 5), 11 a group not in
`/OCGs`, 12 font, 13/14 annotations (`/OC` 6, 5), 15 their appearance. -/
def fixture (props : String) : ByteArray :=
  let (ax0, ay0) := corner annotCase
  let (ax1, ay1) := corner (annotCase + 1)
  let ocmd (rest : String) := s!"<< /Type /OCMD {rest} >>"
  mkPdf [
    s!"<< /Type /Catalog /Pages 2 0 R {if props.isEmpty then "" else s!"/OCProperties {props}"} >>",
    "<< /Type /Pages /Kids [3 0 R] /Count 1 /MediaBox [0 0 200 200] >>",
    "<< /Type /Page /Parent 2 0 R /Contents 4 0 R /Annots [13 0 R 14 0 R] /Resources << " ++
      "/Font << /F1 12 0 R >> /XObject << /FmOff 7 0 R /FmOn 8 0 R /ImOff 9 0 R /ImOn 10 0 R >> " ++
      "/Properties << /L1 5 0 R /L2 6 0 R /U 11 0 R " ++
      s!"/MAnyOn {ocmd "/OCGs [5 0 R 6 0 R]"} " ++
      s!"/MAllOn {ocmd "/OCGs [5 0 R 6 0 R] /P /AllOn"} " ++
      s!"/MAnyOff {ocmd "/OCGs [5 0 R 6 0 R] /P /AnyOff"} " ++
      s!"/MAllOff {ocmd "/OCGs [5 0 R 6 0 R] /P /AllOff"} " ++
      s!"/MAllOffOne {ocmd "/OCGs 6 0 R /P /AllOff"} " ++
      s!"/MVeNot {ocmd "/OCGs [6 0 R] /P /AllOn /VE [/Not 6 0 R]"} " ++
      s!"/MVeNest {ocmd "/VE [/And 5 0 R [/Or 6 0 R [/Not 6 0 R]]]"} " ++
      s!"/MVeFalse {ocmd "/VE [/And 5 0 R [/Not 5 0 R]]"} >> >> >>",
    strm "" content,
    "<< /Type /OCG /Name (on) >>",
    "<< /Type /OCG /Name (off) >>",
    strm "/Type /XObject /Subtype /Form /BBox [0 0 10 10] /OC 6 0 R" "1 0 0 rg 0 0 10 10 re f",
    strm "/Type /XObject /Subtype /Form /BBox [0 0 10 10] /OC 5 0 R" "1 0 0 rg 0 0 10 10 re f",
    strm ("/Type /XObject /Subtype /Image /Width 1 /Height 1 /ColorSpace /DeviceRGB " ++
      "/BitsPerComponent 8 /Filter /ASCIIHexDecode /OC 6 0 R") "ff0000>",
    strm ("/Type /XObject /Subtype /Image /Width 1 /Height 1 /ColorSpace /DeviceRGB " ++
      "/BitsPerComponent 8 /Filter /ASCIIHexDecode /OC 5 0 R") "ff0000>",
    "<< /Type /OCG /Name (unlisted) >>",
    "<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica >>",
    s!"<< /Type /Annot /Subtype /Square /Rect [{ax0} {ay0} {ax0 + 10} {ay0 + 10}] " ++
      "/AP << /N 15 0 R >> /OC 6 0 R >>",
    s!"<< /Type /Annot /Subtype /Square /Rect [{ax1} {ay1} {ax1 + 10} {ay1 + 10}] " ++
      "/AP << /N 15 0 R >> /OC 5 0 R >>",
    strm "/Type /XObject /Subtype /Form /BBox [0 0 10 10]" "1 0 0 rg 0 0 10 10 re f"]

/-- RGB at device pixel `(x, y)`. -/
def pxAt (img : Api.Image) (x y : Nat) : Nat × Nat × Nat :=
  let i := 4 * (y * img.w + x)
  (Raster.Clip.getB img.data i, Raster.Clip.getB img.data (i + 1),
   Raster.Clip.getB img.data (i + 2))

/-- Whether case `i` is painted (red at the centre of its square; zoom 1, y = 200 − page y). -/
def painted (img : Api.Image) (i : Nat) : Bool :=
  let (x, y) := corner i
  pxAt img (x + 5) (200 - (y + 5)) == (255, 0, 0)

/-- Check every case of `pdf` rendered and extracted under `oc` (`none`: the default): the
cases whose index is in `on` are painted, the others not; `hiddenText`: whether HIDDENTEXT is
extracted. -/
def checkAll (label : String) (pdf : ByteArray) (on : Nat → Bool) (hiddenText : Bool)
    (oc : Option State := none) : IO Nat := do
  match Api.openBytes pdf with
  | .error e => check s!"{label}: opens ({e.message})" false
  | .ok d =>
    let mut f := 0
    match Api.renderPage d 0 1 .r0 oc with
    | .error e => f := f + (← check s!"{label}: renders ({e.message})" false)
    | .ok img =>
      for ((name, _, _), i) in cases.zipIdx do
        f := f + (← check s!"{label}: {name} painted = {on i}" (painted img i == on i))
    match Api.pageText d 0 { oc } with
    | .error e => f := f + (← check s!"{label}: text ({e.message})" false)
    | .ok t =>
      f := f + (← check s!"{label}: visible text extracted" ((t.text.splitOn "SHOWNTEXT").length == 2))
      f := f + (← check s!"{label}: hidden text extracted = {hiddenText}"
        (((t.text.splitOn "HIDDENTEXT").length == 2) == hiddenText &&
         ((t.text.splitOn "MORE").length == 2) == hiddenText))
      -- C6 is kept: every extracted glyph is on a glyph run of the (filtered) display list
      f := f + (← check s!"{label}: no hidden glyph run in the display list"
        (hiddenText || t.core.glyphs.length == "SHOWNTEXT".length))
    return f

/-- The `/D` default of each case. -/
def dflt (i : Nat) : Bool := (cases[i]?.map (·.2.2)).getD false

/-- The cases painted when both groups are OFF: AnyOff, AllOff (both forms), /VE [/Not off],
after the hidden sequence, unknown group, missing name, unbalanced `EMC`. -/
def bothOff (i : Nat) : Bool := [4, 5, 6, 7, 12, 13, 14, 19].contains i

/-- Run the checks. -/
def run : IO Nat := do
  let mut f := 0
  -- default configuration: /D /OFF [6]
  let props := "<< /OCGs [5 0 R 6 0 R] /D << /Name (Default) /OFF [6 0 R] " ++
    "/Order [5 0 R [(Sub) 6 0 R]] /RBGroups [[5 0 R 6 0 R]] /Locked [5 0 R] >> >>"
  f := f + (← checkAll "D /OFF" (fixture props) dflt false)
  -- /BaseState /OFF with /ON [5]: the same visibility
  f := f + (← checkAll "BaseState OFF + ON" (fixture
    "<< /OCGs [5 0 R 6 0 R] /D << /BaseState /OFF /ON [5 0 R] >> >>") dflt false)
  -- no /OCProperties: everything painted, every text extracted
  f := f + (← checkAll "no OCProperties" (fixture "") (fun _ => true) true)
  -- the configuration read for the layers panel, and a panel turning group 6 ON
  match Api.openBytes (fixture props) with
  | .error _ => f := f + (← check "opens" false)
  | .ok d =>
    match Api.optionalContent d with
    | none => f := f + (← check "configuration read" false)
    | some c =>
      f := f + (← check "groups, names, /D name"
        (c.groups.map (·.key) == [(5, 0), (6, 0)] && c.groups.map (·.name) == [[111, 110],
          [111, 102, 102]] && c.name == "Default".toUTF8.toList))
      f := f + (← check "order, radio buttons, locked"
        (c.order.length == 2 && c.rbGroups == [[(5, 0), (6, 0)]] && c.locked == [(5, 0)]))
      f := f + (← check "default state" (Api.ocState d == { known := [(5, 0), (6, 0)], off := [(6, 0)] }))
      -- a panel turning group 6 ON (`State.set`; both groups ON): only the cases that need
      -- a group OFF are hidden (AnyOff, AllOff, /VE [/Not off], the contradiction)
      let st := (Api.ocState d).set (6, 0) true
      f := f + (← checkAll "panel: group 6 ON" (fixture props)
        (fun i => ![4, 5, 6, 7, 9].contains i) true (some st))
      -- a panel turning group 5 OFF too (both OFF)
      let st2 := (Api.ocState d).set (5, 0) false
      f := f + (← checkAll "panel: both OFF" (fixture props) bothOff false (some st2))
      -- setGroup honours /Locked and /RBGroups
      let c' : Config := { c with locked := [] }
      f := f + (← check "radio buttons" ((c'.setGroup (Api.ocState d) (6, 0) true).off == [(5, 0)]))
      f := f + (← check "locked group unchanged" ((c.setGroup (Api.ocState d) (5, 0) false).off == [(6, 0)]))
  -- /BaseState /OFF alone: both groups OFF
  f := f + (← checkAll "BaseState OFF" (fixture "<< /OCGs [5 0 R 6 0 R] /D << /BaseState /OFF >> >>")
    bothOff false)
  return f

end SafePdf.Tests.OptionalContent
