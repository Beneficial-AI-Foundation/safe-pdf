import SafePdf
import SafePdf.Core.Doc.OpenSettings

/-!
# Document open settings (task 9.r8)

Plan.md §6 Phase 9 (honour the document's open settings), ISO 32000-2 §7.7.2, §12.2,
§12.3.2, §12.6.4.2. Small three-page PDFs built here (objects 1 catalog, 2 pages, 3–5 the
pages, 6… extra objects; `/Info` in the trailer when given) exercise every rule of
`Core.Doc.OpenSettings`:

* every `/PageLayout` and `/PageMode` value, unknown names and wrong types (`badValue`);
* `/OpenAction` as explicit destinations (`/XYZ` with zoom, `/Fit`, `/FitH`, `/FitV`,
  `/FitR`, `/FitB*`), an integer page, a GoTo action, a named destination through `/Dests`
  (name) and through the `/Names /Dests` tree (string, with `/Limits`), a page outside the
  document, an unknown name;
* JavaScript, URI, Launch and Named open actions: ignored (`actionIgnored`), no destination;
* indirect references for every key, a reference cycle (`6 0 R` ↔ `7 0 R`) and a name-tree
  `/Kids` cycle: bounded, an issue, no destination;
* `/ViewerPreferences`: every boolean, `NonFullScreenPageMode`, `Direction`, print keys
  ignored, wrong types;
* `/Title` from `/Info` (literal and UTF-16), too long, wrong type.
-/

namespace SafePdf.Tests.OpenSettings

open SafePdf.Core.Doc
open SafePdf.Core.Doc.OpenSettings

/-- Reports a failed check; 1 on failure. -/
def check (what : String) (ok : Bool) : IO Nat := do
  if ok then return 0
  IO.println s!"  FAIL open-settings: {what}"
  return 1

/-- A PDF whose objects `1 …` are the given bodies, with a correct xref table and
`trailerExtra` in the trailer. -/
def mkPdf (objs : List String) (trailerExtra : String := "") : ByteArray := Id.run do
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
    s!"trailer\n<< /Size {objs.length + 1} /Root 1 0 R {trailerExtra} >>\nstartxref\n{x}\n%%EOF\n").toUTF8

/-- A three-page document whose catalog has `cat` added; `extra` are objects 6, 7, …. -/
def fixture (cat : String) (extra : List String := []) (trailerExtra : String := "") : ByteArray :=
  mkPdf ([s!"<< /Type /Catalog /Pages 2 0 R {cat} >>",
    "<< /Type /Pages /Kids [3 0 R 4 0 R 5 0 R] /Count 3 /MediaBox [0 0 600 800] >>",
    "<< /Type /Page /Parent 2 0 R >>", "<< /Type /Page /Parent 2 0 R >>",
    "<< /Type /Page /Parent 2 0 R >>"] ++ extra) trailerExtra

/-- What the tests look at: layout, mode, open page, zoom, position, prefs, title, issues. -/
structure Seen where
  layout : Option PageLayout
  mode : Option PageMode
  page : Option Nat
  zoom : Option Zoom
  fit : Option Nav.Fit
  prefs : Prefs
  title : Option (List UInt8)
  issues : List Issue

/-- Opens `pdf` and reads its settings. -/
def seen (pdf : ByteArray) : Option Seen :=
  match SafePdf.Api.openBytes pdf with
  | .error _ => none
  | .ok d =>
    let s := read d.doc {}
    some ⟨s.layout, s.mode, s.dest.bind (·.page.map (·.val)), s.dest.map (zoomOf ·.fit),
      s.dest.map (·.fit), s.prefs, s.title, s.issues⟩

/-- Checks `p` on the settings of `pdf` (fails when it does not open). -/
def expect (what : String) (pdf : ByteArray) (p : Seen → Bool) : IO Nat :=
  check what ((seen pdf).map p |>.getD false)

/-- `str` as bytes. -/
def b (s : String) : List UInt8 := s.toUTF8.toList

/-- Every viewer preference set (and R2L, outline after full screen). -/
def allPrefs : Prefs where
  hideToolbar := true
  hideMenubar := true
  hideWindowUI := true
  fitWindow := true
  centerWindow := true
  displayDocTitle := true
  nonFullScreen := .useOutlines
  direction := .r2l

/-- A title of 5000 bytes (over `maxTitleBytes`). -/
def longTitle : String := String.ofList (List.replicate 5000 'x')

/-- Runs the suite; returns the number of failures. -/
def run : IO Nat := do
  let mut f := 0
  -- Defaults.
  f := f + (← expect "no settings" (fixture "") fun s =>
    s.layout.isNone && s.mode.isNone && s.page.isNone && s.prefs == {} && s.title.isNone &&
    s.issues.isEmpty)
  -- Every /PageLayout.
  for (nm, v) in layoutNames do
    f := f + (← expect s!"layout {nm}" (fixture s!"/PageLayout /{nm}") fun s =>
      s.layout == some v && s.issues.isEmpty)
  f := f + (← expect "layout unknown" (fixture "/PageLayout /Diagonal") fun s =>
    s.layout.isNone && s.issues == [.badValue "PageLayout"])
  f := f + (← expect "layout wrong type" (fixture "/PageLayout (OneColumn)") fun s =>
    s.layout.isNone && s.issues == [.badValue "PageLayout"])
  -- Every /PageMode.
  for (nm, v) in modeNames do
    f := f + (← expect s!"mode {nm}" (fixture s!"/PageMode /{nm}") fun s =>
      s.mode == some v && s.issues.isEmpty)
  f := f + (← expect "mode wrong type" (fixture "/PageMode 3") fun s =>
    s.mode.isNone && s.issues == [.badValue "PageMode"])
  -- Explicit destinations.
  f := f + (← expect "XYZ page 3 at 150 %" (fixture "/OpenAction [5 0 R /XYZ 72 700 1.5]")
    fun s => s.page == some 2 && s.zoom == some (.percent 150) &&
      s.fit == some (.xyz (some ⟨72, 0⟩) (some ⟨700, 0⟩) (some ⟨15, 1⟩)) && s.issues.isEmpty)
  f := f + (← expect "XYZ null zoom keeps" (fixture "/OpenAction [4 0 R /XYZ null null null]")
    fun s => s.page == some 1 && s.zoom == some .keep)
  f := f + (← expect "XYZ zoom 0 keeps" (fixture "/OpenAction [4 0 R /XYZ 0 0 0]")
    fun s => s.page == some 1 && s.zoom == some .keep)
  f := f + (← expect "Fit" (fixture "/OpenAction [3 0 R /Fit]") fun s =>
    s.page == some 0 && s.zoom == some .fitPage)
  f := f + (← expect "FitB" (fixture "/OpenAction [3 0 R /FitB]") fun s =>
    s.zoom == some .fitPage)
  f := f + (← expect "FitH" (fixture "/OpenAction [4 0 R /FitH 500]") fun s =>
    s.page == some 1 && s.zoom == some .fitWidth && s.fit == some (.fitH (some ⟨500, 0⟩)))
  f := f + (← expect "FitBH" (fixture "/OpenAction [4 0 R /FitBH null]") fun s =>
    s.zoom == some .fitWidth)
  f := f + (← expect "FitV" (fixture "/OpenAction [4 0 R /FitV 30]") fun s =>
    s.zoom == some .fitHeight)
  f := f + (← expect "FitBV" (fixture "/OpenAction [4 0 R /FitBV 30]") fun s =>
    s.zoom == some .fitHeight)
  f := f + (← expect "FitR" (fixture "/OpenAction [4 0 R /FitR 10 20 300 400]") fun s =>
    s.zoom == some .fitPage)
  f := f + (← expect "integer page" (fixture "/OpenAction [2 /Fit]") fun s =>
    s.page == some 2)
  f := f + (← expect "page not in document" (fixture "/OpenAction [99 0 R /Fit]") fun s =>
    s.page.isNone && s.issues == [.destNotInDocument])
  f := f + (← expect "empty array" (fixture "/OpenAction []") fun s =>
    s.page.isNone && s.issues == [.badValue "OpenAction"])
  -- GoTo actions and named destinations.
  f := f + (← expect "GoTo action" (fixture "/OpenAction << /S /GoTo /D [4 0 R /Fit] >>")
    fun s => s.page == some 1 && s.issues.isEmpty)
  f := f + (← expect "named via /Dests" (fixture "/OpenAction /Chap /Dests << /Chap [5 0 R /Fit] >>")
    fun s => s.page == some 2 && s.issues.isEmpty)
  f := f + (← expect "named via /Dests, dictionary value"
    (fixture "/OpenAction << /S /GoTo /D /Chap >> /Dests << /Chap << /D [4 0 R /XYZ 0 0 2] >> >>")
    fun s => s.page == some 1 && s.zoom == some (.percent 200))
  f := f + (← expect "named via /Names /Dests tree"
    (fixture "/OpenAction << /S /GoTo /D (sec2) >> /Names << /Dests 6 0 R >>"
      ["<< /Kids [7 0 R] >>", "<< /Limits [(a) (z)] /Names [(sec1) [3 0 R /Fit] (sec2) [5 0 R /Fit]] >>"])
    fun s => s.page == some 2 && s.issues.isEmpty)
  f := f + (← expect "named not found" (fixture "/OpenAction (nowhere)") fun s =>
    s.page.isNone && s.issues == [.destUnresolved (b "nowhere")])
  -- Actions that are never executed.
  f := f + (← expect "JavaScript ignored"
    (fixture "/OpenAction << /S /JavaScript /JS (app.alert\\(1\\)) >>") fun s =>
    s.page.isNone && s.issues == [.actionIgnored (b "JavaScript")])
  f := f + (← expect "URI ignored"
    (fixture "/OpenAction << /S /URI /URI (https://example.org) >>") fun s =>
    s.page.isNone && s.issues == [.actionIgnored (b "URI")])
  f := f + (← expect "Launch ignored"
    (fixture "/OpenAction << /S /Launch /F (calc.exe) >>") fun s =>
    s.page.isNone && s.issues == [.actionIgnored (b "Launch")])
  f := f + (← expect "Named ignored" (fixture "/OpenAction << /S /Named /N /LastPage >>")
    fun s => s.page.isNone && s.issues == [.actionIgnored (b "Named")])
  f := f + (← expect "GoTo with JavaScript /Next: only the GoTo"
    (fixture "/OpenAction << /S /GoTo /D [4 0 R /Fit] /Next << /S /JavaScript /JS (x) >> >>")
    fun s => s.page == some 1 && s.issues.isEmpty)
  f := f + (← expect "action without /S" (fixture "/OpenAction << /D [4 0 R /Fit] >>")
    fun s => s.page.isNone && s.issues == [.badValue "OpenAction"])
  -- Indirect references and cycles.
  f := f + (← expect "indirect values"
    (fixture "/OpenAction 6 0 R /PageLayout 7 0 R /PageMode 8 0 R /ViewerPreferences 9 0 R"
      ["[4 0 R /Fit]", "/TwoPageLeft", "/UseOutlines", "<< /HideToolbar 10 0 R >>", "true"])
    fun s => s.page == some 1 && s.layout == some .twoPageLeft && s.mode == some .useOutlines &&
      s.prefs.hideToolbar && s.issues.isEmpty)
  f := f + (← expect "reference cycle" (fixture "/OpenAction 6 0 R" ["7 0 R", "6 0 R"])
    fun s => s.page.isNone && s.issues == [.badValue "OpenAction"])
  f := f + (← expect "name tree cycle"
    (fixture "/OpenAction (x) /Names << /Dests 6 0 R >>" ["<< /Kids [7 0 R] >>", "<< /Kids [6 0 R] >>"])
    fun s => s.page.isNone && s.issues == [.destUnresolved (b "x")])
  f := f + (← expect "self-referencing action"
    (fixture "/OpenAction 6 0 R" ["<< /S /GoTo /D 6 0 R >>"])
    fun s => s.page.isNone && s.issues.length == 1)
  -- Viewer preferences.
  f := f + (← expect "every viewer preference"
    (fixture ("/ViewerPreferences << /HideToolbar true /HideMenubar true /HideWindowUI true " ++
      "/FitWindow true /CenterWindow true /DisplayDocTitle true " ++
      "/NonFullScreenPageMode /UseOutlines /Direction /R2L /PrintScaling /None /Duplex /Simplex " ++
      "/NumCopies 2 /ViewArea /CropBox /PrintPageRange [0 1] /Enforce [/PrintScaling] >>"))
    fun s => s.prefs == allPrefs && s.issues.isEmpty)
  for (nm, v) in nonFullScreenNames do
    f := f + (← expect s!"NonFullScreenPageMode {nm}"
      (fixture s!"/ViewerPreferences << /NonFullScreenPageMode /{nm} >>") fun s =>
      s.prefs.nonFullScreen == v && s.issues.isEmpty)
  f := f + (← expect "Direction L2R" (fixture "/ViewerPreferences << /Direction /L2R >>")
    fun s => s.prefs.direction == .l2r && s.issues.isEmpty)
  f := f + (← expect "viewer preference types"
    (fixture ("/ViewerPreferences << /HideToolbar 1 /HideMenubar (true) /DisplayDocTitle /true " ++
      "/NonFullScreenPageMode /FullScreen /Direction /Up >>"))
    fun s => s.prefs == {} && s.issues == [.badValue "HideToolbar", .badValue "HideMenubar",
      .badValue "DisplayDocTitle", .badValue "NonFullScreenPageMode", .badValue "Direction"])
  f := f + (← expect "viewer preferences not a dictionary" (fixture "/ViewerPreferences [true]")
    fun s => s.prefs == {} && s.issues == [.badValue "ViewerPreferences"])
  -- Title.
  f := f + (← expect "title" (fixture "" ["<< /Title (A Paper) >>"] "/Info 6 0 R") fun s =>
    s.title == some (b "A Paper") && s.issues.isEmpty)
  f := f + (← expect "title UTF-16" (fixture "" ["<< /Title <FEFF00C40042> >>"] "/Info 6 0 R")
    fun s => s.title.map SafePdf.Api.textString == some "ÄB")
  f := f + (← expect "title too long"
    (fixture "" ["<< /Title (" ++ longTitle ++ ") >>"] "/Info 6 0 R")
    fun s => s.title.isNone && s.issues == [.titleTooLong])
  f := f + (← expect "title wrong type" (fixture "" ["<< /Title 5 >>"] "/Info 6 0 R") fun s =>
    s.title.isNone && s.issues == [.badValue "Title"])
  f := f + (← expect "info wrong type" (fixture "" ["[1 2]"] "/Info 6 0 R") fun s =>
    s.title.isNone && s.issues == [.badValue "Info"])
  -- Several keys together keep the issue order.
  f := f + (← expect "issue order"
    (fixture "/PageLayout 1 /PageMode /X /OpenAction << /S /JavaScript >> /ViewerPreferences 2")
    fun s => s.issues == [.badValue "PageLayout", .badValue "PageMode",
      .actionIgnored (b "JavaScript"), .badValue "ViewerPreferences"])
  -- Messages are printable.
  f := f + (← check "messages"
    ((Issue.actionIgnored (b "JavaScript")).message == "open action /JavaScript ignored (not executed)" &&
     (Issue.destUnresolved [0, 65]).message == "open destination \"?A\" not found"))
  return f

end SafePdf.Tests.OpenSettings
