import SafePdf.Core.Doc.Nav

/-!
# Document open settings (task 9.r8)

Plan.md §6 Phase 9 (the viewer: view modes, outline sidebar, "honour the document's open
settings", ledger Decision 2026-11-23 "The viewer honours every document open setting"), §4 S2
(totality), §5.2 (bounded work). ISO 32000-2 §7.7.2 (catalog: `/PageLayout`, `/PageMode`,
`/OpenAction`, `/ViewerPreferences`), §12.2 (viewer preferences, Table 147), §12.3.2
(destinations), §12.6.4.2 (GoTo actions), §14.3.3 (document information dictionary, `/Title`).

`read doc limits` collects what a viewer applies when it opens the document. It is pure and
total and **never fails the document**: a missing key gives the default, a value of the wrong
type or an unknown name gives the default plus an `Issue` (errors as values, as in `Nav`).

## Rules

* O1. **Lenient resolution** as `Nav` rule N1: every value is resolved one level
  (`Nav.getL`); a failed fetch or a stream counts as `null` (= absent). Reference chains are
  not followed further, so a reference cycle costs one fetch per key.
* O2. **`/PageLayout`** (a name): `SinglePage`, `OneColumn`, `TwoColumnLeft`,
  `TwoColumnRight`, `TwoPageLeft`, `TwoPageRight`; anything else is `badValue`. The viewer
  maps them as PDF.js's `apiPageLayoutToViewerModes`: `continuous` (the column layouts and
  OneColumn) and `spread` (`oddLeft` = PDF.js `SpreadMode.ODD`: pages 1|2, 3|4;
  `oddRight` = `SpreadMode.EVEN`: page 1 alone, then 2|3).
* O3. **`/PageMode`** (a name): `UseNone`, `UseOutlines`, `UseThumbs`, `FullScreen`, `UseOC`,
  `UseAttachments`; else `badValue`. `outlineOpen` is the sidebar rule: no mode → open when
  the file has an outline (the viewer's default); UseNone → closed; UseOutlines → open when
  there is an outline; FullScreen → closed (the `/NonFullScreenPageMode` applies on leaving);
  UseThumbs/UseOC/UseAttachments → the default rule for the outline (UseThumbs and UseOC: their
  panels do not exist yet, `panelMissing` names them for a status note; UseAttachments: the
  viewer opens its attachments panel, task 9.r10, `Attachments`).
* O4. **`/OpenAction`** is honoured **only** as a destination (an explicit array, or a name or
  string naming one through `/Dests` or the `/Names /Dests` tree, `Nav.resolveDest`) or as an
  action dictionary with `/S /GoTo` (its `/D` the same way). Every other action type
  (JavaScript, Launch, URI, GoToR, Named, …) is **never executed**: it is reported as
  `actionIgnored` with its `/S` bytes. `/Next` chains are not followed. A destination whose
  page is not one of the document's pages, or an unresolved name, gives an issue and no
  destination: `dest` always has a page (`read_dest_page`).
* O5. **Zoom of the open destination** (`zoomOf`): `/XYZ` with a zoom `> 0` → `percent`
  (rounded, between 1 and `maxZoomPercent`); `null`/0/negative → `keep`; `/Fit`, `/FitB` →
  `fitPage`; `/FitH`, `/FitBH` → `fitWidth`; `/FitV`, `/FitBV` → `fitHeight`; `/FitR` →
  `fitPage` (best effort: the rectangle lies on the page, so it is visible at Page Fit).
* O6. **`/ViewerPreferences`** (a dictionary): the booleans `HideToolbar`, `HideMenubar`,
  `HideWindowUI`, `FitWindow`, `CenterWindow`, `DisplayDocTitle` (default `false`; a
  non-boolean is `badValue`), `NonFullScreenPageMode` (UseNone, UseOutlines, UseThumbs,
  UseOC; default UseNone) and `Direction` (`L2R`, `R2L`; default L2R). The print keys
  (`ViewArea`, `ViewClip`, `PrintArea`, `PrintClip`, `PrintScaling`, `Duplex`,
  `PickTrayByPDFSize`, `PrintPageRange`, `NumCopies`, `Enforce`) are ignored.
* O7. **Title**: the `/Title` string of the trailer's `/Info` dictionary, as raw bytes (the
  shell decodes the text string). Titles longer than `maxTitleBytes` are dropped with
  `titleTooLong` (never truncated: a cut UTF-16 or UTF-8 sequence would show garbage). The
  XMP metadata's `dc:title` is not read (there is no XMP parser).

## Work bounds

One-level resolutions of a fixed number of keys, plus at most one named-destination lookup
(a `Nav.treeWalk`: at most `objectCount` nodes, `Nav.treeWalk_visited_le`).

## Theorems

* `read_dest_page`: the open destination, when there is one, is on a page of the document.
* `titleOf_le`: the title has at most `maxTitleBytes` bytes.
* `zoomOf_percent_bounds`: a percentage zoom lies in `[1, maxZoomPercent]`.
-/

set_option autoImplicit false

namespace SafePdf.Core.Doc.OpenSettings

open SafePdf
open SafePdf.Core.Doc
open SafePdf.Core.Doc.Nav

/-! ## Values -/

/-- `/PageLayout` (§7.7.2, Table 29). -/
inductive PageLayout where
  /-- One page at a time. -/
  | singlePage
  /-- Pages in one continuous column. -/
  | oneColumn
  /-- Two continuous columns, odd-numbered pages on the left. -/
  | twoColumnLeft
  /-- Two continuous columns, odd-numbered pages on the right. -/
  | twoColumnRight
  /-- Two pages at a time, odd-numbered pages on the left. -/
  | twoPageLeft
  /-- Two pages at a time, odd-numbered pages on the right. -/
  | twoPageRight
  deriving DecidableEq, Repr, Inhabited

/-- How pages are paired for a layout (PDF.js `SpreadMode`). -/
inductive Spread where
  /-- One page per row (PDF.js NONE). -/
  | none
  /-- Pages 1|2, 3|4, …: odd pages on the left (PDF.js ODD). -/
  | oddLeft
  /-- Page 1 alone, then 2|3, …: odd pages on the right (PDF.js EVEN). -/
  | oddRight
  deriving DecidableEq, Repr, Inhabited

/-- `/PageMode` (§7.7.2, Table 29); also the values of `/NonFullScreenPageMode`. -/
inductive PageMode where
  /-- Neither outline nor thumbnails. -/
  | useNone
  /-- Outline visible. -/
  | useOutlines
  /-- Thumbnails visible. -/
  | useThumbs
  /-- Full-screen mode. -/
  | fullScreen
  /-- Optional content group panel visible. -/
  | useOC
  /-- Attachments panel visible. -/
  | useAttachments
  deriving DecidableEq, Repr, Inhabited

/-- `/Direction` (§12.2, Table 147): reading order. -/
inductive Direction where
  /-- Left to right. -/
  | l2r
  /-- Right to left: facing pages put the first page on the right. -/
  | r2l
  deriving DecidableEq, Repr, Inhabited

/-- The zoom an open destination asks for (rule O5). -/
inductive Zoom where
  /-- Keep the viewer's zoom. -/
  | keep
  /-- A fixed scale in percent. -/
  | percent (p : Nat)
  /-- The whole page in the window. -/
  | fitPage
  /-- The page width in the window. -/
  | fitWidth
  /-- The page height in the window. -/
  | fitHeight
  deriving DecidableEq, Repr, Inhabited

/-- What could not be honoured (never an error of the document). -/
inductive Issue where
  /-- The value of `key` has the wrong type or is an unknown name; the default is used. -/
  | badValue (key : String)
  /-- An `/OpenAction` of type `kind` (JavaScript, URI, Launch, …): never executed. -/
  | actionIgnored (kind : List UInt8)
  /-- The open action names a destination that is not found. -/
  | destUnresolved (name : List UInt8)
  /-- The open destination's page is not a page of the document. -/
  | destNotInDocument
  /-- The `/Title` is longer than `maxTitleBytes`. -/
  | titleTooLong
  deriving DecidableEq, Repr

/-- `/ViewerPreferences` (§12.2, rule O6), defaults as in Table 147. -/
structure Prefs where
  /-- `/HideToolbar`. -/
  hideToolbar : Bool := false
  /-- `/HideMenubar`. -/
  hideMenubar : Bool := false
  /-- `/HideWindowUI` (scroll bars and navigation controls). -/
  hideWindowUI : Bool := false
  /-- `/FitWindow`: resize the window to the first page. -/
  fitWindow : Bool := false
  /-- `/CenterWindow`: centre the window on the screen. -/
  centerWindow : Bool := false
  /-- `/DisplayDocTitle`: the window title is the document's `/Title`. -/
  displayDocTitle : Bool := false
  /-- `/NonFullScreenPageMode`: the page mode after leaving full screen. -/
  nonFullScreen : PageMode := .useNone
  /-- `/Direction`. -/
  direction : Direction := .l2r
  deriving DecidableEq, Repr, Inhabited

/-- Everything the viewer applies when it opens a document of `n` pages. -/
structure Settings (n : Nat) where
  /-- `/PageLayout`, if valid. -/
  layout : Option PageLayout := none
  /-- `/PageMode`, if valid. -/
  mode : Option PageMode := none
  /-- The open destination (rule O4), always with a page. -/
  dest : Option (Dest n) := none
  /-- `/ViewerPreferences`. -/
  prefs : Prefs := {}
  /-- `/Title` of the `/Info` dictionary, raw bytes. -/
  title : Option (List UInt8) := none
  /-- What could not be honoured, in key order. -/
  issues : List Issue := []

/-- Longest `/Title` kept (rule O7). -/
def maxTitleBytes : Nat := 4096

/-- Largest percentage an open destination's zoom becomes (rule O5). -/
def maxZoomPercent : Nat := 6400

/-! ## Names -/

/-- The value of a name among `(spelling, value)` pairs. -/
def lookupName {α : Type} (table : List (String × α)) (nm : Name) : Option α :=
  (table.find? fun p => Name.ofString p.1 == nm).map Prod.snd

/-- The `/PageLayout` names. -/
def layoutNames : List (String × PageLayout) :=
  [("SinglePage", .singlePage), ("OneColumn", .oneColumn), ("TwoColumnLeft", .twoColumnLeft),
   ("TwoColumnRight", .twoColumnRight), ("TwoPageLeft", .twoPageLeft),
   ("TwoPageRight", .twoPageRight)]

/-- The `/PageMode` names. -/
def modeNames : List (String × PageMode) :=
  [("UseNone", .useNone), ("UseOutlines", .useOutlines), ("UseThumbs", .useThumbs),
   ("FullScreen", .fullScreen), ("UseOC", .useOC), ("UseAttachments", .useAttachments)]

/-- The `/NonFullScreenPageMode` names (Table 147: no FullScreen, no UseAttachments). -/
def nonFullScreenNames : List (String × PageMode) :=
  [("UseNone", .useNone), ("UseOutlines", .useOutlines), ("UseThumbs", .useThumbs),
   ("UseOC", .useOC)]

/-- The `/Direction` names. -/
def directionNames : List (String × Direction) := [("L2R", .l2r), ("R2L", .r2l)]

/-- Whether a layout scrolls continuously (PDF.js `ScrollMode.VERTICAL`) rather than page by
page (`ScrollMode.PAGE`). -/
def PageLayout.continuous : PageLayout → Bool
  | .singlePage | .twoPageLeft | .twoPageRight => false
  | .oneColumn | .twoColumnLeft | .twoColumnRight => true

/-- How a layout pairs pages (PDF.js `apiPageLayoutToViewerModes`). -/
def PageLayout.spread : PageLayout → Spread
  | .singlePage | .oneColumn => .none
  | .twoColumnLeft | .twoPageLeft => .oddLeft
  | .twoColumnRight | .twoPageRight => .oddRight

/-! ## Reading keys -/

/-- A name-valued key of `d` (rules O2, O3, O6): absent → `none`; a name from `table` → its
value; anything else → `none` and `badValue key`. -/
def nameKey {α : Type} (doc : Doc) (limits : Limits) (d : Dict) (key : String)
    (table : List (String × α)) : Option α × List Issue :=
  match getL doc limits d key with
  | .null => (none, [])
  | .name nm =>
    match lookupName table nm with
    | some v => (some v, [])
    | none => (none, [.badValue key])
  | _ => (none, [.badValue key])

/-- A boolean key of `d` (rule O6): absent → `false`; not a boolean → `false` and
`badValue key`. -/
def boolKey (doc : Doc) (limits : Limits) (d : Dict) (key : String) : Bool × List Issue :=
  match getL doc limits d key with
  | .null => (false, [])
  | .bool b => (b, [])
  | _ => (false, [.badValue key])

/-- `/ViewerPreferences` from its dictionary (rule O6). -/
def prefsOf (doc : Doc) (limits : Limits) (d : Dict) : Prefs × List Issue :=
  let ht := boolKey doc limits d "HideToolbar"
  let hm := boolKey doc limits d "HideMenubar"
  let hw := boolKey doc limits d "HideWindowUI"
  let fw := boolKey doc limits d "FitWindow"
  let cw := boolKey doc limits d "CenterWindow"
  let dt := boolKey doc limits d "DisplayDocTitle"
  let nf := nameKey doc limits d "NonFullScreenPageMode" nonFullScreenNames
  let dr := nameKey doc limits d "Direction" directionNames
  ({ hideToolbar := ht.1, hideMenubar := hm.1, hideWindowUI := hw.1, fitWindow := fw.1,
     centerWindow := cw.1, displayDocTitle := dt.1, nonFullScreen := nf.1.getD .useNone,
     direction := dr.1.getD .l2r },
   ht.2 ++ hm.2 ++ hw.2 ++ fw.2 ++ cw.2 ++ dt.2 ++ nf.2 ++ dr.2)

/-- The catalog's `/ViewerPreferences` (rule O6): defaults when absent or not a dictionary
(then `badValue`). -/
def viewerPrefs (doc : Doc) (limits : Limits) : Prefs × List Issue :=
  match getL doc limits doc.catalog "ViewerPreferences" with
  | .null => ({}, [])
  | .dict d => prefsOf doc limits d
  | _ => ({}, [.badValue "ViewerPreferences"])

/-- What a resolved target gives as an open destination (rule O4): a destination on a page of
the document, else an issue. -/
def ofTarget {n : Nat} : Target n → Option (Dest n) × List Issue
  | .dest d =>
    match d.page with
    | some _ => (some d, [])
    | none => (none, [.destNotInDocument])
  | .unresolved nm => (none, [.destUnresolved nm])
  | .uri _ => (none, [.actionIgnored (Name.ofString "URI").bytes])
  | .action k => (none, [.actionIgnored k])
  | .none => (none, [.badValue "OpenAction"])

/-- The `/OpenAction` (rule O4): a destination or a GoTo action only; any other action is
reported and never executed. -/
def openAction (doc : Doc) (limits : Limits) : Option (Dest doc.pages.size) × List Issue :=
  match raw doc.catalog "OpenAction" with
  | none => (none, [])
  | some o =>
    match res doc limits o with
    | .null => (none, [])
    | .dict ad =>
      match getL doc limits ad "S" with
      | .name s =>
        if s = Name.ofString "GoTo" then
          ofTarget (resolveDest doc limits ((raw ad "D").getD .null))
        else (none, [.actionIgnored s.bytes])
      | _ => (none, [.badValue "OpenAction"])
    | v@(.array _) | v@(.name _) | v@(.string _) => ofTarget (resolveDest doc limits v)
    | _ => (none, [.badValue "OpenAction"])

/-- The `/Title` of the trailer's `/Info` dictionary (rule O7). -/
def titleOf (doc : Doc) (limits : Limits) : Option (List UInt8) × List Issue :=
  match getL doc limits doc.file.trailer.dict "Info" with
  | .null => (none, [])
  | .dict info =>
    match getL doc limits info "Title" with
    | .null => (none, [])
    | .string s => if s.length ≤ maxTitleBytes then (some s, []) else (none, [.titleTooLong])
    | _ => (none, [.badValue "Title"])
  | _ => (none, [.badValue "Info"])

/-- **The open settings of a document** (rules O1–O7). -/
def read (doc : Doc) (limits : Limits) : Settings doc.pages.size :=
  let lay := nameKey doc limits doc.catalog "PageLayout" layoutNames
  let md := nameKey doc limits doc.catalog "PageMode" modeNames
  let oa := openAction doc limits
  let vp := viewerPrefs doc limits
  let tt := titleOf doc limits
  { layout := lay.1, mode := md.1, dest := oa.1, prefs := vp.1, title := tt.1,
    issues := lay.2 ++ md.2 ++ oa.2 ++ vp.2 ++ tt.2 }

/-! ## Applying them (pure parts of the viewer's rules) -/

/-- A positive decimal as a rounded percentage in `[1, maxZoomPercent]`; `none` for zero or a
negative value (rule O5). -/
def percentOf (d : Decimal) : Option Nat :=
  if d.mantissa ≤ 0 then none
  else
    let den : Nat := 10 ^ d.scale
    let p : Nat := (d.mantissa.toNat * 200 + den) / (2 * den)
    some (max 1 (min maxZoomPercent p))

/-- The zoom an open destination's fit asks for (rule O5). -/
def zoomOf : Fit → Zoom
  | .xyz _ _ (some z) =>
    match percentOf z with
    | some p => .percent p
    | none => .keep
  | .xyz _ _ none => .keep
  | .fit | .fitB | .fitR .. => .fitPage
  | .fitH _ | .fitBH _ => .fitWidth
  | .fitV _ | .fitBV _ => .fitHeight
  | .unknown _ => .keep

/-- Whether the outline sidebar opens for page mode `mode` (rule O3; `none`: the document
sets none) in a document with or without an outline. -/
def outlineOpen (mode : Option PageMode) (hasOutline : Bool) : Bool :=
  match mode with
  | none => hasOutline
  | some .useNone => false
  | some .useOutlines => hasOutline
  | some .fullScreen => false
  | some .useThumbs | some .useOC | some .useAttachments => hasOutline

/-- The panel a page mode asks for that the viewer does not have yet (tasks 9.r9, 9.r11; the
attachments panel exists since task 9.r10). -/
def panelMissing : Option PageMode → Option String
  | some .useThumbs => some "thumbnails"
  | some .useOC => some "layers"
  | _ => none

/-- Printable ASCII of at most 64 bytes (other bytes as `?`), for status notes. -/
def shownBytes (bs : List UInt8) : String :=
  String.ofList ((bs.take 64).map fun b =>
    if 32 ≤ b.toNat ∧ b.toNat < 127 then Char.ofNat b.toNat else '?')

/-- A status note for an issue. -/
def Issue.message : Issue → String
  | .badValue k => s!"invalid /{k} ignored"
  | .actionIgnored k => s!"open action /{shownBytes k} ignored (not executed)"
  | .destUnresolved nm => s!"open destination \"{shownBytes nm}\" not found"
  | .destNotInDocument => "open destination is not a page of the document"
  | .titleTooLong => "document title too long, not shown"

/-! ## Theorems -/

/-- `ofTarget` gives only destinations with a page. -/
theorem ofTarget_page {n : Nat} (t : Target n) (d : Dest n) (h : (ofTarget t).1 = some d) :
    d.page.isSome := by
  cases t with
  | dest d' =>
    simp only [ofTarget] at h
    split at h
    · rename_i p hp
      cases h
      simp [hp]
    · cases h
  | _ => simp [ofTarget] at h

/-- The open destination of `openAction` is on a page of the document. -/
theorem openAction_page (doc : Doc) (limits : Limits) (d : Dest doc.pages.size)
    (h : (openAction doc limits).1 = some d) : d.page.isSome := by
  unfold openAction at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · split at h
        · exact ofTarget_page _ _ h
        · cases h
      · cases h
    all_goals first
      | exact ofTarget_page _ _ h
      | cases h

/-- **The open destination of `read`, when there is one, is on a page of the document.** -/
theorem read_dest_page (doc : Doc) (limits : Limits) (d : Dest doc.pages.size)
    (h : (read doc limits).dest = some d) : d.page.isSome :=
  openAction_page doc limits d h

/-- The title has at most `maxTitleBytes` bytes. -/
theorem titleOf_le (doc : Doc) (limits : Limits) (s : List UInt8)
    (h : (titleOf doc limits).1 = some s) : s.length ≤ maxTitleBytes := by
  unfold titleOf at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h; assumption
      · cases h
    · cases h
  · cases h

/-- A percentage zoom lies in `[1, maxZoomPercent]`. -/
theorem zoomOf_percent_bounds (f : Fit) (p : Nat) (h : zoomOf f = .percent p) :
    1 ≤ p ∧ p ≤ maxZoomPercent := by
  unfold zoomOf at h
  split at h
  · split at h
    · rename_i q hq
      cases h
      unfold percentOf at hq
      split at hq
      · cases hq
      · cases hq
        exact ⟨Nat.le_max_left _ _, Nat.max_le.mpr ⟨by decide, Nat.min_le_left _ _⟩⟩
    · cases h
  all_goals cases h

#guard (PageLayout.twoColumnLeft.spread, PageLayout.twoColumnLeft.continuous) == (.oddLeft, true)
#guard (PageLayout.twoPageRight.spread, PageLayout.twoPageRight.continuous) == (.oddRight, false)
#guard PageLayout.singlePage.spread == .none && !PageLayout.singlePage.continuous
#guard PageLayout.oneColumn.continuous && PageLayout.oneColumn.spread == .none
#guard percentOf ⟨15, 1⟩ == some 150 && percentOf ⟨0, 0⟩ == none &&
  percentOf ⟨-2, 0⟩ == none && percentOf ⟨1, 5⟩ == some 1 && percentOf ⟨1000, 0⟩ == some 6400
#guard zoomOf (.xyz none none (some ⟨3, 0⟩)) == .percent 300 &&
  zoomOf (.xyz none none none) == .keep && zoomOf (.xyz none none (some ⟨0, 0⟩)) == .keep &&
  zoomOf .fit == .fitPage && zoomOf .fitB == .fitPage && zoomOf (.fitH none) == .fitWidth &&
  zoomOf (.fitBH none) == .fitWidth && zoomOf (.fitV none) == .fitHeight &&
  zoomOf (.fitR none none none none) == .fitPage && zoomOf (.unknown []) == .keep
#guard outlineOpen none true && !outlineOpen none false && !outlineOpen (some .useNone) true &&
  outlineOpen (some .useOutlines) true && !outlineOpen (some .useOutlines) false &&
  !outlineOpen (some .fullScreen) true && outlineOpen (some .useThumbs) true
#guard panelMissing (some .useOC) == some "layers" && panelMissing (some .useOutlines) == none &&
  panelMissing (some .useAttachments) == none
#guard shownBytes [74, 97, 118, 97, 0] == "Java?"

end SafePdf.Core.Doc.OpenSettings
