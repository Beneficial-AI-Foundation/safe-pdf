import SafePdf.Shell.Ffi.V2
import SafePdf.Shell.App.Sidebar
import SafePdf.Shell.App.Attach
import SafePdf.Shell.App.Budget
import SafePdf.Shell.App.View

/-!
# C API v2: the sidebar's rules and the identity line (task 11.3d2)

Plan.md §6 Phase 11 (macOS parity: text and navigation, part 2 — the sidebar and the honest
UI), `docs/macos-design.md` §3 decision 1: whatever has a theorem or a `#guard` in the Tk
viewer crosses the FFI as a pure function and is not re-implemented in Swift. This module
exports the Tk-free sidebar model `App.Sidebar` (which panels a document shows, the panel a
`/PageMode` opens, the toggle's pick, thumbnail sizes, the lazy thumbnail band and eviction, the
outline tree), the attachments panel's save-target rules (`App.Attach.targetProblem`), the
thumbnail of a page of an open document (as the Tk viewer's `pageSizeRot` / `thumbZoom`) and the
12.5 identity line.

`identityLine` follows `Viewer.identityLine` step by step (that module links Tk and cannot be
imported here) and repeats its `#guard`s, as `FfiView.layout` follows `Viewer.computeLayout`.

Unverified shell code. Not the public C API: `macos/safepdf_core.c` wraps these exports
(`macos/safepdf_core.h`, section "sidebar"). Lists cross as `ByteArray`s of 64-bit
little-endian unsigned integers (`Flat.putU64` / `Flat.getU64`); every result is owned by the
caller.
-/

namespace SafePdf.Shell.Ffi.SidebarApi

open SafePdf SafePdf.Core
open SafePdf.Shell.App
open SafePdf.Core.Doc.OpenSettings (PageMode)

/-! ## Panels -/

/-- The content flags of a document (bit 0 outline, bit 1 attachments, bit 2 layers; the C
struct `safepdf_sidebar_content`). -/
def contentOf (bits : UInt32) : Sidebar.Content :=
  { hasOutline := bits &&& 1 != 0, hasAttachments := bits &&& 2 != 0,
    hasLayers := bits &&& 4 != 0 }

/-- The C number of a panel (`safepdf_panel`: the order of `Sidebar.panels`). -/
def panelIdx : Sidebar.Panel → UInt32
  | .thumbnails => 0 | .outline => 1 | .attachments => 2 | .layers => 3

/-- The panel of a C number. -/
def panelOf : UInt32 → Option Sidebar.Panel
  | 0 => some .thumbnails | 1 => some .outline | 2 => some .attachments | 3 => some .layers
  | _ => none

/-- The page mode of its C number (`safepdf_page_mode`, `V2.pageModeIdx`); `none` for UNSET or
anything else. -/
def modeOf (m : UInt32) : Option PageMode :=
  match m.toNat with
  | 0 => some .useNone | 1 => some .useOutlines | 2 => some .useThumbs | 3 => some .fullScreen
  | 4 => some .useOC | 5 => some .useAttachments | _ => none

#guard [PageMode.useNone, .useOutlines, .useThumbs, .fullScreen, .useOC, .useAttachments].all
  fun m => modeOf (V2.pageModeIdx m).toUInt32 == some m

/-- **The panel the sidebar opens with** (`Sidebar.onLoad`) for page mode `mode` (C number,
`0xFFFFFFFF` for none) and content bits `c`; 4 means closed. -/
@[export safepdf_lean_sidebar_on_load]
def onLoad (mode c : UInt32) : UInt32 :=
  match Sidebar.onLoad (modeOf mode) (contentOf c) with
  | some p => panelIdx p
  | none => 4

#guard onLoad 0xFFFFFFFF 1 == 1 && onLoad 0xFFFFFFFF 0 == 4 && onLoad 2 0 == 0 &&
  onLoad 5 1 == 1 && onLoad 5 2 == 2 && onLoad 4 0 == 4 && onLoad 4 4 == 3 && onLoad 3 7 == 4

/-- Whether panel `p`'s switcher button shows for content bits `c` (`Panel.available`, the
filter of `Sidebar.buttons`); 0 for an unknown panel. -/
@[export safepdf_lean_sidebar_available]
def available (p c : UInt32) : UInt8 :=
  match panelOf p with
  | some q => if q.available (contentOf c) then 1 else 0
  | none => 0

#guard (List.range 4).map (fun i => available i.toUInt32 0) == [1, 0, 0, 0] &&
  (List.range 5).map (fun i => available i.toUInt32 7) == [1, 1, 1, 1, 0]

/-- **The panel the sidebar toggle opens** (`Sidebar.pick`): the last one chosen while it is
available, else the outline, else the thumbnails. -/
@[export safepdf_lean_sidebar_pick]
def pick (last c : UInt32) : UInt32 :=
  panelIdx (Sidebar.pick ((panelOf last).getD .thumbnails) (contentOf c))

#guard pick 3 1 == 1 && pick 3 0 == 0 && pick 3 4 == 3 && pick 0 1 == 0

/-! ## Thumbnails -/

/-- The thumbnail scales tried (`Budget.thumbScales`: full, ½, ¼, ⅛ zoom) and the first at which
`Sidebar.thumbBudget` images of `bytes` bytes at full scale (`bytes / 4^k` at scale `k`) fit the
thumbnails' reserve of the photo pool (`Budget.Ceilings.thumbReserve`, 32 MiB) — the Tk
viewer's sizing rule of task 12.3b without its pool bookkeeping: the native shell keeps at
most `thumbBudget` thumbnails and reserves them nothing else. The last scale when none fits. -/
def thumbScaleFor (bytes : Nat) : Nat :=
  let reserve := ({} : Budget.Ceilings).thumbReserve
  (Budget.thumbScales.find? fun k => Sidebar.thumbBudget * (bytes / 4 ^ k) ≤ reserve).getD 3

-- A 98 x 127 thumbnail at 2x (196 x 254 RGBA, about 199 KB) fits at full size; 1 MiB does
-- not (40 MiB > 32 MiB) but fits at half zoom; 64 MiB images only at the last scale.
#guard thumbScaleFor (196 * 254 * 4) == 0 && thumbScaleFor (Budget.mib 1) == 1 &&
  thumbScaleFor (Budget.mib 64) == 3

/-- The sidebar's thumbnail constants: `thumbW`, `thumbTop`, `thumbLabelH`, `thumbGap`,
`thumbMargin`, `thumbBudget` (eight bytes each). -/
@[export safepdf_lean_sidebar_constants]
def constants (_u : Unit) : ByteArray :=
  [Sidebar.thumbW, Sidebar.thumbTop, Sidebar.thumbLabelH, Sidebar.thumbGap, Sidebar.thumbMargin,
    Sidebar.thumbBudget].foldl Flat.putU64 .empty

/-- The scale (`thumbScaleFor`) of a thumbnail image of `w × h` pixels (RGBA). -/
@[export safepdf_lean_sidebar_thumb_scale]
def thumbScale (w h : USize) : UInt32 := (thumbScaleFor (w.toNat * h.toNat * 4)).toUInt32

/-- **The thumbnail of page `i`** of an open document with the user's extra rotation of `q`
quarter turns, as the Tk viewer computes it (`pageSizeRot`, `Sidebar.thumbSize`, `thumbZoom`):
the page's crop box with `/Rotate` plus the user rotation, its size in points, the thumbnail's
size in pixels at 1x and its zoom `thumbW / width` (1 for a degenerate page). Out: width,
height, zoom numerator, zoom denominator (eight bytes each); empty when `i` is out of range or
`q` above 3. -/
@[export safepdf_lean_doc_thumb]
def docThumb (d : V2.Handle) (i : USize) (q : UInt8) : ByteArray :=
  match d.api.page i.toNat, V2.rotOfQuarters q.toNat with
  | .ok p, some r =>
    let (pw, ph) := View.boxSize (Raster.Geom.rotAdd p.rotate r) (Raster.Geom.Box.ofRect p.cropBox)
    let (w, h) := Sidebar.thumbSize pw ph
    let z : Rat := if pw ≤ 0 then 1 else (Sidebar.thumbW : Rat) / pw
    [w, h, z.num.toNat, z.den].foldl Flat.putU64 .empty
  | _, _ => .empty

/-- `n` numbers of `b` from integer `i` on. -/
def nums (b : ByteArray) (i n : Nat) : List Nat :=
  (List.range n).map fun k => Flat.getU64 b (8 * (i + k))

/-- A list as its length and numbers. -/
def listW (xs : List Nat) : ByteArray := xs.foldl Flat.putU64 (Flat.putU64 .empty xs.length)

/-- **The thumbnails laid out** (`Sidebar.thumbLayout`). In: count `n`, then `n` (width, height)
pairs. Out: `listW` of each image's top y, then the total height. -/
@[export safepdf_lean_sidebar_thumb_layout]
def thumbLayoutW (a : ByteArray) : ByteArray :=
  let n := min (Flat.getU64 a 0) (a.size / 16)
  let xs := nums a 1 (2 * n)
  let (ts, h) := Sidebar.thumbLayout ((List.range n).map fun k =>
    (xs.getD (2 * k) 0, xs.getD (2 * k + 1) 0))
  Flat.putU64 (listW (ts.toList.map (·.y))) h

#guard nums (thumbLayoutW ([2, 98, 127, 98, 76].foldl Flat.putU64 .empty)) 0 4 ==
  [2, 12, 12 + 127 + 34, 12 + 127 + 34 + 76 + 34]

/-- **The thumbnails to render** for the visible band `[top, bot)` of the panel
(`Sidebar.thumbsWanted` with `thumbMargin` over `Sidebar.thumbLayout` of the sizes). In: count
`n`, then `n` (width, height) pairs, `top`, `bot`. Out: `listW` of the pages, nearest to the
band's middle first. Counts are capped by the input's size. -/
@[export safepdf_lean_sidebar_thumbs_wanted]
def thumbsWanted (a : ByteArray) : ByteArray :=
  let n := min (Flat.getU64 a 0) (a.size / 16)
  let xs := nums a 1 (2 * n)
  let sizes := (List.range n).map fun k => (xs.getD (2 * k) 0, xs.getD (2 * k + 1) 0)
  let (ts, _) := Sidebar.thumbLayout sizes
  listW (Sidebar.thumbsWanted ts (Flat.getU64 a (8 * (1 + 2 * n)))
    (Flat.getU64 a (8 * (2 + 2 * n))) Sidebar.thumbMargin)

#guard let a := (List.replicate 100 [98, 127]).flatten
  let b := ([100] ++ a ++ [0, 400]).foldl Flat.putU64 .empty
  nums (thumbsWanted b) 0 7 == [6, 1, 0, 2, 3, 4, 5]

/-- **The thumbnails to drop** (`Sidebar.thumbEvict` with `thumbBudget`): in `listW` of the
held pages, `listW` of the wanted pages, then the centre page. Out: `listW` of the pages to
drop, farthest first. -/
@[export safepdf_lean_sidebar_thumb_evict]
def thumbEvict (a : ByteArray) : ByteArray :=
  let nh := min (Flat.getU64 a 0) (a.size / 8)
  let held := nums a 1 nh
  let nw := min (Flat.getU64 a (8 * (1 + nh))) (a.size / 8)
  let wanted := nums a (2 + nh) nw
  listW (Sidebar.thumbEvict held wanted Sidebar.thumbBudget (Flat.getU64 a (8 * (2 + nh + nw))))

#guard let held := List.range 45
  let b := (([45] ++ held ++ [2, 0, 1] ++ [0]).foldl Flat.putU64 .empty)
  nums (thumbEvict b) 0 6 == [5, 44, 43, 42, 41, 40]

/-! ## The outline (and layers) tree -/

/-- **The tree of an outline** (`Sidebar.rows`, `Sidebar.initialOpen`). In: count `n`, then
per entry its depth and whether it starts open (`/Count > 0`; for the layers panel: not the
italic "Additional Layers" heading, `Sidebar.layerEntries`). Out: per row its parent plus one
(0: none), whether it has children, whether it starts open. -/
@[export safepdf_lean_sidebar_tree]
def tree (a : ByteArray) : ByteArray :=
  let n := min (Flat.getU64 a 0) (a.size / 16)
  let xs := nums a 1 (2 * n)
  let es : List Links.Entry := (List.range n).map fun k =>
    ⟨"", xs.getD (2 * k) 0, xs.getD (2 * k + 1) 0 != 0, .none⟩
  let opens := Sidebar.initialOpen es
  ((Sidebar.rows es).zip (List.range n)).foldl (fun b (r, k) =>
    let b := Flat.putU64 b (match r.parent with | some p => p + 1 | none => 0)
    let b := Flat.putU64 b (if r.hasKids then 1 else 0)
    Flat.putU64 b (if opens.getD k false then 1 else 0)) .empty

-- A (open), A.1 (closed), A.1.a, B: parents none, A, A.1, none; A and A.1 have children.
#guard nums (tree ([4, 0, 1, 1, 0, 2, 0, 0, 0].foldl Flat.putU64 .empty)) 0 12 ==
  [0, 1, 1, 1, 1, 0, 2, 0, 0, 0, 0, 0]

/-- **What an outline item does, in words** (`Links.describe`, the status text of an item that
is not followed): `kind` is the C `safepdf_action_kind` (0 go to page `page`, 1 URI `text`,
2 bad page, 3 unresolved name `text`, 4 other action `text`, 5 none). -/
@[export safepdf_lean_action_describe]
def describe (labels : Array String) (n : USize) (kind : UInt8) (page : USize) (text : String) :
    String :=
  let a : Links.Action := match kind.toNat with
    | 0 => .goto { page := page.toNat }
    | 1 => .uri text
    | 2 => .badPage
    | 3 => .unresolved text
    | 4 => .other text
    | _ => .none
  Links.describe labels n.toNat a

#guard describe #[] 3 4 0 "Launch" == "link action /Launch (not followed)" &&
  describe #["i", "ii", "1"] 3 0 2 "" == "go to page 1 (3/3)"

/-! ## Attachments: where an attachment may be saved -/

/-- **Why a chosen file cannot take an attachment** (`Attach.targetProblem`, task 9.r6's rules):
flags bit 0 a folder, bit 1 exists, bit 2 the file is writable, bit 3 its folder is writable,
bit 4 it is the opened document. `""` when it can. -/
@[export safepdf_lean_attachment_target_problem]
def targetProblem (name : String) (flags : UInt32) : String :=
  let f (k : UInt32) : Bool := flags &&& (1 <<< k) != 0
  (Attach.targetProblem name (f 0) (f 1) (f 2) (f 3) (f 4)).getD ""

#guard targetProblem "x" 0b01010 == "x is read-only; choose another name" &&
  targetProblem "x" 0b01110 == "" && targetProblem "x" 0b11110 ==
    "x is the opened document; choose another name"

/-- The size column after decoding an attachment for saving (`Attach.sizeColumn` with the
probe's outcome) — `listed` is the size known without decoding (`has` 0: none), `stream`
whether it has an embedded stream, `ok` whether decoding succeeded and `n` the decoded size. -/
@[export safepdf_lean_attachment_size_after]
def sizeAfter (has : UInt8) (listed : UInt64) (stream ok : UInt8) (n : UInt64) : String :=
  let a : Doc.Attachments.Attachment :=
    { name := "", fileName := "", size := if has != 0 then some listed.toNat else none,
      stream := if stream != 0 then some (0, 0) else none, filtered := true }
  Attach.sizeColumn a (some (if ok != 0 then .decoded n.toNat else .failed ""))

#guard sizeAfter 0 0 1 1 1500 == "1.5 KB" && sizeAfter 0 0 1 0 0 == "error" &&
  sizeAfter 1 26 1 0 0 == "26 B"

/-! ## The trusted identity line (task 12.5) -/

/-- Last path component of a file name (`Viewer.baseName`). -/
def baseName (path : String) : String :=
  (System.FilePath.mk path).fileName.getD path

/-- A file name or path as shown in the identity line (`Viewer.identityClean`): controls and
bidi overrides (`Links.unsafeChar`) become spaces. -/
def identityClean (t : String) : String :=
  t.map fun c => if Links.unsafeChar c then ' ' else c

/-- **The trusted identity line** (`Viewer.identityLine`, task 12.5): which application shows
which file — its name and path, never anything the document says about itself (no `/Title`). -/
def identityLine (path : Option String) (inMemory : Bool) : String :=
  match path with
  | none => s!"{Menu.appName}: no document"
  | some p =>
    let src := if inMemory then "opened from the library, not from a file" else identityClean p
    s!"{Menu.appName} is showing {identityClean (baseName p)} ({src}) - this line is drawn by \
      {Menu.appName}, never by the document"

#guard identityLine none false == "SafePDF: no document"
#guard identityLine (some "/a/b.pdf") false == "SafePDF is showing b.pdf (/a/b.pdf) - this line \
  is drawn by SafePDF, never by the document"
#guard identityLine (some "x‮ftp.pdf") true == "SafePDF is showing x ftp.pdf (opened from the \
  library, not from a file) - this line is drawn by SafePDF, never by the document"

/-- `identityLine` for the C side: `has` 0 means no document. -/
@[export safepdf_lean_identity_line]
def identity (path : String) (has inMemory : UInt8) : String :=
  identityLine (if has != 0 then some path else none) (inMemory != 0)

end SafePdf.Shell.Ffi.SidebarApi
