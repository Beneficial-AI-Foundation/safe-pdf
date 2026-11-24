import SafePdf.Shell.Worker.Protocol
import SafePdf.Shell.App.Links
import SafePdf.Shell.App.Sidebar
import SafePdf.Shell.App.Attach
import SafePdf.Core.Doc.Attachments

/-!
# Flat tables: Lean values in the layout the C API v2 copies out (task 11.3a1)

Plan.md §6 Phase 11 and `docs/macos-design.md` §3 decision 2 ("structured data crosses as flat
C structs, caller-owned, freed by one `safepdf_free_*` per type"). Unverified shell code, but
pure: every conversion here is a total function from the worker's or the core's values to a
**flat blob** that `macos/safepdf_core.c` turns into the public C structs of
`macos/safepdf_core.h` (glyph cells, links, outline rows, labels, attachments, layer rows,
layers states). The blob is an internal transport between the two halves of the shim, never
part of the public API.

**Layout** (all numbers 64-bit little-endian):

```
ntables
for each table: nrows, ncols, then nrows * ncols cells (row by row)
the string pool (to the end of the blob)
```

A cell is an unsigned number (`Field.u`, saturated at `2^64 - 1`), the IEEE-754 bits of a
double (`Field.f`), or the offset of a string in the pool (`Field.s`). Every string is stored
as its UTF-8 bytes followed by one zero byte; a NUL character inside a string becomes U+FFFD
first (`cText`), so the C side can hand out plain `const char *` pointers into one copy of the
pool. Rows shorter than the table's column count are padded with `u 0`, longer ones cut, so
every table is rectangular by construction (`Table.norm`).

The layers state the C side passes **in** (`safepdf_layers_state`) uses a simpler encoding,
`encodeState`/`decodeState`: the number of known groups, their (object, generation) pairs, the
number of OFF groups, their pairs.
-/

namespace SafePdf.Shell.Ffi.Flat

open SafePdf SafePdf.Core
open SafePdf.Shell.App

/-- One cell of a flat table. -/
inductive Field where
  /-- An unsigned number (saturated at `2^64 - 1`). -/
  | u (n : Nat)
  /-- A double. -/
  | f (x : Float)
  /-- A string (an offset into the pool). -/
  | s (t : String)

/-- A flat table: a column count and its rows. -/
structure Table where
  /-- Number of columns. -/
  cols : Nat
  /-- Rows (normalised to `cols` cells each by `Table.norm`). -/
  rows : Array (Array Field)

/-- A row padded with `u 0` or cut to `n` cells. -/
def padRow (n : Nat) (r : Array Field) : Array Field :=
  if r.size ≥ n then r.extract 0 n else r ++ Array.replicate (n - r.size) (.u 0)

/-- Every row of the table with exactly `cols` cells. -/
def Table.norm (t : Table) : Table := { t with rows := t.rows.map (padRow t.cols) }

/-- A rational as a double (display coordinates only; never fed back into the core). -/
def ratToFloat (q : Rat) : Float := Float.ofInt q.num / Float.ofNat q.den

/-- `n` as eight little-endian bytes appended to `b` (saturated at `2^64 - 1`). -/
def putU64 (b : ByteArray) (n : Nat) : ByteArray := Id.run do
  let v := min n (2 ^ 64 - 1)
  let mut out := b
  for i in [0:8] do
    out := out.push ((v >>> (8 * i)) % 256).toUInt8
  return out

/-- The number stored at byte `p` of `b` (eight little-endian bytes; missing bytes read 0). -/
def getU64 (b : ByteArray) (p : Nat) : Nat := Id.run do
  let mut v := 0
  for i in [0:8] do
    v := v + ((b[p + i]?).getD 0).toNat <<< (8 * i)
  return v

#guard getU64 (putU64 .empty 0x0123456789abcdef) 0 == 0x0123456789abcdef
#guard getU64 (putU64 .empty (2 ^ 70)) 0 == 2 ^ 64 - 1
#guard (putU64 .empty 1).size == 8

/-- A string as the C side receives it: NUL characters replaced by U+FFFD. -/
def cText (s : String) : String := s.map fun c => if c.toNat == 0 then '�' else c

#guard cText "a\x00b" == "a�b"
#guard cText "plain" == "plain"

/-- Appends one cell to `cells`, its string (if any) to `pool`. -/
def putField (acc : ByteArray × ByteArray) : Field → ByteArray × ByteArray
  | .u n => (putU64 acc.1 n, acc.2)
  | .f x => (putU64 acc.1 x.toBits.toNat, acc.2)
  | .s t => (putU64 acc.1 acc.2.size, (acc.2 ++ (cText t).toUTF8).push 0)

/-- **The blob of a list of tables** (layout in the module doc). -/
def encode (ts : List Table) : ByteArray :=
  let (cells, pool) := ts.foldl (fun acc t =>
    let t := t.norm
    let acc := (putU64 (putU64 acc.1 t.rows.size) t.cols, acc.2)
    t.rows.foldl (fun acc r => r.foldl putField acc) acc) (putU64 .empty ts.length, .empty)
  cells ++ pool

-- Number of tables, rows and columns of table 0, the cells, and the pool of a one-table blob.
#guard let b := encode [{ cols := 2, rows := #[#[.u 7, .s "hi"], #[.u 9]] }]
  getU64 b 0 == 1 && getU64 b 8 == 2 && getU64 b 16 == 2 &&
  getU64 b 24 == 7 && getU64 b 32 == 0 && getU64 b 40 == 9 && getU64 b 48 == 0 &&
  b.size == 56 + 3 && b[56]? == some 104 && b[58]? == some 0

-- A second string's offset is after the first one's terminator.
#guard let b := encode [{ cols := 2, rows := #[#[.s "ab", .s "c"]] }]
  getU64 b 24 == 0 && getU64 b 32 == 3

-- A double travels as its bits.
#guard let b := encode [{ cols := 1, rows := #[#[.f 1.5]] }]
  getU64 b 24 == (1.5 : Float).toBits.toNat

/-! ## Boxes and actions -/

/-- A page-space box as four doubles (`llx lly urx ury`). -/
def boxFields (b : Raster.Geom.Box) : Array Field :=
  #[.f (ratToFloat b.llx), .f (ratToFloat b.lly), .f (ratToFloat b.urx), .f (ratToFloat b.ury)]

/-- The C kind number of a link action (`safepdf_action_kind`). -/
def actionKind : Links.Action → Nat
  | .goto _ => 0 | .uri _ => 1 | .badPage => 2 | .unresolved _ => 3 | .other _ => 4 | .none => 5

/-- **An action** as seven cells: kind, page, has-left, left, has-top, top, text (the URI, the
unresolved name or the other action's kind; `""` otherwise). -/
def actionFields : Links.Action → Array Field
  | .goto j => #[.u 0, .u j.page, .u (if j.left.isSome then 1 else 0),
      .f (ratToFloat (j.left.getD 0)), .u (if j.top.isSome then 1 else 0),
      .f (ratToFloat (j.top.getD 0)), .s ""]
  | a@(.uri t) | a@(.unresolved t) | a@(.other t) =>
      #[.u (actionKind a), .u 0, .u 0, .f 0, .u 0, .f 0, .s t]
  | a => #[.u (actionKind a), .u 0, .u 0, .f 0, .u 0, .f 0, .s ""]

#guard (actionFields (.uri "x")).size == 7 && (actionFields (.goto ⟨3, none, some 1⟩)).size == 7
#guard (actionFields .badPage).size == 7

/-- The viewer's action of a worker action (the inverse of `Worker.Serve.action`). -/
def actionOfProto : Worker.Protocol.Action → Links.Action
  | .goto p l t => .goto ⟨p, l, t⟩
  | .uri s => .uri s
  | .badPage => .badPage
  | .unresolved n => .unresolved n
  | .other k => .other k
  | .none => .none

/-! ## The tables of each C struct -/

/-- **A page's selection and search index** (the worker's `pageIndex` answer): table 0 has
one row per cell — text, separator, box (4), line, hidden — and table 1 one row per line,
its direction (quarter turns). A cell without a hidden flag counts as painted. -/
def pageIndex (cells : List Worker.Protocol.Cell) (lineDirs : List Nat) (hidden : List Bool) :
    ByteArray :=
  let hs := hidden.toArray
  let rows := cells.toArray.mapIdx fun i c =>
    #[.s c.text, .s c.sep] ++ boxFields c.box ++ #[.u c.line, .u (if hs[i]?.getD false then 1 else 0)]
  encode [{ cols := 8, rows }, { cols := 1, rows := lineDirs.toArray.map fun d => #[.u d] }]

#guard let b := pageIndex [{ text := "A", sep := "", box := ⟨0, 0, 1, 1⟩, line := 0 }] [0] [true]
  getU64 b 0 == 2 && getU64 b 8 == 1 && getU64 b 16 == 8 &&
  getU64 b (24 + 7 * 8) == 1

/-- **A page's links** (the worker's `viewLinks` answer): box (4), then the action (7). -/
def links (ls : List Worker.Protocol.ViewLink) : ByteArray :=
  encode [{ cols := 11, rows := ls.toArray.map fun l => boxFields l.box ++ actionFields (actionOfProto l.action) }]

/-- Characters dropped from an outline title (as the Tk viewer's `safeText`). -/
def safeText (s : String) : String :=
  String.ofList ((s.toList.take Links.maxTitle).map fun c => if Links.unsafeChar c then ' ' else c)

/-- What activating an outline item of the worker does (as the Tk viewer's `actionOfTarget`). -/
def actionOfTarget : Worker.Protocol.Target → Links.Action
  | .none => .none
  | .page i f => let (l, t) := Links.fitPos f; .goto ⟨i, l, t⟩
  | .danglingDest _ => .badPage
  | .unresolved n => .unresolved (safeText n)
  | .uri u => .uri (Links.uriText u.toUTF8.toList)
  | .action k => if k == "URI" then .other "URI (no address)" else .other (Links.uriText k.toUTF8.toList)

/-- An outline item of the worker as an outline entry (as the Tk viewer's `entryOfItem`). -/
def entryOfItem (it : Worker.Protocol.OutlineItem) : Links.Entry :=
  { title := safeText it.title, depth := it.depth,
    isOpen := match it.count with | some c => decide (0 < c) | none => false,
    action := actionOfTarget it.target }

/-- **The outline** (the worker's `outline` answer, depths clamped as the Tk viewer's):
title, depth, starts open, then the action (7). -/
def outline (items : List Worker.Protocol.OutlineItem) : ByteArray :=
  let es := Links.clampDepths 0 (items.map entryOfItem)
  encode [{ cols := 10, rows := es.toArray.map fun e =>
    #[.s e.title, .u e.depth, .u (if e.isOpen then 1 else 0)] ++ actionFields e.action }]

#guard let b := outline [{ title := "a", depth := 3, target := .none, count := some 2 }]
  getU64 b 8 == 1 && getU64 b 32 == 0 && getU64 b 40 == 1

/-- **Page labels**, one row per page (`""`: the document gives the page no label). -/
def labels (ls : Array String) : ByteArray :=
  encode [{ cols := 1, rows := ls.map fun l => #[.s l] }]

/-- An optional string as two cells: present, value. -/
def optS (o : Option String) : Array Field := #[.u (if o.isSome then 1 else 0), .s (o.getD "")]

/-- An optional number as two cells: present, value. -/
def optU (o : Option Nat) : Array Field := #[.u (if o.isSome then 1 else 0), .u (o.getD 0)]

/-- The C number of an attachment problem (0: none). -/
def problemNum : Option Doc.Attachments.Problem → Nat
  | none => 0 | some .notEmbedded => 1 | some .badEF => 2 | some .notAStream => 3

/-- **The attachments** (`Core.Doc.Attachments.list`): table 0 one row per entry — name, file
name, description (2), size as listed (2, `Attachments.listedSize`), MIME type (2), created
(2), modified (2), page (2), in the name tree, problem, problem text, then (task 11.3d2) the
size column and the tooltip before any decoding (`Attach.sizeColumn`, `Attach.tooltip` without
a probe) and whether it has an embedded stream; table 1 one row per icon — page, rectangle
(4), entry; table 2 one row: truncated, warnings. -/
def attachments (l : Doc.Attachments.Listing) : ByteArray :=
  let ents := l.entries.toArray.map fun a =>
    #[.s a.name, .s a.fileName] ++ optS a.desc ++ optU (Doc.Attachments.listedSize a) ++
      optS a.mime ++ optS a.created ++ optS a.modified ++ optU a.page ++
      #[.u (if a.inTree then 1 else 0), .u (problemNum a.problem),
        .s ((a.problem.map Doc.Attachments.Problem.message).getD ""),
        .s (Attach.sizeColumn a none), .s (Attach.tooltip a none),
        .u (if a.stream.isSome then 1 else 0)]
  let icons := l.icons.toArray.map fun i =>
    #[.u i.page] ++ boxFields (Raster.Geom.Box.ofRect i.rect) ++ #[.u i.entry]
  encode [{ cols := 20, rows := ents }, { cols := 6, rows := icons },
          { cols := 2, rows := #[#[.u (if l.truncated then 1 else 0), .u l.warnings]] }]

/-- The rows of a list of group keys. -/
def keyRows (ks : List Doc.OptionalContent.Key) : Array (Array Field) :=
  ks.toArray.map fun k => #[.u k.1, .u k.2]

/-- **A layers state**: table 0 the known groups, table 1 the OFF groups. -/
def stateTables (st : Doc.OptionalContent.State) : List Table :=
  [{ cols := 2, rows := keyRows st.known }, { cols := 2, rows := keyRows st.off }]

/-- A layers state as a blob (`stateTables`). -/
def state (st : Doc.OptionalContent.State) : ByteArray := encode (stateTables st)

/-- **The layers panel** of configuration `c`: table 0 one row per row of
`Sidebar.layerRows` — depth, label, has a group, object, generation, italic, locked, ON in the
default state; then the default state (`Config.initial`, tables 1 and 2). No optional content:
no rows and an empty state. -/
def layers (c : Option Doc.OptionalContent.Config) : ByteArray :=
  match c with
  | none => encode ({ cols := 8, rows := #[] } :: stateTables {})
  | some c =>
    let st := c.initial
    let rows := (Sidebar.layerRows c).toArray.map fun r =>
      let k := r.group.getD (0, 0)
      #[.u r.depth, .s r.label, .u (if r.group.isSome then 1 else 0), .u k.1, .u k.2,
        .u (if r.italic then 1 else 0), .u (if Sidebar.layerLocked c r then 1 else 0),
        .u (if r.group.any st.isOn then 1 else 0)]
    encode ({ cols := 8, rows } :: stateTables st)

/-! ## The layers state the C side passes in -/

/-- A list of keys: count, then (object, generation) pairs. -/
def putKeys (b : ByteArray) (ks : List Doc.OptionalContent.Key) : ByteArray :=
  ks.foldl (fun b k => putU64 (putU64 b k.1) k.2) (putU64 b ks.length)

/-- **A layers state as the C side encodes it**: the known groups, then the OFF groups. -/
def encodeState (st : Doc.OptionalContent.State) : ByteArray :=
  putKeys (putKeys .empty st.known) st.off

/-- `n` keys read from `b` at `p` (structural in `n`), and the position after them; `none`
when the bytes end first. -/
def getKeys (b : ByteArray) : Nat → Nat → List Doc.OptionalContent.Key →
    Option (List Doc.OptionalContent.Key × Nat)
  | 0, p, acc => some (acc.reverse, p)
  | n + 1, p, acc =>
    if p + 16 ≤ b.size then getKeys b n (p + 16) ((getU64 b p, getU64 b (p + 8)) :: acc)
    else none

/-- **Decodes a layers state** (`encodeState`); `none` for a malformed blob (counts above the
bytes, trailing bytes). -/
def decodeState (b : ByteArray) : Option Doc.OptionalContent.State := do
  if b.size < 8 then none
  let nk := getU64 b 0
  if b.size < 8 + 16 * nk then none
  let (known, p) ← getKeys b nk 8 []
  if b.size < p + 8 then none
  let no := getU64 b p
  if b.size < p + 8 + 16 * no then none
  let (off, q) ← getKeys b no (p + 8) []
  if q == b.size then some { known, off } else none

#guard decodeState (encodeState { known := [(3, 0), (5, 1)], off := [(5, 1)] }) ==
  some { known := [(3, 0), (5, 1)], off := [(5, 1)] }
#guard decodeState (encodeState {}) == some {}
#guard decodeState .empty == none
#guard decodeState (putU64 .empty 1000) == none
#guard decodeState ((encodeState {}).push 0) == none

end SafePdf.Shell.Ffi.Flat
