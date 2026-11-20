import SafePdf.Core.Doc.Nav
import SafePdf.Core.Font.Encoding
import SafePdf.Core.Font.CMap
import SafePdf.Core.Raster.Geom

/-!
# Viewer navigation: outline, links, page labels, history (task 8.2d; Plan.md §6 Phase 8, §10 `SafePdf/Shell/`)

The pure, Tk-free part of the viewer's navigation (unverified shell code, but total and checked
by `#guard`s and two small theorems). Everything comes from the verified navigation layer
`Core.Doc.Nav` (task 4.2): the outline (`Nav.outline`, a flat preorder list with depths and
cycle cuts), link annotations (`Nav.targetOf` on each `/Link`), named destinations (resolved by
`Nav.resolveDest`) and page labels (`Nav.labelTable`).

* **Text strings** (`textString`, §7.9.2.2): UTF-16BE with a `FE FF` mark (`CMap.utf16`), UTF-8
  with an `EF BB BF` mark, else PDFDocEncoding (`Font.pdfDocEncoding` + the Adobe Glyph List);
  control characters (and the bidi overrides U+202A–U+202E, U+2066–U+2069) become spaces, so a
  title cannot reorder or hide the text around it; titles are cut at `maxTitle` characters.
* **Destinations** (`Jump`): a page index plus an optional page-space position (`left`,
  `top`) from the fit spec (`/XYZ left top`, `/FitH top`, `/FitV left`, `/FitR left … top`,
  `/FitBH`, `/FitBV`); the zoom of `/XYZ` and the fit modes are not applied (the viewer keeps
  its zoom).
* **Links** (`Link`, `pageLinks`): the page's `/Annots` walked as `Nav.pageLinks` does (rule
  N7), whose `Nav.Target.uri` carries the `/URI` string of a `/URI` action. `Action`: internal jump, URI, unresolved name, other action
  type (not followed), nothing. `linkAt` is the topmost (last in `/Annots` order) link whose
  rectangle contains a page point.
* **URIs** are shown and copied as `uriText`: printable ASCII as is, every other byte
  (space, controls, non-ASCII) percent-encoded, so the string shown is exactly the address
  (§12.6.4.8: a URI is 7-bit ASCII) and nothing in it can be invisible or reorder the text.
  `uriText_ascii` proves the result is printable ASCII.
* **Page labels**: `pageText label i n` is `page L (i+1/n)`, or `page i+1/n` when the label
  is the plain page number. `gotoPage labels input` (Ctrl+G) accepts an exact label first,
  then a page number `1..n`, then a label ignoring ASCII case.
* **History** (`History`): browser-style back/forward stacks of `Loc` (page and scroll
  fractions), at most `historyCap` entries each; a new jump clears the forward stack.
  `History.back_push` proves that going back after a jump returns to where the jump started.
-/

namespace SafePdf.Shell.App.Links

open SafePdf.Core
open SafePdf.Core.Doc (Doc)
open SafePdf.Core.Raster.Geom (Pt Box decimalToRat)

/-! ## Text strings -/

/-- The longest title shown, in characters. -/
def maxTitle : Nat := 500

/-- Whether a character is shown as a space: C0/C1 controls, DEL and the bidi embedding,
override and isolate controls (they could reorder the surrounding text). -/
def unsafeChar (c : Char) : Bool :=
  c.toNat < 0x20 || (0x7F ≤ c.toNat && c.toNat < 0xA0) ||
  (0x202A ≤ c.toNat && c.toNat ≤ 0x202E) || (0x2066 ≤ c.toNat && c.toNat ≤ 0x2069) ||
  c.toNat == 0x200E || c.toNat == 0x200F

/-- One PDFDocEncoding byte as text (`Font.pdfDocEncoding` and the Adobe Glyph List); an
unassigned byte is U+FFFD. -/
def pdfDocChar (b : UInt8) : List Char :=
  match (Font.pdfDocEncoding.glyph b.toNat).bind Font.glyphToUnicode with
  | some s => s.toList
  | none => if b.toNat < 0x80 then [Char.ofNat b.toNat] else [Font.CMap.replacement]

/-- A PDF text string (§7.9.2.2) as display text: UTF-16BE (`FE FF`), UTF-8 (`EF BB BF`) or
PDFDocEncoding; unsafe characters become spaces; at most `maxTitle` characters. -/
def textString (bs : List UInt8) : String :=
  let cs : List Char := match bs with
    | 0xFE :: 0xFF :: rest => Font.CMap.utf16 rest
    | 0xEF :: 0xBB :: 0xBF :: rest =>
      (String.fromUTF8? (ByteArray.mk rest.toArray)).map (·.toList) |>.getD
        (rest.flatMap pdfDocChar)
    | _ => bs.flatMap pdfDocChar
  String.ofList ((cs.take maxTitle).map fun c => if unsafeChar c then ' ' else c)

/-- Bytes of a string (test helper and labels). -/
def bytes (s : String) : List UInt8 := s.toUTF8.toList

#guard textString (bytes "Chapter 1") == "Chapter 1"
#guard textString [0xFE, 0xFF, 0x00, 0x41, 0x00, 0xE9] == "Aé"
#guard textString [0xEF, 0xBB, 0xBF, 0xC3, 0xA9] == "é"
#guard textString [0x41, 0x0A, 0x42, 0x80] == "A B" ++ "•"  -- 0x80: bullet in PDFDocEncoding
#guard textString [0xFE, 0xFF, 0x20, 0x2E, 0x00, 0x78] == " x"  -- U+202E (RLO) neutralised
#guard (textString (List.replicate 1000 0x41)).length == maxTitle

/-! ## URIs -/

/-- Upper-case hexadecimal digit of `n < 16`. -/
def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (55 + n)

/-- One URI byte as shown: printable ASCII (`!`…`~`) as is, anything else `%XX`. -/
def uriByte (b : UInt8) : List Char :=
  if 0x21 ≤ b.toNat ∧ b.toNat ≤ 0x7E then [Char.ofNat b.toNat]
  else ['%', hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)]

/-- A URI as shown and copied: printable ASCII kept, every other byte percent-encoded. -/
def uriText (bs : List UInt8) : String := String.ofList (bs.flatMap uriByte)

#guard uriText (bytes "https://example.org/a?b=c&d=[e]") == "https://example.org/a?b=c&d=[e]"
#guard uriText (bytes "http://x/a b\n") == "http://x/a%20b%0A"
#guard uriText [0x68, 0xE2, 0x80, 0xAE] == "h%E2%80%AE"

/-- `Char.ofNat` below the surrogates keeps the code point. -/
theorem toNat_ofNat_small (n : Nat) (h : n < 0xD800) : (Char.ofNat n).toNat = n := by
  have hv : n.isValidChar := by unfold Nat.isValidChar; omega
  unfold Char.ofNat
  simp [hv, Char.ofNatAux, Char.toNat]

/-- A hexadecimal digit is printable ASCII. -/
theorem hexDigit_ascii (n : Nat) (h : n < 16) :
    0x21 ≤ (hexDigit n).toNat ∧ (hexDigit n).toNat ≤ 0x7E := by
  unfold hexDigit
  split <;> rw [toNat_ofNat_small _ (by omega)] <;> omega

/-- Every character of a shown URI byte is printable ASCII (no space, control, or non-ASCII
character that could hide or reorder text). -/
theorem uriByte_ascii (b : UInt8) : ∀ c ∈ uriByte b, 0x21 ≤ c.toNat ∧ c.toNat ≤ 0x7E := by
  intro c hc
  have hb := b.toNat_lt
  unfold uriByte at hc
  split at hc
  · simp only [List.mem_singleton] at hc
    subst hc
    rw [toNat_ofNat_small _ (by omega)]
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · decide
    · exact hexDigit_ascii _ (by omega)
    · exact hexDigit_ascii _ (Nat.mod_lt _ (by decide))

/-- **A shown URI is printable ASCII**: every character of `uriText bs` lies in `!`…`~`. -/
theorem uriText_ascii (bs : List UInt8) :
    ∀ c ∈ (uriText bs).toList, 0x21 ≤ c.toNat ∧ c.toNat ≤ 0x7E := by
  intro c hc
  simp only [uriText, String.toList_ofList, List.mem_flatMap] at hc
  obtain ⟨b, _, hb⟩ := hc
  exact uriByte_ascii b c hb

/-! ## Destinations and links -/

/-- Where a jump leads: a page index and an optional page-space position. -/
structure Jump where
  /-- Page index (0-based). -/
  page : Nat
  /-- Page-space x of the left edge to show, if the destination gives one. -/
  left : Option Rat := none
  /-- Page-space y of the top edge to show, if the destination gives one. -/
  top : Option Rat := none
  deriving DecidableEq, Repr

/-- The position `(left, top)` of a fit spec (`none` where it leaves the coordinate alone). -/
def fitPos : Doc.Nav.Fit → Option Rat × Option Rat
  | .xyz l t _ => (l.map decimalToRat, t.map decimalToRat)
  | .fitH t | .fitBH t => (none, t.map decimalToRat)
  | .fitV l | .fitBV l => (l.map decimalToRat, none)
  | .fitR l _ _ t => (l.map decimalToRat, t.map decimalToRat)
  | _ => (none, none)

/-- The jump of an explicit destination whose page is in the document. -/
def jumpOf {n : Nat} (d : Doc.Nav.Dest n) : Option Jump :=
  d.page.map fun p => let (l, t) := fitPos d.fit; ⟨p.val, l, t⟩

/-- What activating a link or outline item does. -/
inductive Action where
  /-- Jump within the document. -/
  | goto (j : Jump)
  /-- A `/URI` action, with its address as shown (`uriText`). -/
  | uri (s : String)
  /-- A destination whose page is not in this document (kept as a description). -/
  | badPage
  /-- A named destination that was not found (name as text). -/
  | unresolved (name : String)
  /-- Another action type (`/Launch`, `/GoToR`, `/JavaScript`, …): never followed. -/
  | other (kind : String)
  /-- No destination or action. -/
  | none
  deriving DecidableEq, Repr

/-- The action of a `Nav` target (a `/URI` action carries its address, shown as `uriText`). -/
def actionOf {n : Nat} (t : Doc.Nav.Target n) : Action :=
  match t with
  | .dest d => match jumpOf d with
    | some j => .goto j
    | Option.none => .badPage
  | .unresolved nm => .unresolved (textString nm)
  | .uri u => .uri (uriText u)
  | .action k =>
    if k == bytes "URI" then .other "URI (no address)" else .other (uriText k)
  | .none => .none

/-- A link of a page: its page-space rectangle and action. -/
structure Link where
  /-- `/Rect`, normalized, over ℚ. -/
  box : Box
  /-- What clicking it does. -/
  action : Action

/-- The link of one `/Annots` element (as `Nav.linkOf`, plus the URI). -/
def linkOf (doc : Doc) (limits : Limits) (a : PdfObject) : Option Link :=
  match Doc.Nav.res doc limits a with
  | .dict ad =>
    if Doc.Nav.isLink doc limits ad then
      (Doc.rectOf (Doc.Nav.getL doc limits ad "Rect")).map fun r =>
        ⟨Box.ofRect r, actionOf (Doc.Nav.targetOf doc limits ad)⟩
    else Option.none
  | _ => Option.none

/-- **The links of page `i`** (rule N7: the page's own `/Annots`, each resolved one level), in
`/Annots` order; empty for an index out of range. -/
def pageLinks (doc : Doc) (limits : Limits) (i : Nat) : Array Link :=
  match doc.pages[i]? with
  | Option.none => #[]
  | some p =>
    match Doc.Nav.fetchDict doc limits p.num p.gen with
    | Option.none => #[]
    | some pd =>
      match Doc.Nav.getL doc limits pd "Annots" with
      | .array xs => (xs.filterMap (linkOf doc limits)).toArray
      | _ => #[]

/-- Whether page point `p` lies in box `b` (edges included). -/
def Box.contains (b : Box) (p : Pt) : Bool :=
  decide (b.llx ≤ p.x ∧ p.x ≤ b.urx ∧ b.lly ≤ p.y ∧ p.y ≤ b.ury)

/-- The topmost link at page point `p` (the last one in `/Annots` order: annotations are
painted in that order), with its index. -/
def linkAt (ls : Array Link) (p : Pt) : Option (Nat × Link) :=
  (List.range ls.size).foldl (fun acc i =>
    match ls[i]? with
    | some l => if Box.contains l.box p then some (i, l) else acc
    | Option.none => acc) Option.none

#guard (linkAt #[⟨⟨0, 0, 10, 10⟩, .none⟩, ⟨⟨5, 5, 20, 20⟩, .uri "u"⟩] ⟨6, 6⟩).map (·.1) == some 1
#guard (linkAt #[⟨⟨0, 0, 10, 10⟩, .none⟩, ⟨⟨5, 5, 20, 20⟩, .uri "u"⟩] ⟨1, 1⟩).map (·.1) == some 0
#guard (linkAt #[⟨⟨0, 0, 10, 10⟩, .none⟩] ⟨11, 1⟩).isNone

/-- The status-line description of an action. -/
def describe (labels : Array String) (n : Nat) : Action → String
  | .goto j =>
    let l := labels.getD j.page (toString (j.page + 1))
    if l == toString (j.page + 1) then s!"go to page {j.page + 1}"
    else s!"go to page {l} ({j.page + 1}/{n})"
  | .uri s => s!"external link (click to copy the address): {s}"
  | .badPage => "link to a page that is not in this document"
  | .unresolved nm => s!"link to an unknown destination \"{nm}\""
  | .other k => s!"link action /{k} (not followed)"
  | .none => "link without a destination"

#guard describe #["i", "ii", "1"] 3 (.goto ⟨2, none, none⟩) == "go to page 1 (3/3)"
#guard describe #["1", "2"] 2 (.goto ⟨1, none, none⟩) == "go to page 2"

/-! ## Outline -/

/-- An outline entry for the side panel. -/
structure Entry where
  /-- Title as display text. -/
  title : String
  /-- Nesting depth, at most one more than the previous entry's (a treeview needs parents). -/
  depth : Nat
  /-- Whether the item starts open (`/Count` > 0). -/
  isOpen : Bool
  /-- What clicking it does. -/
  action : Action

/-- Clamp each depth to one more than the previous entry's (the first entry to 0), so that
every entry of depth `d > 0` has a parent at depth `d - 1` right before it in the tree. -/
def clampDepths : Nat → List Entry → List Entry
  | _, [] => []
  | lim, e :: es =>
    let d := min e.depth lim
    { e with depth := d } :: clampDepths (d + 1) es

/-- **The outline entries** of a document (`Nav.outline`, preorder), with `/URI` addresses of
items whose action is a URI. -/
def outlineEntries (doc : Doc) (limits : Limits) : List Entry :=
  clampDepths 0 <| (Doc.Nav.outline doc limits).items.map fun it =>
    { title := textString it.title, depth := it.depth,
      isOpen := match it.count with | some c => decide (0 < c) | Option.none => false,
      action := actionOf it.target }

/-- Treeview parents: for each entry, the index of its parent (`none`: top level). -/
def parents (es : List Entry) : List (Option Nat) :=
  let step := fun (acc : List (Option Nat) × List Nat × Nat) (e : Entry) =>
    let (out, stack, i) := acc
    -- `stack`: indices of the open ancestors, innermost first (length = current depth + 1).
    let anc := stack.drop (stack.length - e.depth)
    (anc.head? :: out, i :: anc, i + 1)
  (es.foldl step ([], [], 0)).1.reverse

#guard parents ([0, 1, 2, 1, 0, 1].map fun d => ⟨"", d, false, .none⟩) ==
  [none, some 0, some 1, some 0, none, some 4]
#guard (clampDepths 0 ([3, 5, 1].map fun d => ⟨"", d, false, .none⟩)).map (·.depth) == [0, 1, 1]

/-! ## Page labels -/

/-- The labels of all pages as display text (`Nav.labelTable`, one tree walk). -/
def labels (doc : Doc) (limits : Limits) : Array String :=
  let t := Doc.Nav.labelTable doc limits
  (Array.range doc.pages.size).map fun i => textString (t.label i)

/-- The page as shown in the title and status line: `page L (k/n)`, or `page k/n` when the
label is the page number `k`. -/
def pageText (labels : Array String) (i n : Nat) : String :=
  match labels[i]? with
  | some l => if l == toString (i + 1) || l.isEmpty then s!"page {i + 1}/{n}"
    else s!"page {l} ({i + 1}/{n})"
  | none => s!"page {i + 1}/{n}"

#guard pageText #["i", "ii", "iii"] 2 120 == "page iii (3/120)"
#guard pageText #["1", "2"] 1 2 == "page 2/2"

/-- ASCII lower case. -/
def lowerAscii (s : String) : String := s.map Char.toLower

/-- **Go to page** (Ctrl+G): the first page whose label is exactly `input` (trimmed), else the
page number `1..n`, else the first page whose label equals it ignoring ASCII case. -/
def gotoPage (labels : Array String) (input : String) : Option Nat :=
  let q := input.trimAscii.toString
  if q.isEmpty then none else
  match labels.findIdx? (· == q) with
  | some i => some i
  | none =>
    match q.toNat? with
    | some k => if 1 ≤ k ∧ k ≤ labels.size then some (k - 1) else none
    | none => labels.findIdx? (fun l => lowerAscii l == lowerAscii q)

#guard gotoPage #["i", "ii", "1", "2"] "ii" == some 1
#guard gotoPage #["i", "ii", "1", "2"] "1" == some 2
#guard gotoPage #["i", "ii", "1", "2"] " 4 " == some 3
#guard gotoPage #["i", "ii", "1", "2"] "II" == some 1
#guard gotoPage #["i", "ii", "1", "2"] "9" == none
#guard gotoPage #["i", "ii"] "" == none

/-! ## History -/

/-- A position in the document: page and scroll fractions (`xview`/`yview` first values). -/
structure Loc where
  /-- Page index. -/
  page : Nat
  /-- Horizontal scroll fraction. -/
  x : Rat
  /-- Vertical scroll fraction. -/
  y : Rat
  deriving DecidableEq, Repr

/-- The most entries kept on each stack. -/
def historyCap : Nat := 100

/-- Back/forward history: nearest first. -/
structure History where
  /-- Where Back goes, nearest first. -/
  back : List Loc := []
  /-- Where Forward goes, nearest first. -/
  fwd : List Loc := []
  deriving DecidableEq, Repr

/-- Record a jump from `cur`: `cur` goes on the back stack; the forward stack is cleared. -/
def History.push (h : History) (cur : Loc) : History :=
  ⟨(cur :: h.back).take historyCap, []⟩

/-- Go back from `cur`: the location to go to and the new history (`cur` on the forward
stack); `none` when there is nothing to go back to. -/
def History.goBack (h : History) (cur : Loc) : Option (Loc × History) :=
  match h.back with
  | [] => none
  | l :: rest => some (l, ⟨rest, (cur :: h.fwd).take historyCap⟩)

/-- Go forward from `cur` (the mirror of `goBack`). -/
def History.goForward (h : History) (cur : Loc) : Option (Loc × History) :=
  match h.fwd with
  | [] => none
  | l :: rest => some (l, ⟨(cur :: h.back).take historyCap, rest⟩)

/-- **Back after a jump returns** to where the jump started, and Forward then returns to
where Back was pressed. -/
theorem History.back_push (h : History) (cur here : Loc) :
    ((h.push cur).goBack here).map (·.1) = some cur ∧
    (((h.push cur).goBack here).bind fun r => r.2.goForward cur).map (·.1) = some here := by
  simp [History.push, History.goBack, History.goForward, historyCap]

#guard
  let a : Loc := ⟨0, 0, 0⟩
  let b : Loc := ⟨5, 0, 1 / 2⟩
  let c : Loc := ⟨9, 0, 0⟩
  let h := ({} : History).push a |>.push b  -- a → b → c
  match h.goBack c with
  | some (l, h) => l == b && (match h.goBack b with
    | some (l2, h2) => l2 == a && (h2.goBack a).isNone &&
      (match h2.goForward a with | some (l3, _) => l3 == b | none => false)
    | none => false)
  | none => false

end SafePdf.Shell.App.Links
