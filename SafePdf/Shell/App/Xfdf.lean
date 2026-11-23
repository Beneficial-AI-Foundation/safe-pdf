import SafePdf.Shell.App.Marks
import SafePdf.Core.Annot
import SafePdf.Shell.Read

/-!
# XFDF import and export of user marks (tasks 9.5d, 9.11; Plan.md §6 Phase 9 "Persistence — annotations inside the PDF", §10 `SafePdf/Shell/`)

XFDF (ISO 19444-1, the XML form of FDF) is the interchange format Acrobat, Okular, Foxit and
others read and write for annotations. In safe-pdf it is **import/export only**: the store
of the marks is the PDF itself (incremental update, Plan.md S8/C7, task 9.5c). This module
is unverified shell code, pure and Tk-free, total (no `partial`; recursion on fuel or on a
shrinking index), checked by `#guard`s and the suite `Tests/Xfdf.lean`.

**Export** (`toXfdf`): every mark of a `Marks.Store` as

```
<?xml version="1.0" encoding="UTF-8"?>
<xfdf xmlns="http://ns.adobe.com/xfdf/" xml:space="preserve">
<f href="paper.pdf"/>
<annots>
<highlight page="0" rect="100,686,166,708" color="#FFFF98" name="safepdf-mark-1" flags="print"
  date="D:20261120144414Z" opacity="1" coords="100,708,166,708,100,698,166,698"/>
<highlight page="0" rect="100,656,166,668" color="#53FFBC" name="safepdf-mark-3" flags="print"
  date="D:…" opacity="1" coords="100,668,166,668,100,656,166,656"><contents>a comment</contents><popup
  page="0" rect="100,656,166,668" name="safepdf-mark-3-popup-4" open="no"/></highlight>
<text page="0" rect="300,380,320,400" color="#FFFF98" name="safepdf-mark-2" flags="print"
  date="D:…" icon="Comment"><contents>hello</contents></text>
</annots>
</xfdf>
```

* `page` is 0-based, `rect` is `left,bottom,right,top`, `coords` is the `/QuadPoints` of the
  mark (8 numbers per quad, upper-left, upper-right, lower-left, lower-right: the order Acrobat
  and PDF.js use, `Marks.Mark.quadPoints`), `color` is `#RRGGBB` (`Color.hex`), `name` is the
  `/NM` `safepdf-mark-ID` (`Mark.nm`), `date` the PDF date the caller passes
  (`Save.nowDate`). These are the XFDF attribute names of ISO 19444-1 §6.5 (common
  annotation attributes `page`, `rect`, `color`, `name`, `flags`, `date`, `opacity`;
  `highlight` `coords`; `text` `icon`) as written by Adobe's "XML Forms Data Format
  Specification" 3.0 examples.
* A note's `rect` is its icon box inside the page box (`Mark.rect`, as Save writes the
  `/Rect`). A note anchored to a selection keeps its quads in a `coords` attribute on the
  `<text>` element — not part of the `text` element in ISO 19444-1, ignored by other readers,
  read back by us — exactly as 9.5b keeps them in a non-standard `/QuadPoints` on the `/Text`
  annotation.
* **A highlight's comment** (`Marks.Store.commentOf`: the newest note anchored to exactly its
  quads, with a text; task 9.8) is exported in the standard form (task 9.11): `<contents>` of
  the `<highlight>`, followed by a `<popup>` whose `name` is `safepdf-mark-ID-popup-CID` — the
  form Save writes into the PDF since 9.5g (`/Contents` + `/Popup`, rule A11: the popup's
  `/NM` carries the comment note's id), and the form Acrobat, Foxit and Okular write. As in
  the PDF, the comment has no colour of its own: it is the highlight's (`Save.normalize`).
  Every other note (an empty one, an older note on the same quads, a note on a selection
  without highlight) stays a `<text>` element. (9.5d exported the comment as a separate
  `<text>` with `coords`; such files are still imported, below.) Export → import is the
  identity on the marks as Save stores them (`Save.normalize`: a comment in its highlight's
  colour), ids included.
* **Free text and ink** (task 9.9), in the elements ISO 19444-1 defines for them:
  `<freetext page rect name flags date><contents>TEXT</contents><defaultappearance>/Helv 12 Tf
  1 0 0 rg</defaultappearance></freetext>` (`rect` the box, `defaultappearance` the `/DA` the
  PDF gets: font size and text colour; no `color`, as pdf.js writes no `/C` for free text) and
  `<ink page rect color name flags date width opacity><inklist><gesture>x1,y1;x2,y2;…</gesture>
  …</inklist></ink>` (one `<gesture>` per stroke, in order; `width` the thickness, `opacity`
  in `[0, 1]`).
* Escaping (`escape`): `& < > "` as `&amp; &lt; &gt; &quot;`; in attribute values tab, line
  feed and carriage return as character references (so attribute-value normalisation keeps
  them); in content a carriage return as `&#13;` (end-of-line normalisation would turn it
  into a line feed). Characters XML 1.0 forbids even as references (C0 controls other than
  tab/LF/CR, U+FFFE, U+FFFF) become U+FFFD. Everything else, non-BMP characters included, is
  written as UTF-8.
* Numbers (`fmtRat`): exact decimals when the denominator divides 10¹², else rounded to
  10⁻⁶; never an exponent.

**Import** (`readXfdf`): a small XML reader (`parse`; no library) bounded by `Limits` —
input size, element depth, attribute count, name/attribute/text length, node count and the
number of marks — that refuses DTDs (`<!DOCTYPE`, any `<!` declaration: `Error.dtd`) and
every entity except the five predefined ones and numeric character references
(`Error.entity`), so no entity is ever expanded beyond one character and nothing external is
ever fetched (billion laughs, XXE). It checks well-formedness (matching end tags, one root,
unique attributes, legal characters) and never throws: malformed input is an `Error` value
with the character position. Over the tree, `<xfdf>` (any namespace prefix) →
`<annots>` → per annotation:

* `<highlight page coords [color] [name]>` → a highlight over the bounding boxes of each
  group of 8 `coords` numbers (Acrobat and Okular write UL, UR, LL, LR; pdf.js's and Foxit's
  orders give the same boxes); a non-empty `<contents>` / `<contents-richtext>` child → a
  comment note in the highlight's colour anchored to the same quads (that is how Acrobat,
  Okular, Foxit and we since 9.11 store a highlight's comment); its id comes from a `<popup>`
  child named `NAME-popup-CID` (`NAME` the highlight's `name`, ours), else it gets a fresh
  one.
* `<text page rect [color] [name] [coords]>` → a note with the text of `<contents>` (or the
  plain text of `<contents-richtext>`: text nodes, `<p>`/`<div>` ended by a line break,
  `<br/>` a line break), anchored to `coords` when present (ours; 9.5d's form of a
  highlight's comment is such a note on the highlight's quads), else to the upper-left
  corner of `rect`. A `<text inreplyto=…>` is a reply in another tool's comment thread and
  is skipped.
* `color` maps to the nearest PDF.js palette colour (`nearest`; the same squared distance and
  tie-break as `Save.nearestColor`, in bytes instead of units); missing or malformed: yellow.
* `<freetext page rect>` (task 9.9) → free text with the text of `<contents>` (or the plain
  text of `<contents-richtext>`), its box's upper-left corner at `rect`'s, the font size and
  colour of `<defaultappearance>` (`Core.Annot.parseDA`; else size 10 and `color`, else black).
* `<ink page>` with `<inklist>` → ink with one stroke per `<gesture>` (`x,y;x,y;…`), thickness
  `width` (default 1), opacity `opacity` (default 1), colour `color` (default black).
* Everything else is skipped and reported (`Report.skipped`: element and reason, the first
  `maxReport`; `Report.skippedCount`): other annotation types (`underline`, `squiggly`,
  `strikeout`, …), a missing or bad `page`/`coords`/`rect`/`inklist`, a page beyond the
  document.
  Elements outside `<annots>` other than `<f>` and `<ids>` (e.g. `<fields>`) are counted in
  `Report.ignored`.

**Into the store** (`importItems`): a mark equal to one already in the store (page, colour,
kind, text, quads) is not added again (re-importing a file is idempotent); a mark named
`safepdf-mark-ID` keeps its id when `ID` is at least the store's `nextId` before the import
(never used in this store, so the "ids are never reused" rule of `Marks.Store` holds and a
saved id can never be taken over) and no earlier item of the import took it, otherwise it
gets a fresh id. The added marks are appended in id order (so a comment exported
inside its highlight comes back after an older note on the same quads, and `commentOf` finds
the same note again). Imported marks are unsaved: the next Save writes them.
-/

namespace SafePdf.Shell.App.Xfdf

open SafePdf.Core.Raster.Geom (Pt Box)
open SafePdf.Shell.App.Marks (Mark Color Store Kind Anchor)

/-! ## Limits and errors -/

/-- Bounds of the XML reader and the import. -/
structure Limits where
  /-- Largest input in bytes. -/
  maxBytes : Nat := 8 * 1024 * 1024
  /-- Deepest element nesting (the XFDF of highlights and notes needs 4; rich text a few
  more). -/
  maxDepth : Nat := 32
  /-- Most attributes on one element. -/
  maxAttrs : Nat := 32
  /-- Longest attribute value in characters (`coords` of a long selection). -/
  maxAttrLen : Nat := 256 * 1024
  /-- Longest element or attribute name. -/
  maxNameLen : Nat := 128
  /-- Longest text or CDATA run in characters. -/
  maxTextLen : Nat := 1024 * 1024
  /-- Most elements and text nodes in the document. -/
  maxNodes : Nat := 200000
  /-- Most marks one import yields. -/
  maxMarks : Nat := 10000
  deriving Repr, Inhabited

/-- Why an input is refused (character positions count Unicode scalar values after the
UTF-8 decoding and end-of-line normalisation). -/
inductive Error where
  /-- The input has `size` bytes, more than `limit`. -/
  | tooLarge (size limit : Nat)
  /-- The input is not UTF-8. -/
  | notUtf8
  /-- A document type declaration or other markup declaration (`<!DOCTYPE`, `<!ENTITY`, …). -/
  | dtd (pos : Nat)
  /-- A reference to an entity other than the five predefined ones. -/
  | entity (pos : Nat) (name : String)
  /-- A character reference to a character XML does not allow. -/
  | charRef (pos : Nat)
  /-- A character XML does not allow. -/
  | badChar (pos : Nat)
  /-- Elements nested deeper than `limit`. -/
  | tooDeep (pos limit : Nat)
  /-- More than `limit` attributes on one element. -/
  | tooManyAttrs (pos limit : Nat)
  /-- A name, attribute value or text longer than `limit`. -/
  | tooLong (pos : Nat) (what : String) (limit : Nat)
  /-- More than `limit` elements and text nodes. -/
  | tooManyNodes (limit : Nat)
  /-- Not well-formed XML. -/
  | syntax (pos : Nat) (msg : String)
  /-- The root element is `root`, not `xfdf`. -/
  | notXfdf (root : String)
  deriving Repr, BEq, Inhabited

/-- A one-line message for the status bar. -/
def Error.message : Error → String
  | .tooLarge s l => s!"XFDF file too large ({s} bytes, limit {l})"
  | .notUtf8 => "XFDF file is not UTF-8"
  | .dtd p => s!"XFDF: document type declarations are not accepted (at {p})"
  | .entity p n => s!"XFDF: unknown entity &{n}; (at {p})"
  | .charRef p => s!"XFDF: invalid character reference (at {p})"
  | .badChar p => s!"XFDF: invalid character (at {p})"
  | .tooDeep p l => s!"XFDF: elements nested deeper than {l} (at {p})"
  | .tooManyAttrs p l => s!"XFDF: more than {l} attributes (at {p})"
  | .tooLong p w l => s!"XFDF: {w} longer than {l} (at {p})"
  | .tooManyNodes l => s!"XFDF: more than {l} nodes"
  | .syntax p m => s!"XFDF: {m} (at {p})"
  | .notXfdf r => s!"not an XFDF file (root element <{r}>)"

/-! ## XML tree -/

/-- An XML node: text (references resolved) or an element with its attributes in document
order and its children. -/
inductive Node where
  /-- Character data. -/
  | text (s : String)
  /-- An element. -/
  | elem (name : String) (attrs : List (String × String)) (children : List Node)
  deriving Repr, Inhabited

/-- The input as characters. -/
abbrev Src := Array Char

/-- Whether `c` is a character XML 1.0 allows (production `Char`). -/
def isXmlChar (c : Char) : Bool :=
  let n := c.toNat
  n == 9 || n == 10 || n == 13 || (0x20 ≤ n && n ≤ 0xD7FF) || (0xE000 ≤ n && n ≤ 0xFFFD) ||
    0x10000 ≤ n

/-- XML white space. -/
def isWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- Whether `c` may start a name (ASCII letters, `_`, `:`, any non-ASCII character). -/
def isNameStart (c : Char) : Bool := c.isAlpha || c == '_' || c == ':' || 0x80 ≤ c.toNat

/-- Whether `c` may continue a name. -/
def isNameChar (c : Char) : Bool := isNameStart c || c.isDigit || c == '-' || c == '.'

/-- The first index at or after `i` that is not white space. -/
def skipWs (a : Src) (i : Nat) : Nat :=
  if h : i < a.size then
    if isWs a[i] then skipWs a (i + 1) else i
  else i
termination_by a.size - i

/-- The first index at or after `i` that is not a name character. -/
def scanName (a : Src) (i : Nat) : Nat :=
  if h : i < a.size then
    if isNameChar a[i] then scanName a (i + 1) else i
  else i
termination_by a.size - i

/-- Whether `pat` occurs in `a` at `i`. -/
def matchAt (a : Src) (i : Nat) : List Char → Bool
  | [] => true
  | c :: cs => a[i]? == some c && matchAt a (i + 1) cs

/-- The first index at or after `i` where `pat` occurs. -/
def findSeq (a : Src) (i : Nat) (pat : List Char) : Option Nat :=
  if h : i < a.size then
    if matchAt a i pat then some i else findSeq a (i + 1) pat
  else none
termination_by a.size - i

/-- The first index in `[i, stop)` holding `c` (`stop` defaults to the end), so that a
length limit stops the search early. -/
def findChar (a : Src) (i : Nat) (c : Char) (stop : Nat := a.size) : Option Nat :=
  if h : i < a.size ∧ i < stop then
    if a[i] == c then some i else findChar a (i + 1) c stop
  else none
termination_by a.size - i

/-- The characters `[i, j)` of `a`. -/
def slice (a : Src) (i j : Nat) : String := String.ofList (a.extract i j).toList

/-- The value of a hexadecimal digit. -/
def hexVal (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- The number of digits `ds` in base `b` (`none` for an empty list or a non-digit). -/
def digitsIn (b : Nat) (ds : List Char) : Option Nat :=
  if ds.isEmpty then none
  else ds.foldl (fun acc c => acc.bind fun n => (hexVal c).bind fun d =>
    if d < b then some (n * b + d) else none) (some 0)

/-- The character of a reference body `name` (between `&` and `;`) at `pos`. -/
def resolveRef (pos : Nat) (name : String) : Except Error Char :=
  match name with
  | "amp" => .ok '&'
  | "lt" => .ok '<'
  | "gt" => .ok '>'
  | "quot" => .ok '"'
  | "apos" => .ok '\''
  | _ =>
    let num := match name.toList with
      | '#' :: 'x' :: hs => if hs.length ≤ 6 then digitsIn 16 hs else none
      | '#' :: ds => if ds.length ≤ 7 then digitsIn 10 ds else none
      | _ => none
    if name.startsWith "#" then
      match num with
      | some n =>
        let c := Char.ofNat n
        if c.toNat == n && isXmlChar c then .ok c else .error (.charRef pos)
      | none => .error (.charRef pos)
    else .error (.entity pos name)

/-- Decodes the characters `[i, j)`: references resolved, illegal characters refused, and
in an attribute value (`attr`) white space other than spaces normalised to spaces and `<`
refused. `fuel` bounds the steps (`j - i + 1` suffices: each step consumes a character). -/
def decodeRange (a : Src) (j : Nat) (attr : Bool) : Nat → Nat → String → Except Error String
  | 0, _, acc => .ok acc
  | fuel + 1, k, acc =>
    if k ≥ j then .ok acc
    else match a[k]? with
      | none => .ok acc
      | some '&' =>
        match findChar a (k + 1) ';' (k + 13) with
        | some e =>
          if e < j && e ≤ k + 12 then
            match resolveRef k (slice a (k + 1) e) with
            | .ok c => decodeRange a j attr fuel (e + 1) (acc.push c)
            | .error err => .error err
          else .error (.syntax k "unterminated reference")
        | none => .error (.syntax k "unterminated reference")
      | some c =>
        if attr && c == '<' then .error (.syntax k "'<' in an attribute value")
        else if !isXmlChar c then .error (.badChar k)
        else if attr && isWs c then decodeRange a j attr fuel (k + 1) (acc.push ' ')
        else decodeRange a j attr fuel (k + 1) (acc.push c)

/-- Parses the attributes of a start tag from `i` (after the element name) up to and
including `>` or `/>`: the attributes in order, whether the tag closes itself, and the index
after it. `fuel` bounds the number of attributes. -/
def parseAttrs (lim : Limits) (a : Src) :
    Nat → Nat → List (String × String) → Except Error (List (String × String) × Bool × Nat)
  | 0, i, _ => .error (.tooManyAttrs i lim.maxAttrs)
  | fuel + 1, i, acc =>
    let j := skipWs a i
    match a[j]? with
    | none => .error (.syntax j "unterminated tag")
    | some '>' => .ok (acc.reverse, false, j + 1)
    | some '/' =>
      if a[j + 1]? == some '>' then .ok (acc.reverse, true, j + 2)
      else .error (.syntax j "'/' not followed by '>'")
    | some c =>
      if !isNameStart c then .error (.syntax j "bad attribute name")
      else if !acc.isEmpty && j == i then .error (.syntax j "no space between attributes")
      else if acc.length ≥ lim.maxAttrs then .error (.tooManyAttrs j lim.maxAttrs)
      else
        let e := scanName a j
        if e - j > lim.maxNameLen then .error (.tooLong j "attribute name" lim.maxNameLen)
        else
          let name := slice a j e
          let k := skipWs a e
          if a[k]? != some '=' then .error (.syntax k "attribute without '='")
          else
            let q := skipWs a (k + 1)
            match a[q]? with
            | some qc =>
              if qc != '"' && qc != '\'' then .error (.syntax q "attribute value not quoted")
              else match findChar a (q + 1) qc (q + 2 + lim.maxAttrLen) with
                | none =>
                  if a.size > q + 1 + lim.maxAttrLen then
                    .error (.tooLong q "attribute value" lim.maxAttrLen)
                  else .error (.syntax q "unterminated attribute value")
                | some close =>
                  if acc.any (·.1 == name) then .error (.syntax j s!"duplicate attribute {name}")
                  else match decodeRange a close true (close - q) (q + 1) "" with
                    | .ok v => parseAttrs lim a fuel (close + 1) ((name, v) :: acc)
                    | .error err => .error err
            | none => .error (.syntax q "unterminated tag")

/-- A lexical token of the reader. -/
inductive Tok where
  /-- A start tag (self-closing when `selfClose`). -/
  | start (name : String) (attrs : List (String × String)) (selfClose : Bool)
  /-- An end tag. -/
  | close (name : String)
  /-- Character data (text or CDATA). -/
  | text (s : String)
  /-- A comment or processing instruction (the XML declaration among them). -/
  | skip

/-- The text token of `[i, e)` (`e > i` when called from `next`). -/
def textAt (lim : Limits) (a : Src) (i e : Nat) : Except Error (Tok × Nat) :=
  if e - i > lim.maxTextLen then .error (.tooLong i "text" lim.maxTextLen)
  else match decodeRange a e false (e - i + 1) i "" with
    | .ok s => .ok (.text s, e)
    | .error err => .error err

/-- The token at `i` and the index after it (always `> i`). -/
def next (lim : Limits) (a : Src) (i : Nat) : Except Error (Tok × Nat) :=
  match a[i]? with
  | none => .ok (.skip, i + 1)
  | some '<' =>
    if matchAt a (i + 1) ['?'] then
      match findSeq a (i + 2) ['?', '>'] with
      | some e => .ok (.skip, e + 2)
      | none => .error (.syntax i "unterminated processing instruction")
    else if matchAt a (i + 1) "!--".toList then
      match findSeq a (i + 4) "-->".toList with
      | some e => .ok (.skip, e + 3)
      | none => .error (.syntax i "unterminated comment")
    else if matchAt a (i + 1) "![CDATA[".toList then
      match findSeq a (i + 9) "]]>".toList with
      | some e =>
        if e - (i + 9) > lim.maxTextLen then .error (.tooLong i "CDATA section" lim.maxTextLen)
        else
          let cs := (a.extract (i + 9) e).toList
          if cs.all isXmlChar then .ok (.text (String.ofList cs), e + 3)
          else .error (.badChar i)
      | none => .error (.syntax i "unterminated CDATA section")
    else if matchAt a (i + 1) ['!'] then .error (.dtd i)
    else if matchAt a (i + 1) ['/'] then
      let e := scanName a (i + 2)
      if e == i + 2 then .error (.syntax i "bad end tag")
      else if e - (i + 2) > lim.maxNameLen then .error (.tooLong i "element name" lim.maxNameLen)
      else
        let k := skipWs a e
        if a[k]? == some '>' then .ok (.close (slice a (i + 2) e), k + 1)
        else .error (.syntax k "bad end tag")
    else
      match a[i + 1]? with
      | some c =>
        if !isNameStart c then .error (.syntax i "bad start tag")
        else
          let e := scanName a (i + 1)
          if e - (i + 1) > lim.maxNameLen then .error (.tooLong i "element name" lim.maxNameLen)
          else match parseAttrs lim a (lim.maxAttrs + 1) e [] with
            | .ok (as, sc, j) => .ok (.start (slice a (i + 1) e) as sc, j)
            | .error err => .error err
      | none => .error (.syntax i "unterminated tag")
  | some _ =>
    match findChar a i '<' (i + lim.maxTextLen + 1) with
    | none =>
      if a.size > i + lim.maxTextLen then .error (.tooLong i "text" lim.maxTextLen)
      else textAt lim a i a.size
    | some e => textAt lim a i e

/-- An open element while the tree is built: name, attributes, children so far (newest
first). -/
structure Frame where
  /-- Element name. -/
  name : String
  /-- Attributes. -/
  attrs : List (String × String)
  /-- Children, newest first. -/
  kids : List Node

/-- Hands a finished node to the innermost open element, or makes it the root. -/
def attach (n : Node) : List Frame → List Frame × Option Node
  | [] => ([], some n)
  | f :: fs => ({ f with kids := n :: f.kids } :: fs, none)

/-- Builds the tree from the tokens starting at `i`: `stack` holds the open elements
(innermost first, `depth` of them), `root` the finished root, `count` the nodes so far.
`fuel` bounds the steps (`a.size + 1` suffices: each token consumes a character). -/
def build (lim : Limits) (a : Src) :
    Nat → Nat → List Frame → Nat → Option Node → Nat → Except Error Node
  | 0, i, _, _, _, _ => .error (.syntax i "internal: out of fuel")
  | fuel + 1, i, stack, depth, root, count =>
    if i ≥ a.size then
      match stack, root with
      | f :: _, _ => .error (.syntax i s!"unclosed element <{f.name}>")
      | [], none => .error (.syntax i "no root element")
      | [], some r => .ok r
    else match next lim a i with
      | .error e => .error e
      | .ok (tok, j) =>
        if j ≤ i then .error (.syntax i "internal: no progress") else
        match tok with
        | .skip => build lim a fuel j stack depth root count
        | .text s =>
          match stack with
          | [] =>
            if s.all isWs then build lim a fuel j stack depth root count
            else .error (.syntax i "text outside the root element")
          | f :: fs =>
            if count + 1 > lim.maxNodes then .error (.tooManyNodes lim.maxNodes)
            else build lim a fuel j ({ f with kids := .text s :: f.kids } :: fs) depth root
              (count + 1)
        | .start n as sc =>
          if count + 1 > lim.maxNodes then .error (.tooManyNodes lim.maxNodes)
          else if stack.isEmpty && root.isSome then .error (.syntax i "a second root element")
          else if depth ≥ lim.maxDepth then .error (.tooDeep i lim.maxDepth)
          else if sc then
            let (st, r) := attach (.elem n as []) stack
            build lim a fuel j st depth (r <|> root) (count + 1)
          else build lim a fuel j (⟨n, as, []⟩ :: stack) (depth + 1) root (count + 1)
        | .close n =>
          match stack with
          | [] => .error (.syntax i s!"unexpected </{n}>")
          | f :: fs =>
            if f.name != n then .error (.syntax i s!"</{n}> closes <{f.name}>")
            else
              let (st, r) := attach (.elem f.name f.attrs f.kids.reverse) fs
              build lim a fuel j st (depth - 1) (r <|> root) count

/-- End-of-line normalisation (XML 1.0 §2.11): CR LF and lone CR become LF; the characters
of `s` as an array. -/
def normEol (s : String) : Array Char :=
  (s.foldl (fun (acc, cr) c =>
    if c == '\r' then (acc.push '\n', true)
    else if c == '\n' && cr then (acc, false)
    else (acc.push c, false)) (Array.emptyWithCapacity s.utf8ByteSize, false)).1

/-- **The XML reader**: the root element of `bytes` (UTF-8, an optional byte-order mark), or
why it is refused. -/
def parse (lim : Limits) (bytes : ByteArray) : Except Error Node :=
  if bytes.size > lim.maxBytes then .error (.tooLarge bytes.size lim.maxBytes)
  else
    let body := if (bytes.extract 0 3).toList == [0xEF, 0xBB, 0xBF] then bytes.extract 3 bytes.size
      else bytes
    match String.fromUTF8? body with
    | none => .error .notUtf8
    | some s =>
      let a := normEol s
      build lim a (a.size + 1) 0 [] 0 none 0

/-! ## Node helpers -/

/-- The name without a namespace prefix. -/
def localName (n : String) : String :=
  String.ofList ((n.toList.reverse.takeWhile (· != ':')).reverse)

/-- The value of attribute `k`. -/
def attr (as : List (String × String)) (k : String) : Option String :=
  (as.find? (·.1 == k)).map (·.2)

/-- The plain text of a node: text nodes in order, `<p>`/`<div>` ended by a line break,
`<br>` a line break; white-space-only text containing a line break (indentation between
paragraphs) dropped. `fuel` is the depth left (the reader bounds the depth). -/
def plain : Nat → Node → String
  | _, .text s => if s.all isWs && s.contains '\n' then "" else s
  | 0, .elem .. => ""
  | fuel + 1, .elem n _ cs =>
    let ln := localName n
    if ln == "br" then "\n"
    else
      let inner := cs.foldl (fun acc c => acc ++ plain fuel c) ""
      if ln == "p" || ln == "div" then inner ++ "\n" else inner

/-- Drops trailing line breaks. -/
def dropTrailingNl (s : String) : String :=
  String.ofList ((s.toList.reverse.dropWhile (· == '\n')).reverse)

/-- The comment of an annotation element's children: the text of `<contents>`, else the
plain text of `<contents-richtext>`. -/
def contentsOf (lim : Limits) (cs : List Node) : Option String :=
  let child (k : String) : Option (List Node) := cs.findSome? fun
    | .elem n _ kids => if localName n == k then some kids else none
    | .text _ => none
  match child "contents" with
  | some kids => some (kids.foldl (fun acc c => match c with
      | .text s => acc ++ s
      | .elem .. => acc) "")
  | none => (child "contents-richtext").map fun kids =>
      dropTrailingNl (kids.foldl (fun acc c => acc ++ plain (lim.maxDepth + 1) c) "")

/-! ## Numbers and colours -/

/-- Splits on commas and white space, dropping empty parts. -/
def splitNums (s : String) : List String :=
  let (parts, cur) := s.toList.foldl (fun (parts, cur) c =>
    if c == ',' || isWs c then
      (if cur.isEmpty then parts else String.ofList cur.reverse :: parts, [])
    else (parts, c :: cur)) (([] : List String), ([] : List Char))
  (if cur.isEmpty then parts else String.ofList cur.reverse :: parts).reverse

/-- A decimal number: optional sign, digits with an optional fraction, optional exponent of
at most two digits; at most 64 characters. -/
def parseNum (s : String) : Option Rat :=
  let cs := s.toList
  if cs.length > 64 then none else
  let (neg, cs) := match cs with
    | '-' :: r => (true, r)
    | '+' :: r => (false, r)
    | r => (false, r)
  let (ip, cs) := cs.span Char.isDigit
  let (fp, cs) := match cs with
    | '.' :: r => r.span Char.isDigit
    | r => ([], r)
  if ip.isEmpty && fp.isEmpty then none else
  let ex : Option Int := match cs with
    | [] => some 0
    | c :: r =>
      if c == 'e' || c == 'E' then
        let (eneg, r) := match r with
          | '-' :: r => (true, r)
          | '+' :: r => (false, r)
          | r => (false, r)
        if r.length > 2 then none
        else (digitsIn 10 r).map fun n => if eneg then -(n : Int) else n
      else none
  match ex, digitsIn 10 (ip ++ fp) with
  | some e, some m =>
    let ex := e - fp.length
    let q : Rat := if ex ≥ 0 then ((m * 10 ^ ex.toNat : Nat) : Rat)
      else (m : Rat) / ((10 ^ (-ex).toNat : Nat) : Rat)
    some (if neg then -q else q)
  | _, _ => none

/-- The numbers of an attribute value (`none` when a part is not a number). -/
def nums (s : String) : Option (List Rat) :=
  ((splitNums s).foldl (fun acc p => acc.bind fun xs => (parseNum p).map (· :: xs))
    (some [])).map List.reverse

/-- The page-space boxes of `coords` (8 numbers per quad; the bounding box of each quad's
four points, as `Save.boxesOf`). -/
def boxesOf (xs : List Rat) : List Box :=
  let rec go : List Rat → List Box → List Box
    | x1 :: y1 :: x2 :: y2 :: x3 :: y3 :: x4 :: y4 :: rest, acc =>
      go rest (⟨min (min x1 x2) (min x3 x4), min (min y1 y2) (min y3 y4),
        max (max x1 x2) (max x3 x4), max (max y1 y2) (max y3 y4)⟩ :: acc)
    | _, acc => acc.reverse
  go xs []

/-- `#RRGGBB` (either case) as bytes. -/
def parseColor (s : String) : Option (Nat × Nat × Nat) :=
  match (s.toList.dropWhile isWs).reverse.dropWhile isWs |>.reverse with
  | ['#', r1, r2, g1, g2, b1, b2] => do
    let r ← digitsIn 16 [r1, r2]
    let g ← digitsIn 16 [g1, g2]
    let b ← digitsIn 16 [b1, b2]
    pure (r, g, b)
  | _ => none

/-- The palette colour nearest to the bytes `(r, g, b)` (squared distance, ties to the earlier
palette colour; `Save.nearestColor` scaled by 255²). -/
def nearest (rgb : Nat × Nat × Nat) : Color :=
  let (r, g, b) := rgb
  let dist (c : Color) : Int :=
    let (r', g', b') := c.rgb
    let d (x y : Nat) : Int := ((x : Int) - y) * ((x : Int) - y)
    d r r' + d g g' + d b b'
  Color.all.foldl (fun best c => if dist c < dist best then c else best) .yellow

/-- A number as a decimal: exact when the denominator divides 10¹², else rounded to 10⁻⁶. -/
def fmtRat (q : Rat) : String :=
  let neg := q < 0
  let q := if neg then -q else q
  let (n, k) := match (List.range 13).find? (fun k => 10 ^ k % q.den == 0) with
    | some k => (q.num.toNat * (10 ^ k / q.den), k)
    | none => ((q * ((10 ^ 6 : Nat) : Rat) + 1 / 2).floor.toNat, 6)
  let ip := n / 10 ^ k
  let fd := toString (n % 10 ^ k)
  let fd := String.ofList (List.replicate (k - fd.length) '0') ++ fd
  let fd := String.ofList ((fd.toList.reverse.dropWhile (· == '0')).reverse)
  (if neg && n != 0 then "-" else "") ++ toString ip ++ (if fd.isEmpty then "" else "." ++ fd)

#guard fmtRat 100 == "100" && fmtRat (-3) == "-3" && fmtRat (1 / 4) == "0.25" &&
  fmtRat (-1 / 8) == "-0.125" && fmtRat 0 == "0" && fmtRat (1 / 3) == "0.333333" &&
  fmtRat (2 / 3) == "0.666667" && fmtRat (-1 / 3000000) == "0" &&
  fmtRat (-1 / 10000000) == "-0.0000001"
#guard [100, -3, 1 / 4, -1 / 8, 0, 1234567 / 1000, 1 / 1024].all fun q => parseNum (fmtRat q) == some q
#guard parseNum "1e2" == some 100 && parseNum "-.5" == some (-1 / 2) && parseNum "+7." == some 7 &&
  parseNum "2.5E-1" == some (1 / 4)
#guard parseNum "" == none && parseNum "." == none && parseNum "1e" == none &&
  parseNum "1e999" == none && parseNum "0x10" == none && parseNum "1,2" == none &&
  parseNum "nan" == none
#guard nums "1, 2,3\n 4.5 " == some [1, 2, 3, 9 / 2] && nums "1,x" == none && nums "" == some []
#guard boxesOf [100, 708, 166, 708, 100, 698, 166, 698, 1, 2] == [⟨100, 698, 166, 708⟩]
-- pdf.js / Foxit order (LL, LR, UL, UR, i.e. counter-clockwise) gives the same box.
#guard boxesOf [100, 698, 166, 698, 100, 708, 166, 708] == [⟨100, 698, 166, 708⟩]
#guard parseColor "#ffff00" == some (255, 255, 0) && parseColor " #53FFBC " == some (0x53, 0xFF, 0xBC) &&
  parseColor "#fff" == none && parseColor "yellow" == none && parseColor "#GG0000" == none
#guard Color.all.all fun c => nearest c.rgb == c
#guard nearest (255, 255, 0) == .yellow && nearest (255, 0, 0) == .red &&
  nearest (0, 0, 255) == .blue && nearest (0, 255, 0) == .green && nearest (255, 192, 203) == .pink

/-! ## Export -/

/-- One character escaped for XML (`attr`: inside a double-quoted attribute value). -/
def escChar (attr : Bool) (c : Char) : String :=
  match c with
  | '&' => "&amp;"
  | '<' => "&lt;"
  | '>' => "&gt;"
  | '"' => "&quot;"
  | '\r' => "&#13;"
  | '\t' => if attr then "&#9;" else "\t"
  | '\n' => if attr then "&#10;" else "\n"
  | c => if isXmlChar c then c.toString else "�"

/-- A string escaped for XML content (`attr = false`) or a double-quoted attribute value. -/
def escape (attr : Bool) (s : String) : String :=
  s.toList.foldl (fun acc c => acc ++ escChar attr c) ""

#guard escape false "a<b & \"c\" >" == "a&lt;b &amp; &quot;c&quot; &gt;"
#guard escape true "x\ty\nz\r" == "x&#9;y&#10;z&#13;" && escape false "x\ty\nz\r" == "x\ty\nz&#13;"
#guard escape false "a\x00b\x1Fc￾" == "a�b�c�"
#guard escape false "Grüße 😀 𝔸" == "Grüße 😀 𝔸"

/-- Attributes as ` k="v"` pairs. -/
def attrsXml (kvs : List (String × String)) : String :=
  kvs.foldl (fun acc (k, v) => acc ++ " " ++ k ++ "=\"" ++ escape true v ++ "\"") ""

/-- Numbers joined by commas. -/
def numsXml (xs : List Rat) : String := ",".intercalate (xs.map fmtRat)

/-- A box as `left,bottom,right,top`. -/
def boxXml (b : Box) : String := numsXml [b.llx, b.lly, b.urx, b.ury]

/-- US Letter, the page box used when the caller knows none (note icons only). -/
def letter : Box := ⟨0, 0, 612, 792⟩

/-- The `name` of the popup that carries the comment `cid` of the highlight `m`:
`safepdf-mark-ID-popup-CID`, the `/NM` Save gives the popup in the PDF (rule A11). -/
def popupName (m : Mark) (cid : Nat) : String := m.nm ++ "-popup-" ++ toString cid

/-- The comment id in a popup name `popupName` wrote for the highlight named `hl`. -/
def commentIdOf (hl popup : String) : Option Nat :=
  let pre := hl ++ "-popup-"
  if !hl.isEmpty && popup.startsWith pre then (popup.drop pre.length).toString.toNat? else none

#guard commentIdOf "safepdf-mark-4" "safepdf-mark-4-popup-9" == some 9 &&
  commentIdOf "safepdf-mark-4" "safepdf-mark-4-popup" == none &&
  commentIdOf "safepdf-mark-4" "safepdf-mark-5-popup-9" == none &&
  commentIdOf "" "-popup-9" == none

/-- A free text's `/DA` as text: `/Helv SIZE Tf R G B rg` (the PDF's, rule A12). -/
def daText (size : Nat) (c : Marks.Rgb) : String :=
  let u (n : Nat) : String := fmtRat (Core.Raster.Geom.decimalToRat
    (Core.Write.Annots.decRound 4 ((n : Rat) / 255)))
  s!"/Helv {size} Tf {u c.1} {u c.2.1} {u c.2.2} rg"

#guard daText 12 (255, 0, 152) == "/Helv 12 Tf 1 0 0.5961 rg"

/-- One stroke as a `<gesture>` text: `x,y;x,y;…`. -/
def gestureXml (st : List Pt) : String := ";".intercalate (st.map fun p => numsXml [p.x, p.y])

/-- The XFDF element of mark `m` on a page with page box `pb`, dated `date`; `none` for a
highlight without quads. A highlight's `comment` (`Store.commentOf`) goes into its element as
`<contents>` and a `<popup>` named `popupName` (task 9.11). -/
def markXml (pb : Box) (date : String) (m : Mark) (comment : Option Mark := none) :
    Option String :=
  (m.rect pb).map fun r =>
    let common := [("page", toString m.page), ("rect", boxXml r), ("color", m.color.hex),
      ("name", m.nm), ("flags", "print")] ++ (if date.isEmpty then [] else [("date", date)])
    let coords := if m.quads.isEmpty then [] else [("coords", numsXml m.quadPoints)]
    match m.kind with
    | .highlight _ =>
      let start := "<highlight" ++ attrsXml (common ++ [("opacity", "1")] ++ coords)
      match comment with
      | some c =>
        start ++ "><contents>" ++ escape false c.text ++ "</contents><popup" ++
          attrsXml [("page", toString m.page), ("rect", boxXml r), ("name", popupName m c.id),
            ("open", "no")] ++ "/></highlight>"
      | none => start ++ "/>"
    | .note t _ =>
      "<text" ++ attrsXml (common ++ [("icon", "Comment")] ++ coords) ++ "><contents>" ++
        escape false t ++ "</contents></text>"
    | .freeText t _ sz c =>
      let attrs := common.filter (·.1 != "color")
      "<freetext" ++ attrsXml attrs ++ "><contents>" ++ escape false t ++
        "</contents><defaultappearance>" ++ escape false (daText sz c) ++
        "</defaultappearance></freetext>"
    | .ink ss w o _ =>
      let attrs := common.map fun (k, v) => if k == "color" then (k, m.hex) else (k, v)
      "<ink" ++ attrsXml (attrs ++ [("width", toString w), ("opacity", fmtRat ((o : Rat) / 100))]) ++
        "><inklist>" ++ String.join (ss.map fun st => "<gesture>" ++ gestureXml st ++ "</gesture>") ++
        "</inklist></ink>"

/-- **Export**: the XFDF document of every mark of `s` (creation order; a highlight's comment
inside the highlight's element, not on its own); `box` gives page boxes for note icons (US
Letter when `none`), `date` the `date` attribute (omitted when empty), `href` the PDF's file
name for `<f href=…/>`. -/
def toXfdf (s : Store) (box : Nat → Option Box) (date : String) (href : Option String := none) :
    String :=
  let head := "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n" ++
    "<xfdf xmlns=\"http://ns.adobe.com/xfdf/\" xml:space=\"preserve\">\n" ++
    (match href with
     | some h => "<f" ++ attrsXml [("href", h)] ++ "/>\n"
     | none => "")
  let ms := s.marks.toList
  let comments := ms.filterMap s.commentOf
  let annots := ms.filterMap fun m =>
    if m.isNote && comments.any (·.id == m.id) then none
    else markXml ((box m.page).getD letter) date m (s.commentOf m)
  head ++ "<annots>\n" ++ annots.foldl (fun acc x => acc ++ x ++ "\n") "" ++ "</annots>\n</xfdf>\n"

/-! ## Import -/

/-- A mark read from XFDF, before it gets an id in a store. -/
structure Item where
  /-- The `name` attribute (our `safepdf-mark-ID`, or another tool's id). -/
  name : Option String
  /-- Page index (0-based). -/
  page : Nat
  /-- Nearest palette colour. -/
  color : Color
  /-- Highlight or note. -/
  kind : Kind
  deriving Repr, Inhabited

/-- An annotation that was not imported. -/
structure Skip where
  /-- Element name (without namespace prefix). -/
  element : String
  /-- Why. -/
  reason : String
  deriving Repr, Inhabited, BEq

/-- How many skipped annotations the report lists (all are counted). -/
def maxReport : Nat := 100

/-- What an import found. -/
structure Report where
  /-- The marks, in document order. -/
  items : List Item := []
  /-- Number of marks. -/
  count : Nat := 0
  /-- The first `maxReport` skipped annotations, in document order. -/
  skipped : List Skip := []
  /-- Number of skipped annotations. -/
  skippedCount : Nat := 0
  /-- Number of elements outside `<annots>` that are ignored (other than `<f>`, `<ids>`). -/
  ignored : Nat := 0
  deriving Repr, Inhabited

/-- The `page` attribute checked against the page count `pages`. -/
def pageOf (as : List (String × String)) (pages : Option Nat) : Except String Nat :=
  match attr as "page" with
  | none => .error "no page"
  | some p =>
    let ds := (p.toList.dropWhile isWs).reverse.dropWhile isWs |>.reverse
    match (if ds.length ≤ 9 then digitsIn 10 ds else none) with
    | none => .error s!"bad page '{p}'"
    | some n =>
      match pages with
      | some k => if n < k then .ok n else .error s!"page {n} is not in the document"
      | none => .ok n

/-- The `coords` attribute as boxes: `none` when absent, an error when not 8n numbers. -/
def coordsOf (as : List (String × String)) : Except String (Option (List Box)) :=
  match attr as "coords" with
  | none => .ok none
  | some c =>
    match nums c with
    | some xs => if xs.isEmpty || xs.length % 8 != 0 then .error "coords is not 8n numbers"
                 else .ok (some (boxesOf xs))
    | none => .error "coords is not a list of numbers"

/-- The children named `k` (local name) of a node list. -/
def childrenNamed (cs : List Node) (k : String) : List (List Node) :=
  cs.filterMap fun
    | .elem n _ kids => if localName n == k then some kids else none
    | .text _ => none

/-- The concatenated text nodes of a node list. -/
def textOfNodes (cs : List Node) : String :=
  cs.foldl (fun acc c => match c with
    | .text s => acc ++ s
    | .elem .. => acc) ""

/-- The points of a `<gesture>`: `x,y` pairs separated by `;`. -/
def gesturePts (s : String) : Option (List Pt) :=
  (s.splitOn ";").foldr (fun part acc => acc.bind fun ps =>
    if (part.toList.all isWs) then some ps
    else match nums part with
      | some [x, y] => some (⟨x, y⟩ :: ps)
      | _ => none) (some [])

#guard gesturePts "1,2;3.5,4" == some [⟨1, 2⟩, ⟨7 / 2, 4⟩] && gesturePts "1,2;3" == none &&
  gesturePts "1,2; " == some [⟨1, 2⟩]

/-- A number attribute rounded to a natural number in `[lo, hi]` (`d` when absent or bad). -/
def natAttr (as : List (String × String)) (k : String) (scale : Rat) (lo hi d : Nat) : Nat :=
  match (attr as k).bind parseNum with
  | some q => max lo (min hi ((q * scale + 1 / 2).floor.toNat))
  | none => d

/-- The marks of one annotation element (`ln` its local name), or why it is skipped. -/
def itemsOf (lim : Limits) (pages : Option Nat) (ln : String) (as : List (String × String))
    (cs : List Node) : Except String (List Item) := do
  let color := ((attr as "color").bind parseColor).map nearest |>.getD .yellow
  let name := attr as "name"
  if ln == "highlight" then
    let page ← pageOf as pages
    let some quads ← coordsOf as | throw "no coords"
    let hl : Item := { name, page, color, kind := .highlight quads }
    let t := (contentsOf lim cs).getD ""
    -- The comment's id from our popup name (`popupName`), when there is one.
    let cname := cs.findSome? fun
      | .elem n pas _ =>
        if localName n == "popup" then
          ((name.bind fun h => (attr pas "name").bind (commentIdOf h))).map
            (Marks.nmPrefix ++ toString ·)
        else none
      | .text _ => none
    pure (if t.isEmpty then [hl]
      else [hl, { name := cname, page, color, kind := .note t (.quads quads) }])
  else if ln == "text" then
    if (attr as "inreplyto").isSome then throw "reply to another annotation (inreplyto)"
    let page ← pageOf as pages
    let some r := attr as "rect" | throw "no rect"
    let some [x1, y1, x2, y2] := nums r | throw "rect is not 4 numbers"
    let anchor : Anchor := match ← coordsOf as with
      | some qs => .quads qs
      | none => .point ⟨min x1 x2, max y1 y2⟩
    pure [{ name, page, color, kind := .note ((contentsOf lim cs).getD "") anchor }]
  else if ln == "freetext" then
    let page ← pageOf as pages
    let some r := attr as "rect" | throw "no rect"
    let some [x1, y1, x2, y2] := nums r | throw "rect is not 4 numbers"
    let rgb := ((attr as "color").bind parseColor).getD (0, 0, 0)
    let (size, rgb) := match childrenNamed cs "defaultappearance" with
      | kids :: _ =>
        let da := Core.Annot.parseDA (textOfNodes kids).toUTF8.toList
        let b (q : Rat) : Nat := max 0 (min 255 ((q * 255 + 1 / 2).floor.toNat))
        let c := match da.color with
          | [g] => (b g, b g, b g)
          | [r, g, bl] => (b r, b g, b bl)
          | _ => rgb
        (max 1 (min 1000 ((da.size + 1 / 2).floor.toNat)), c)
      | [] => (10, rgb)
    pure [{ name, page, color := .yellow,
            kind := .freeText ((contentsOf lim cs).getD "") ⟨min x1 x2, max y1 y2⟩ size rgb }]
  else if ln == "ink" then
    let page ← pageOf as pages
    let some lists := (childrenNamed cs "inklist").head? | throw "no inklist"
    let gs := childrenNamed lists "gesture"
    let some strokes := gs.foldr (fun g acc => acc.bind fun ss =>
        (gesturePts (textOfNodes g)).map (· :: ss)) (some []) | throw "bad gesture"
    let strokes := strokes.filter (!·.isEmpty)
    if strokes.isEmpty then throw "no strokes"
    let rgb := ((attr as "color").bind parseColor).getD (0, 0, 0)
    pure [{ name, page, color := .yellow,
            kind := .ink strokes (natAttr as "width" 1 1 100 1)
              (natAttr as "opacity" 100 0 100 100) rgb }]
  else throw "unsupported annotation type"

/-- Adds the annotation element `n` of `<annots>` to the report. -/
def annotStep (lim : Limits) (pages : Option Nat) (r : Report) (n : Node) : Report :=
  match n with
  | .text _ => r
  | .elem name as cs =>
    let ln := localName name
    let skip (why : String) : Report :=
      { r with skipped := if r.skippedCount < maxReport then ⟨ln, why⟩ :: r.skipped else r.skipped,
               skippedCount := r.skippedCount + 1 }
    if r.count ≥ lim.maxMarks then skip "too many marks"
    else match itemsOf lim pages ln as cs with
      | .ok its => { r with items := its.reverse ++ r.items, count := r.count + its.length }
      | .error why => skip why

/-- The report of an XFDF tree (`root` must be `xfdf`). -/
def readTree (lim : Limits) (pages : Option Nat) (root : Node) : Except Error Report :=
  match root with
  | .text _ => .error (.notXfdf "")
  | .elem n _ cs =>
    if localName n != "xfdf" then .error (.notXfdf n)
    else
      let r := cs.foldl (fun r c => match c with
        | .text _ => r
        | .elem m _ kids =>
          let lm := localName m
          if lm == "annots" then kids.foldl (annotStep lim pages) r
          else if lm == "f" || lm == "ids" then r
          else { r with ignored := r.ignored + 1 }) ({} : Report)
      .ok { r with items := r.items.reverse, skipped := r.skipped.reverse }

/-- **Import**: the marks of the XFDF document `bytes` (pages checked against `pages` when
given) and what was skipped, or why the input is refused. -/
def readXfdf (lim : Limits) (bytes : ByteArray) (pages : Option Nat := none) :
    Except Error Report :=
  (parse lim bytes).bind (readTree lim pages)

/-- Whether two anchors are equal. -/
def anchorEq : Anchor → Anchor → Bool
  | .quads a, .quads b => a == b
  | .point p, .point q => p == q
  | _, _ => false

/-- Whether two kinds are equal (text, quads, anchor; free text and ink: `Kind.same`). -/
def kindEq : Kind → Kind → Bool
  | .highlight a, .highlight b => a == b
  | .note t a, .note u b => t == u && anchorEq a b
  | a, b => a.same b

/-- Whether two marks have the same content (page, colour, kind; ids not compared). -/
def sameContent (a b : Mark) : Bool :=
  a.page == b.page && a.color == b.color && kindEq a.kind b.kind

/-- **Into the store** (see the module doc): the store, the ids of the added marks (in item
order), and the number of items already present. The added marks follow the old ones in id
order. -/
def importItems (s : Store) (items : List Item) : Store × List Nat × Nat :=
  let old := s.marks.size
  let next0 := s.nextId
  let (s, ids, dups) := items.foldl (fun (s, ids, dups) it =>
    let m : Mark := ⟨0, it.page, it.color, it.kind⟩
    if s.marks.any (sameContent m) then (s, ids, dups + 1)
    else match it.name.bind Marks.idOfNm with
      | some id =>
        if id ≥ next0 && !s.marks.any (·.id == id) then (s.restore { m with id }, id :: ids, dups)
        else let (s, id) := s.add it.page it.color it.kind; (s, id :: ids, dups)
      | none => let (s, id) := s.add it.page it.color it.kind; (s, id :: ids, dups))
    (s, ([] : List Nat), 0)
  let added := (s.marks.extract old s.marks.size).toList.mergeSort (·.id ≤ ·.id)
  ({ s with marks := s.marks.extract 0 old ++ added.toArray }, ids.reverse, dups)

/-! ## Files -/

/-- Reads and imports the XFDF file `path` through the shared capped read
(`Shell.Read.readFile`, task 12.1: at most `lim.maxBytes + 1` bytes through a handle, so a
file that grows while it is read is still refused); an error message for the status bar
otherwise. -/
def readFile (lim : Limits) (path : String) (pages : Option Nat := none) :
    IO (Except String Report) := do
  try
    match ← Shell.Read.readFile path lim.maxBytes .inputBytes with
    | .error _ =>
      -- The size for the message: the file system's, at least the bytes the read saw.
      let size ← try pure (← System.FilePath.metadata path).byteSize.toNat catch _ => pure 0
      return .error (Error.tooLarge (max size (lim.maxBytes + 1)) lim.maxBytes).message
    | .ok bytes => return (readXfdf lim bytes pages).mapError Error.message
  catch e => return .error s!"cannot read {path}: {e}"

/-! ## Checks -/

/-- Parses a string with the default limits. -/
private def p (s : String) : Except Error Node := parse {} s.toUTF8

/-- Whether parsing gives an error satisfying `f`. -/
private def refuses (s : String) (f : Error → Bool) (lim : Limits := {}) : Bool :=
  match parse lim s.toUTF8 with
  | .error e => f e
  | .ok _ => false

private def isOk (s : String) : Bool := (p s).toOption.isSome

-- Well-formed inputs.
#guard isOk "<a/>" && isOk "<?xml version=\"1.0\"?>\n<!-- c --><a x='1' y=\"2\">t<b/><![CDATA[<&>]]></a>\n"
#guard match p "<a x=\"&lt;&#65;&#x1F600;&amp;\tz\">&quot;&apos;&gt;&#13;</a>" with
  | .ok (.elem "a" [("x", "<A😀& z")] [.text "\"'>\r"]) => true
  | _ => false
#guard match p "<a>x\r\ny\rz</a>" with
  | .ok (.elem _ _ [.text "x\ny\nz"]) => true
  | _ => false
-- Byte-order mark.
#guard (parse {} (ByteArray.mk #[0xEF, 0xBB, 0xBF] ++ "<a/>".toUTF8)).toOption.isSome
-- DTDs and entities: never expanded, refused.
#guard refuses "<!DOCTYPE lolz [<!ENTITY lol \"lol\"><!ENTITY lol2 \"&lol;&lol;\">]><a>&lol2;</a>"
  fun | .dtd 0 => true | _ => false
#guard refuses "<!DOCTYPE x SYSTEM \"file:///etc/passwd\"><x/>" fun | .dtd _ => true | _ => false
#guard refuses "<a><!ENTITY x \"y\"></a>" fun | .dtd _ => true | _ => false
#guard refuses "<a>&lol;</a>" fun | .entity _ "lol" => true | _ => false
#guard refuses "<a x=\"&xxe;\"/>" fun | .entity _ "xxe" => true | _ => false
#guard refuses "<a>&#0;</a>" fun | .charRef _ => true | _ => false
#guard refuses "<a>&#xD800;</a>" fun | .charRef _ => true | _ => false
#guard refuses "<a>&#x110000;</a>" fun | .charRef _ => true | _ => false
#guard refuses "<a>&#xFFFE;</a>" fun | .charRef _ => true | _ => false
#guard refuses "<a>&amp</a>" fun | .syntax .. => true | _ => false
#guard refuses "<a>\x01</a>" fun | .badChar _ => true | _ => false
-- Well-formedness.
#guard refuses "<a><b></a></b>" fun | .syntax .. => true | _ => false
#guard refuses "<a>" fun | .syntax .. => true | _ => false
#guard refuses "</a>" fun | .syntax .. => true | _ => false
#guard refuses "<a/><b/>" fun | .syntax .. => true | _ => false
#guard refuses "x<a/>" fun | .syntax .. => true | _ => false
#guard refuses "" fun | .syntax .. => true | _ => false
#guard refuses "<a x='1' x='2'/>" fun | .syntax .. => true | _ => false
#guard refuses "<a x='1'y='2'/>" fun | .syntax .. => true | _ => false
#guard refuses "<a x=1/>" fun | .syntax .. => true | _ => false
#guard refuses "<a x='<'/>" fun | .syntax .. => true | _ => false
#guard refuses "<a x='1" fun | .syntax .. => true | _ => false
#guard refuses "<a><!-- x</a>" fun | .syntax .. => true | _ => false
#guard (parse {} (ByteArray.mk #[0x3C, 0x61, 0xFF, 0x2F, 0x3E])) matches .error .notUtf8
-- Limits: depth, attributes, lengths, nodes, size.
#guard isOk (String.join (List.replicate 32 "<a>") ++ String.join (List.replicate 32 "</a>"))
#guard refuses (String.join (List.replicate 33 "<a>") ++ String.join (List.replicate 33 "</a>"))
  fun | .tooDeep _ 32 => true | _ => false
#guard refuses (String.join (List.replicate 100000 "<a>")) fun | .tooDeep _ 32 => true | _ => false
#guard refuses ("<a" ++ String.join ((List.range 33).map (s!" a{·}='1'")) ++ "/>")
  fun | .tooManyAttrs _ 32 => true | _ => false
#guard isOk ("<a" ++ String.join ((List.range 32).map (s!" a{·}='1'")) ++ "/>")
#guard refuses "<a x='12345'/>" (lim := { maxAttrLen := 4 }) fun | .tooLong _ _ 4 => true | _ => false
#guard refuses "<abcde/>" (lim := { maxNameLen := 4 }) fun | .tooLong _ _ 4 => true | _ => false
#guard refuses "<a>12345</a>" (lim := { maxTextLen := 4 }) fun | .tooLong _ _ 4 => true | _ => false
#guard refuses "<a><b/><b/><b/></a>" (lim := { maxNodes := 3 }) fun | .tooManyNodes 3 => true | _ => false
#guard refuses "<a/>     " (lim := { maxBytes := 8 }) fun | .tooLarge 9 8 => true | _ => false

-- Rich text.
#guard contentsOf {} [.elem "contents-richtext" []
  [.elem "body" [] [.text "\n", .elem "p" [] [.text "Hi ", .elem "span" [] [.text "there"]],
    .text "\n  ", .elem "p" [] [.text "line", .elem "br" [] [], .text "two"]]]] ==
  some "Hi there\nline\ntwo"
#guard contentsOf {} [.elem "contents" [] [.text "plain"],
  .elem "contents-richtext" [] [.text "rich"]] == some "plain"
#guard contentsOf {} [.elem "popup" [] []] == none

private def pb : Box := letter
private def q1 : Box := ⟨100.25, 698, 166, 708.5⟩
private def q2 : Box := ⟨100, 686, 111, 696⟩

private def sample : Store :=
  let s : Store := {}
  let (s, _) := (s.addHighlight 0 .yellow [q1, q2]).getD (s, 0)
  let (s, _) := s.addNote 0 .yellow "Grüße <&> \"x\" 'y'\n\ttab\r😀 𝔸" (.point ⟨300, 400⟩)
  let (s, _) := (s.addHighlight 2 .green [q2]).getD (s, 0)
  let (s, _) := s.addNote 2 .green "comment" (.quads [q2])
  let (s, _) := (s.addHighlight 1 .red [⟨1 / 3, 2, 3, 4⟩]).getD (s, 0)
  let (s, _) := s.addNote 1 .pink "" (.point ⟨10, 700⟩)
  s

/-- Free text and ink (task 9.9). -/
private def sampleEd : Store :=
  let (s, _) := sample.add 0 .yellow (.freeText "Typed <text> & ✓\nline 2" ⟨72.5, 700⟩ 14 (255, 0, 0))
  let (s, _) := s.add 1 .yellow (.ink [[⟨10, 10⟩, ⟨20.25, 30⟩], [⟨5, 5⟩]] 3 40 (0, 96, 223))
  s

/-- Whether two stores hold the same marks (ids included), in order. -/
private def sameMarks (a b : Store) : Bool :=
  a.marks.size == b.marks.size &&
    (a.marks.toList.zip b.marks.toList).all fun (x, y) => x.id == y.id && sameContent x y

private def roundTrip (s : Store) : Option Store :=
  match readXfdf {} (toXfdf s (fun _ => some pb) "D:20261120144414Z" (some "a&b.pdf")).toUTF8 with
  | .ok r => if r.skippedCount == 0 && r.ignored == 0 then some (importItems {} r.items).1 else none
  | .error _ => none

-- Round trip export → import is the identity on our marks, except the coordinate 1/3, which
-- is written to 10⁻⁶.
#guard match roundTrip (sample.remove 5) with
  | some s => sameMarks s (sample.remove 5) && s.nextId == 7
  | none => false
-- Free text and ink (task 9.9) round-trip too, ids, strokes, sizes and colours included.
#guard match roundTrip (sampleEd.remove 5) with
  | some s => sameMarks s (sampleEd.remove 5) && s.nextId == 9
  | none => false
#guard ((toXfdf sampleEd (fun _ => some pb) "" none).splitOn "\n").any (· ==
  "<ink page=\"1\" rect=\"2,2,23.25,33\" color=\"#0060DF\" name=\"safepdf-mark-8\" flags=\"print\" " ++
  "width=\"3\" opacity=\"0.4\"><inklist><gesture>10,10;20.25,30</gesture><gesture>5,5</gesture></inklist></ink>")
#guard match roundTrip sample with
  | some s => s.marks.size == 6 && (s.find? 5).any (fun m => m.quads == [⟨333333 / 1000000, 2, 3, 4⟩])
  | none => false
#guard ((toXfdf sample (fun _ => some pb) "D:1" (some "a&b.pdf")).splitOn "\n").take 4 ==
  ["<?xml version=\"1.0\" encoding=\"UTF-8\"?>",
   "<xfdf xmlns=\"http://ns.adobe.com/xfdf/\" xml:space=\"preserve\">",
   "<f href=\"a&amp;b.pdf\"/>",
   "<annots>"]
#guard (toXfdf sample (fun _ => some pb) "D:1").splitOn "\n" |>.contains
  ("<highlight page=\"0\" rect=\"100,686,166,708.5\" color=\"#FFFF98\" name=\"safepdf-mark-1\" " ++
   "flags=\"print\" date=\"D:1\" opacity=\"1\" " ++
   "coords=\"100.25,708.5,166,708.5,100.25,698,166,698,100,696,111,696,100,686,111,686\"/>")
-- A highlight's comment: `<contents>` and a `<popup>` named after the comment's id, inside
-- the `<highlight>` (task 9.11); no `<text>` of its own.
#guard (toXfdf sample (fun _ => some pb) "").splitOn "\n" |>.contains
  ("<highlight page=\"2\" rect=\"100,686,111,696\" color=\"#53FFBC\" name=\"safepdf-mark-3\" " ++
   "flags=\"print\" opacity=\"1\" coords=\"100,696,111,696,100,686,111,686\">" ++
   "<contents>comment</contents><popup page=\"2\" rect=\"100,686,111,696\" " ++
   "name=\"safepdf-mark-3-popup-4\" open=\"no\"/></highlight>")
#guard !((toXfdf sample (fun _ => some pb) "").splitOn "safepdf-mark-4\"").length > 1
#guard ((toXfdf sample (fun _ => some pb) "").splitOn "<text ").length == 3
-- The comment takes its highlight's colour (as in the PDF, `Save.normalize`); its id comes back.
#guard let s := (sample.remove 5).recolor 4 .blue
  match roundTrip s with
  | some r => (r.find? 4).any (fun m => m.color == .green && m.text == "comment") &&
    sameMarks r (sample.remove 5)
  | none => false
-- An older note on the same quads stays a `<text>`; the comment is still the newest note
-- after the round trip (marks come back in id order).
#guard let s := ((({} : Store).addNote 0 .yellow "older" (.quads [q1])).1.add 0 .yellow
      (.highlight [q1])).1.addNote 0 .yellow "newest" (.quads [q1]) |>.1
  match roundTrip s with
  | some r => sameMarks r s && ((r.find? 2).bind r.commentOf).map (·.id) == some 3
  | none => false
-- A comment created before its highlight (lower id) keeps its id too.
#guard let s := (((({} : Store).addNote 0 .yellow "first" (.quads [q1])).1.add 0 .yellow
      (.highlight [q1])).1)
  match roundTrip s with
  | some r => r.marks.toList.map (·.id) == [1, 2] && (r.find? 1).any (·.text == "first")
  | none => false
-- 9.5d's form (the comment as a separate `<text>` with `coords`) is still imported.
#guard let x := "<xfdf><annots><highlight page='0' color='#53FFBC' coords='0,1,1,1,0,0,1,0' " ++
    "name='safepdf-mark-1'/><text page='0' rect='1,0,21,20' color='#53FFBC' name='safepdf-mark-2' " ++
    "coords='0,1,1,1,0,0,1,0'><contents>old form</contents></text></annots></xfdf>"
  match readXfdf {} x.toUTF8 with
  | .ok r => let s := (importItems {} r.items).1
    s.marks.size == 2 && ((s.find? 1).bind s.commentOf).map (·.text) == some "old form"
  | .error _ => false
-- Re-importing into the same store adds nothing; into a store with used ids, fresh ids.
#guard match readXfdf {} (toXfdf (sample.remove 5) (fun _ => some pb) "").toUTF8 with
  | .ok r => let (s, ids, dups) := importItems (sample.remove 5) r.items
    ids.isEmpty && dups == 5 && s.marks.size == 5
  | .error _ => false
#guard match readXfdf {} (toXfdf (sample.remove 1) (fun _ => some pb) "").toUTF8 with
  | .ok r =>
    let base := ((({} : Store).add 0 .red (.highlight [q1])).1.add 0 .red (.highlight [q2])).1
    let (s, ids, _) := importItems base r.items
    ids == [3, 4, 5, 6, 7] && s.nextId == 8
  | .error _ => false
-- Ids at or above `nextId` are kept; a duplicate id in the file gets a fresh one.
#guard let x := "<xfdf><annots><highlight page='0' coords='0,1,1,1,0,0,1,0' name='safepdf-mark-9'/>" ++
    "<highlight page='0' coords='0,2,1,2,0,0,1,0' name='safepdf-mark-9'/></annots></xfdf>"
  match readXfdf {} x.toUTF8 with
  | .ok r => (importItems {} r.items).2.1 == [9, 10]
  | .error _ => false

-- Other tools' forms: comment in `<contents>`, rich text, replies, other types, bad pages.
#guard let x := "<?xml version='1.0' encoding='UTF-8'?><xfdf xmlns='http://ns.adobe.com/xfdf/'>" ++
    "<annots><highlight color='#FFFF00' page='3' rect='1,2,3,4' coords='1,4,3,4,1,2,3,2' name='a1'>" ++
    "<contents>Nice</contents><popup page='3' rect='0,0,1,1'/></highlight>" ++
    "<text page='0' rect='10,20,30,40' inreplyto='a1'><contents>re</contents></text>" ++
    "<ink page='0' rect='0,0,1,1'/><highlight page='99' coords='0,0,0,0,0,0,0,0'/>" ++
    "<highlight page='0' coords='1,2,3'/><text page='x' rect='0,0,1,1'/>" ++
    "</annots><fields/><f href='x.pdf'/></xfdf>"
  match readXfdf {} x.toUTF8 (pages := some 10) with
  | .ok r =>
    r.count == 2 && r.skippedCount == 5 && r.ignored == 1 &&
    r.skipped.map (·.element) == ["text", "ink", "highlight", "highlight", "text"] &&
    (match r.items with
     | [h, n] => h.page == 3 && h.color == .yellow && n.name == none &&
        kindEq n.kind (.note "Nice" (.quads [⟨1, 2, 3, 4⟩]))
     | _ => false)
  | .error _ => false
#guard (readXfdf {} "<fdf/>".toUTF8) matches .error (.notXfdf "fdf")
#guard match readXfdf { maxMarks := 1 } ("<xfdf><annots>" ++
    "<highlight page='0' coords='0,1,1,1,0,0,1,0'/><highlight page='0' coords='0,1,1,1,0,0,1,0'/>" ++
    "</annots></xfdf>").toUTF8 with
  | .ok r => r.count == 1 && r.skipped == [⟨"highlight", "too many marks"⟩]
  | .error _ => false

end SafePdf.Shell.App.Xfdf
