import SafePdf.Api

/-!
# `viewer --biblean`: full text and identifier detection (task 10.3; Plan.md §6 Phase 10)

After the PDF is open, bib-lean's reader contract (`bib-lean/docs/READER-CONTRACT.md` §3)
offers two optional routes a viewer may call:

* `POST /api/attachments/{key}/fulltext` — "the extracted text, UTF-8, ≤ 32 MiB", answered
  `200 {"bytes": n}`; the server stores it as a search cache (`fulltext/<key>.txt`). The
  format follows the stock viewer (`bib-lean/web/reader.js`, `afterOpen`): the pages' texts
  in page order joined by a form feed `\f` (U+000C), at most `maxFulltextPages` pages,
  content type `text/plain; charset=utf-8`. Here each page's text is our core extraction
  (`SafePdf.Api.pageTextCore` with the default options: annotation appearances included,
  one fresh budget per page) — the same text as `SAFEPDF_PAGE=N inspect --view text`. A
  page whose extraction fails contributes an empty text, so page `i` of the body is always
  page `i` of the PDF; form feeds inside a page's text are dropped for the same reason.
  The body is cut **between pages** before it would exceed `maxFulltextBytes`.
* `POST /api/attachments/{key}/detected` — identifiers found in the PDF text,
  `{"doi"?, "arxiv"?, "isbn"?}` (one value each), answered `202` (a **proposal** the
  library window shows; nothing is fetched or committed, bib-lean Pv5) or `422` (no valid
  identifier). Like the stock viewer, the viewer reads pages 1–2 (`detectPages`) and sends
  the first DOI and the first arXiv identifier found (page 1 before page 2, then text
  order); the contract's body has no field for where they were found, so the page is only
  reported by `--probe`.

The scanners are hand-written (no regular-expression library), total (structural recursion
over the character list, one step per character) and checked by the `#guard`s below:

* **DOI** — Crossref's recommended pattern `10.\d{4,9}/[-._;()/:A-Z0-9]+`
  (case-insensitive), starting at a word boundary (the character before `1` is not a
  letter or digit, so `210.1234/x` is not a DOI); then trailing `.,;:` and unbalanced `)`
  are trimmed (sentence punctuation, a DOI in parentheses).
* **arXiv** — after a prefix `arXiv:` (case-insensitive, blanks allowed after the colon),
  `arxiv.org/abs/` or `arxiv.org/pdf/`: a new-style id `\d{4}\.\d{4,5}(v\d+)?` or an
  old-style id `[a-z-]+(\.[A-Z]{2})?/\d{7}(v\d+)?`. An old-style id is also accepted
  without a prefix when its archive is one of arXiv's archive names (`oldArchives`, e.g.
  `hep-th/9901001`): old papers print the bare id. A bare new-style number (`1234.5678`)
  is never taken, it is too common in running text. The digits must not continue
  (`1706.037621` is not `1706.03762`).

Both lists are deduplicated (DOIs ignoring ASCII case, arXiv ids ignoring the version),
keeping the first occurrence. The server normalises again (`Fetch.parseDoi` /
`Fetch.parseArxiv`: lower case, version dropped) and refuses invalid ones.

`detectedBody` writes the JSON with `jsonString` (a minimal JSON string writer: `"`, `\`
and control characters escaped, everything else verbatim UTF-8); the 10.1 reader
`Http.parseJson` reads it back in the `#guard`s.
-/

namespace SafePdf.Shell.App.BibLean.Text

/-! ## Full text -/

/-- At most this many pages are sent (the stock viewer's `FULLTEXT_MAX_PAGES`). -/
def maxFulltextPages : Nat := 5000

/-- The contract's size limit of a full-text body: 32 MiB. -/
def maxFulltextBytes : Nat := 32 * 1024 * 1024

/-- The page separator of the full text: form feed. -/
def pageSeparator : Char := '\x0c'

/-- A page's text as it goes into the full text: form feeds removed. -/
def cleanPage (s : String) : String :=
  if s.contains pageSeparator then String.ofList (s.toList.filter (· != pageSeparator)) else s

/-- The full-text body: the pages' texts (`cleanPage`) joined by `pageSeparator`, at most
`maxPages` pages, and only as many whole pages as fit in `maxBytes` UTF-8 bytes. Returns the
body and the number of pages in it. -/
def fulltextBody (pages : Array String) (maxPages : Nat := maxFulltextPages)
    (maxBytes : Nat := maxFulltextBytes) : ByteArray × Nat := Id.run do
  let mut out := ByteArray.empty
  let mut n := 0
  for p in pages.toList.take maxPages do
    let b := (cleanPage p).toUTF8
    let sep := if n == 0 then 0 else 1
    if out.size + sep + b.size > maxBytes then break
    if n > 0 then out := out.push 12
    out := out ++ b
    n := n + 1
  return (out, n)

#guard fulltextBody #["a", "b\x0cc", "é"] = ("a\x0cbc\x0cé".toUTF8, 3)
#guard fulltextBody #[] = (ByteArray.empty, 0)
#guard fulltextBody #["", ""] = ("\x0c".toUTF8, 2)
#guard (fulltextBody #["abc", "de", "f"] 5 6).2 = 2
#guard (fulltextBody #["abc", "de", "f"] 2).2 = 2
#guard (fulltextBody #["abcdefg"] 5000 6).2 = 0

/-- The text of page `i` (zero-based) of `d` by the core extraction (`Api.pageTextCore`,
default options: annotation appearances included, a fresh budget); `""` when the page's
extraction fails. -/
def pageTextOf (d : SafePdf.Api.Document) (i : Nat) : String :=
  match SafePdf.Api.pageTextCore d i with
  | .ok pt => pt.text
  | .error _ => ""

/-! ## Identifier scanners -/

/-- ASCII lower case. -/
def lower (c : Char) : Char := c.toLower

/-- A word character for the boundary tests: ASCII letter or digit. -/
def wordChar (c : Char) : Bool := c.isAlphanum

/-- A DOI suffix character of Crossref's pattern: `[-._;()/:A-Z0-9]`, case-insensitive. -/
def doiSuffixChar (c : Char) : Bool := c.isAlphanum || "-._;()/:".contains c

/-- Trailing sentence punctuation and unbalanced closing parentheses removed from a DOI
given **reversed**; `opens`/`closes` count the parentheses still in it. -/
def trimRev (opens closes : Nat) : List Char → List Char
  | c :: r =>
    if ".,;:".contains c then trimRev opens closes r
    else if c == ')' && closes > opens then trimRev opens (closes - 1) r
    else c :: r
  | [] => []

/-- `trimRev` on a suffix in reading order. -/
def trimDoiSuffix (suf : List Char) : List Char :=
  (trimRev (suf.count '(') (suf.count ')') suf.reverse).reverse

/-- A DOI starting exactly at the head of `l` (`10.` registrant `/` suffix), trimmed. -/
def doiAt? : List Char → Option String
  | '1' :: '0' :: '.' :: rest =>
    let reg := rest.takeWhile Char.isDigit
    if reg.length < 4 || reg.length > 9 then none else
    match rest.drop reg.length with
    | '/' :: r2 =>
      let suf := trimDoiSuffix (r2.takeWhile doiSuffixChar)
      if suf.isEmpty then none else some (String.ofList (['1', '0', '.'] ++ reg ++ '/' :: suf))
    | _ => none
  | _ => none

/-- Every DOI in `l`, in text order (with repeats); `prev` is the character before `l`
(a blank at the start), `skip` the characters still inside the last DOI found. -/
def doisAux (prev : Char) (skip : Nat) : List Char → List String
  | [] => []
  | c :: r =>
    if skip > 0 then doisAux c (skip - 1) r
    else if wordChar prev then doisAux c 0 r
    else match doiAt? (c :: r) with
      | some d => d :: doisAux c (d.length - 1) r
      | none => doisAux c 0 r

/-- Every DOI in `s`, in text order (with repeats). -/
def dois (s : String) : List String := doisAux ' ' 0 s.toList

#guard dois "doi:10.1038/nature12373." = ["10.1038/nature12373"]
#guard dois "https://doi.org/10.1103/PhysRevLett.116.061102, and" = ["10.1103/PhysRevLett.116.061102"]
#guard dois "(see 10.1016/S0140-6736(97)11096-0)" = ["10.1016/S0140-6736(97)11096-0"]
#guard dois "(10.1000/xyz)." = ["10.1000/xyz"]
#guard dois "DOI 10.1002/(SICI)1097-4636(199706)35:4" = ["10.1002/(SICI)1097-4636(199706)35:4"]
#guard dois "210.1234/abc 10.123/abc 10.1234567890/x 10.1234/ 10.1234/." = []
#guard dois "10.1234/a 10.5555/b;" = ["10.1234/a", "10.5555/b"]
#guard dois "10.48550/arXiv.1706.03762" = ["10.48550/arXiv.1706.03762"]
#guard dois "doi:10.1234/ab<cd>" = ["10.1234/ab"]
#guard dois "10.1234/x/10.5678/y" = ["10.1234/x/10.5678/y"]

/-- Whether `l` starts with `p`, ignoring ASCII case. -/
def startsWithCI : List Char → List Char → Bool
  | _, [] => true
  | c :: r, p :: ps => lower c == lower p && startsWithCI r ps
  | [], _ :: _ => false

/-- The prefixes after which an arXiv id is expected (lower case). -/
def arxivPrefixes : List String := ["arxiv:", "arxiv.org/abs/", "arxiv.org/pdf/"]

/-- arXiv's archive names (old-style ids `archive/YYMMNNN`, before April 2007). -/
def oldArchives : List String :=
  ["acc-phys", "adap-org", "alg-geom", "ao-sci", "astro-ph", "atom-ph", "bayes-an",
    "chao-dyn", "chem-ph", "cmp-lg", "comp-gas", "cond-mat", "cs", "dg-ga", "funct-an",
    "gr-qc", "hep-ex", "hep-lat", "hep-ph", "hep-th", "math", "math-ph", "mtrl-th", "nlin",
    "nucl-ex", "nucl-th", "patt-sol", "physics", "plasm-ph", "q-alg", "q-bio", "quant-ph",
    "solv-int", "supr-con"]

/-- An optional version `v\d+` at the head of `l`: its characters (empty when absent). -/
def versionAt (l : List Char) : List Char :=
  match l with
  | 'v' :: r =>
    let ds := r.takeWhile Char.isDigit
    if ds.isEmpty || (r.drop ds.length).head?.any Char.isDigit then [] else 'v' :: ds
  | _ => []

/-- Exactly `n₁`…`n₂` digits at the head of `l` (not followed by a further digit). -/
def digitsAt (l : List Char) (lo hi : Nat) : Option (List Char) :=
  let ds := l.takeWhile Char.isDigit
  if lo ≤ ds.length && ds.length ≤ hi then some ds else none

/-- A new-style id `\d{4}\.\d{4,5}(v\d+)?` at the head of `l`. -/
def newStyleAt? (l : List Char) : Option String := do
  let y ← digitsAt l 4 4
  match l.drop 4 with
  | '.' :: r =>
    let n ← digitsAt r 4 5
    some (String.ofList (y ++ '.' :: n ++ versionAt (r.drop n.length)))
  | _ => none

/-- An old-style id `[a-z-]+(\.[A-Z]{2})?/\d{7}(v\d+)?` at the head of `l`; with
`known`, the archive must be one of `oldArchives`. -/
def oldStyleAt? (known : Bool) (l : List Char) : Option String := do
  let arch := l.takeWhile (fun c => c.isLower || c == '-')
  if arch.isEmpty || arch.head? == some '-' then none
  if known && !oldArchives.contains (String.ofList arch) then none
  let r := l.drop arch.length
  let (sub, r) := match r with
    | '.' :: a :: b :: r' => if a.isUpper && b.isUpper then (['.', a, b], r') else ([], r)
    | _ => ([], r)
  match r with
  | '/' :: r =>
    let n ← digitsAt r 7 7
    some (String.ofList (arch ++ sub ++ '/' :: n ++ versionAt (r.drop 7)))
  | _ => none

/-- An arXiv id right after a prefix: blanks skipped, then new- or old-style; with the
number of blanks skipped. -/
def idAfterPrefix? (l : List Char) : Option (String × Nat) :=
  let bl := (l.takeWhile (· == ' ')).length
  let l := l.drop bl
  ((newStyleAt? l).orElse fun _ => oldStyleAt? false l).map (·, bl)

/-- The arXiv id introduced by a prefix at the head of `l`, or a bare old-style id with a
known archive; with the number of characters it spans from the head of `l`. -/
def arxivAt? (l : List Char) : Option (String × Nat) :=
  match arxivPrefixes.find? (fun p => startsWithCI l p.toList) with
  | some p => (idAfterPrefix? (l.drop p.length)).map fun (a, bl) => (a, p.length + bl + a.length)
  | none => (oldStyleAt? true l).map fun a => (a, a.length)

/-- Every arXiv id in `l`, in text order (with repeats); `prev` and `skip` as in
`doisAux`. -/
def arxivsAux (prev : Char) (skip : Nat) : List Char → List String
  | [] => []
  | c :: r =>
    if skip > 0 then arxivsAux c (skip - 1) r
    else if wordChar prev then arxivsAux c 0 r
    else match arxivAt? (c :: r) with
      | some (a, n) => a :: arxivsAux c (n - 1) r
      | none => arxivsAux c 0 r

/-- Every arXiv id in `s`, in text order (with repeats). -/
def arxivs (s : String) : List String := arxivsAux ' ' 0 s.toList

#guard arxivs "arXiv:1706.03762v7 [cs.CL] 2 Aug 2023" = ["1706.03762v7"]
#guard arxivs "ARXIV: 2101.00001" = ["2101.00001"]
#guard arxivs "https://arxiv.org/abs/1501.00001v2." = ["1501.00001v2"]
#guard arxivs "arxiv.org/pdf/2301.12345" = ["2301.12345"]
#guard arxivs "arXiv:hep-th/9901001v1" = ["hep-th/9901001v1"]
#guard arxivs "arXiv:math.AG/0309136" = ["math.AG/0309136"]
#guard arxivs "astro-ph/9805201" = ["astro-ph/9805201"]
#guard arxivs "foo-bar/1234567 xhep-th/9901001" = []
#guard arxivs "1706.03762 arXiv:1706.037621 arXiv:170.03762 arXiv:1706.123" = []
#guard arxivs "arXiv:1706.03762v" = ["1706.03762"]
#guard arxivs "arXiv:1706.03762 and arXiv:1706.03762v2" = ["1706.03762", "1706.03762v2"]

/-! ## Detection -/

/-- An identifier and the zero-based page it was found on. -/
structure Found where
  /-- The identifier as written in the text (trimmed). -/
  id : String
  /-- Zero-based page. -/
  page : Nat
  deriving Repr, BEq, Inhabited

/-- Keeps the first `Found` of each `key`. -/
def dedupBy (key : String → String) (xs : List Found) : List Found :=
  (xs.foldl (fun (seen, acc) f =>
    let k := key f.id
    if seen.contains k then (seen, acc) else (k :: seen, f :: acc)) (([] : List String), ([] : List Found))).2.reverse

/-- An arXiv id without its version (for deduplication). -/
def unversioned (a : String) : String :=
  let r := a.toList.reverse
  let ds := r.takeWhile Char.isDigit
  match r.drop ds.length with
  | 'v' :: rest => if ds.isEmpty then a else String.ofList rest.reverse
  | _ => a

#guard unversioned "1706.03762v7" = "1706.03762"
#guard unversioned "hep-th/9901001" = "hep-th/9901001"

/-- Pages read for detection (the stock viewer's `DETECT_PAGES`). -/
def detectPages : Nat := 2

/-- What detection found on the first pages. -/
structure Detection where
  /-- DOIs, deduplicated ignoring ASCII case, first occurrence first. -/
  dois : List Found
  /-- arXiv ids, deduplicated ignoring the version, first occurrence first. -/
  arxivs : List Found
  deriving Repr, Inhabited

/-- Detection over the texts of the first `detectPages` pages (zero-based page `i` is
`pages[i]`). -/
def detect (pages : List String) : Detection :=
  let ps := (pages.take detectPages).zipIdx
  { dois := dedupBy (fun s => String.ofList (s.toList.map lower))
      (ps.flatMap fun (t, i) => (dois t).map ({ id := ·, page := i }))
    arxivs := dedupBy unversioned (ps.flatMap fun (t, i) => (arxivs t).map ({ id := ·, page := i })) }

/-- Whether detection found anything to propose. -/
def Detection.any (d : Detection) : Bool := !d.dois.isEmpty || !d.arxivs.isEmpty

/-! ## JSON body -/

/-- Four lowercase hex digits of `n < 65536`. -/
def hex4 (n : Nat) : String :=
  let d (k : Nat) : Char := "0123456789abcdef".toList.getD ((n / k) % 16) '0'
  String.ofList [d 4096, d 256, d 16, d 1]

/-- A JSON string literal (RFC 8259 §7): `"` and `\` escaped, control characters as
`\n`/`\r`/`\t`/`\uXXXX`, every other character verbatim. -/
def jsonString (s : String) : String :=
  "\"" ++ String.join (s.toList.map fun c =>
    if c == '"' then "\\\"" else if c == '\\' then "\\\\"
    else if c == '\n' then "\\n" else if c == '\r' then "\\r" else if c == '\t' then "\\t"
    else if c.toNat < 32 || c.toNat == 127 then "\\u" ++ hex4 c.toNat
    else c.toString) ++ "\""

#guard jsonString "a\"b\\c\nd\x01é" = "\"a\\\"b\\\\c\\nd\\u0001é\""

/-- The `POST …/detected` body: `{"doi": …, "arxiv": …}` with the first DOI and the first
arXiv id (members only for what was found); `none` when nothing was found. -/
def detectedBody (d : Detection) : Option String :=
  let ms := (d.dois.head?.map fun f => s!"\"doi\":{jsonString f.id}").toList ++
    (d.arxivs.head?.map fun f => s!"\"arxiv\":{jsonString f.id}").toList
  if ms.isEmpty then none else some ("{" ++ ",".intercalate ms ++ "}")

#guard detectedBody (detect ["Title\narXiv:1706.03762v7 [cs.CL]\ndoi:10.1000/XYZ.",
    "see 10.1000/xyz and 10.2000/abc arXiv:1706.03762"]) =
  some "{\"doi\":\"10.1000/XYZ\",\"arxiv\":\"1706.03762v7\"}"
#guard (detect ["a", "b", "arXiv:1706.03762"]).any = false
#guard (detect ["x", "doi:10.1000/a"]).dois == [{ id := "10.1000/a", page := 1 }]
#guard detectedBody (detect ["nothing here"]) = none

/-- One line for `--probe`: `id (page N)` for each found identifier (one-based pages),
`none` when there are none. -/
def foundLine (xs : List Found) : String :=
  if xs.isEmpty then "none"
  else ", ".intercalate (xs.map fun f => s!"{f.id} (page {f.page + 1})")

#guard foundLine [{ id := "10.1000/a", page := 0 }, { id := "10.1000/b", page := 1 }] =
  "10.1000/a (page 1), 10.1000/b (page 2)"

end SafePdf.Shell.App.BibLean.Text
