import SafePdf.Api
import SafePdf.Shell.App.BibLean.Http

/-!
# `viewer --biblean`: launch as bib-lean's reader (task 10.1; Plan.md §6 Phase 10)

bib-lean starts the viewer as a child process through its reader contract
(`bib-lean/docs/READER-CONTRACT.md` §2): the server origin in `BIBLEAN_SERVER`, the
attachment's item key in `BIBLEAN_ATTACHMENT`, optionally the zero-based page in
`BIBLEAN_PAGE`, and the bearer token as one line on **file descriptor 3** — never in argv or
the environment. `openFromBibLean` does the whole launch without a window:

1. `BIBLEAN_SERVER` must be `http://127.0.0.1:PORT` or `http://localhost:PORT`
   (`Http.Origin.parse?`); anything else, in particular a non-loopback host, is a usage
   error (exit 2). The client only ever connects to `127.0.0.1`.
2. `BIBLEAN_ATTACHMENT` must be an item key (eight characters of bib-lean's alphabet
   `23456789ABCDEFGHIJKLMNPQRSTUVWXYZ`, `keyOk`), so it can go into a path as is (exit 2
   otherwise).
3. The token is read once from `/dev/fd/3` (`readToken`): exactly 64 lowercase hex digits and
   an optional `\n`; a missing descriptor or anything else is exit 3 ("no valid token on file
   descriptor 3"), as the stock viewer does (contract §5).
4. `GET /api/attachments/{key}/file` → the bytes → `SafePdf.Api.openBytes` (a non-`200`
   answer, e.g. `401` for a wrong token, or a file that does not open, is exit 1).
5. `GET /api/items/{key}` → the attachment (`item.parentItem`, `item.title`), then
   `GET /api/items/{parent}` → the parent's `fields.title`: the window title is the parent's
   title, else the attachment's, else the key (`titleOf`; control characters removed, at most
   `maxTitleChars` characters). A failure here only loses the title.
6. The page: `BIBLEAN_PAGE` (one to six decimal digits; anything else is ignored, as the stock
   viewer does), else a `--page N` argument (an `exec` template's `{page}`); used only when it
   is below the page count (contract §2.1: a viewer MAY ignore it otherwise).

**Token hygiene.** The token is held only as `Http.Token` (no `ToString`/`Repr`), written
only into the `Authorization` header of requests to the loopback origin, and never logged:
error messages name the method, the path (holding only the key) and the HTTP status. Lean
offers no way to wipe a `ByteArray`, so the bytes stay in memory until collected (they are
kept in `Session` for the later tasks 10.2–10.3, which post annotations and text). The
descriptor is read through `/dev/fd/3`, which opens a *new* descriptor (closed when the
handle is dropped); the inherited fd 3 itself cannot be closed from Lean without a C call,
so the contract's SHOULD "close fd 3 after" is not met (the pipe is drained to its end; the
viewer starts no child processes that could inherit it).

**Nothing from the library on stderr** (bib-lean `docs/SECURITY.md`): errors carry keys and
statuses only, never titles or bodies.
-/

namespace SafePdf.Shell.App.BibLean.Launch

open SafePdf.Shell.App.BibLean.Http (Origin JVal)

/-! ## Pure parts -/

/-- The 33 characters of a bib-lean item key (Zotero's alphabet). -/
def keyAlphabet : String := "23456789ABCDEFGHIJKLMNPQRSTUVWXYZ"

/-- An item key: exactly eight characters of `keyAlphabet`. -/
def keyOk (k : String) : Bool := k.length == 8 && k.toList.all (fun c => keyAlphabet.toList.contains c)

#guard keyOk "ABCD2345"
#guard !keyOk "ABCD234"
#guard !keyOk "abcd2345"
#guard !keyOk "ABCD234O"
#guard !keyOk "../../x1"

/-- The page from `BIBLEAN_PAGE`: one to six decimal digits, anything else is `none`
(as the stock viewer, `biblean reader`'s `pageOf?`). -/
def pageOf? (v : Option String) : Option Nat := do
  let s ← v
  if s.isEmpty || s.length > 6 || !s.all Char.isDigit then none else s.toNat?

#guard pageOf? (some "4") = some 4
#guard pageOf? (some "000012") = some 12
#guard pageOf? (some "1234567") = none
#guard pageOf? (some "-1") = none
#guard pageOf? (some "") = none
#guard pageOf? none = none

/-- The longest window title taken from the library. -/
def maxTitleChars : Nat := 200

/-- A title for display: control characters (C0, DEL, C1) and line/paragraph separators
dropped, surrounding blanks trimmed, at most `maxTitleChars` characters; `none` when nothing
is left. -/
def cleanTitle (s : String) : Option String :=
  let t := String.ofList (s.toList.filter fun c =>
    !(c.toNat < 32 || (127 ≤ c.toNat && c.toNat < 160) || c.toNat == 0x2028 || c.toNat == 0x2029))
  let t := t.trimAscii.toString
  if t.isEmpty then none else some (String.ofList (t.toList.take maxTitleChars))

#guard cleanTitle "  A\ntitle\u0007 " = some "Atitle"
#guard cleanTitle "\t\n" = none

/-- The `item` object of a `GET /api/items/{key}` answer. -/
def itemOf? (detail : JVal) : Option JVal := detail.get? "item"

/-- The parent's key of an attachment (`item.parentItem`), when it is a valid key. -/
def parentKey? (detail : JVal) : Option String := do
  let k ← (← itemOf? detail).get? "parentItem" >>= JVal.str?
  if keyOk k then some k else none

/-- An attachment's own title (`item.title`). -/
def attachmentTitle? (detail : JVal) : Option String := do
  cleanTitle (← (← itemOf? detail).get? "title" >>= JVal.str?)

/-- A regular item's title (`item.fields.title`). -/
def regularTitle? (detail : JVal) : Option String := do
  let fields ← (← itemOf? detail).get? "fields"
  cleanTitle (← fields.get? "title" >>= JVal.str?)

/-- The window title: the parent's title, else the attachment's, else the key. -/
def titleOf (key : String) (att parent : Option JVal) : String :=
  ((parent.bind regularTitle?).orElse fun _ => att.bind attachmentTitle?).getD key

/-- Parses a JSON body (UTF-8). -/
def parseJson? (b : ByteArray) : Option JVal := (Http.parseJson b).toOption

private def attJson : JVal :=
  (parseJson? "{\"version\":3,\"item\":{\"key\":\"ATT23456\",\"itemType\":\"attachment\",\"title\":\"Full Text PDF\",\"parentItem\":\"PAR23456\"},\"children\":[]}".toUTF8).getD .null
private def parJson : JVal :=
  (parseJson? "{\"version\":3,\"item\":{\"key\":\"PAR23456\",\"itemType\":\"journalArticle\",\"fields\":{\"title\":\"On \\u0007Safe\\nPDFs\"},\"creators\":[],\"parentItem\":null},\"children\":[]}".toUTF8).getD .null

#guard parentKey? attJson = some "PAR23456"
#guard parentKey? parJson = none
#guard titleOf "ATT23456" (some attJson) (some parJson) = "On SafePDFs"
#guard titleOf "ATT23456" (some attJson) none = "Full Text PDF"
#guard titleOf "ATT23456" none none = "ATT23456"
#guard titleOf "ATT23456" (some .null) (some (.obj #[("item", .obj #[])])) = "ATT23456"

/-- The `error` code of an error body `{"error": code, "message": text}` (a short
identifier; the message is not used since it could quote library data). -/
def errorCode? (b : ByteArray) : Option String := do
  let c ← (← parseJson? b).get? "error" >>= JVal.str?
  if !c.isEmpty && c.length ≤ 40 && c.all (fun ch => ch.isAlphanum || ch == '_' || ch == '-')
  then some c else none

#guard errorCode? "{\"error\":\"unauthorized\",\"message\":\"x\"}".toUTF8 = some "unauthorized"
#guard errorCode? "{\"error\":\"a b\"}".toUTF8 = none

/-- A file name for the attachment, from its title: `/`, `\`, NUL and leading dots removed,
at most 100 characters, `.pdf` appended; the key when nothing is left. -/
def fileNameOf (key title : String) : String :=
  let t := String.ofList ((title.toList.filter fun c => c != '/' && c != '\\' && c.toNat != 0
    && c.toNat ≥ 32).dropWhile (· == '.'))
  let t := String.ofList (t.trimAscii.toString.toList.take 100)
  (if t.isEmpty then key else t) ++ ".pdf"

#guard fileNameOf "ATT23456" "On ../Safe/PDFs" = "On ..SafePDFs.pdf"
#guard fileNameOf "ATT23456" "a/b" = "ab.pdf"
#guard fileNameOf "ATT23456" "../.." = "ATT23456.pdf"
#guard fileNameOf "ATT23456" "" = "ATT23456.pdf"

/-! ## The launch -/

/-- Where the viewer talks to: the loopback origin, the attachment key and the token. -/
structure Session where
  /-- `BIBLEAN_SERVER`. -/
  origin : Origin
  /-- `BIBLEAN_ATTACHMENT`. -/
  key : String
  /-- The bearer token from file descriptor 3. -/
  token : Http.Token

/-- A successful launch. -/
structure Opened where
  /-- The server session (for the later routes of tasks 10.2–10.3). -/
  session : Session
  /-- The window title (`titleOf`). -/
  title : String
  /-- The page asked for (`BIBLEAN_PAGE`, else `--page`), zero-based, before clamping. -/
  requested : Option Nat
  /-- The page to open at: `requested` when it is below the page count. -/
  page : Option Nat
  /-- The PDF bytes as served. -/
  bytes : ByteArray
  /-- The opened document. -/
  document : SafePdf.Api.Document

/-- Why a launch failed, with the contract's exit code (§5). -/
inductive Failure where
  /-- A usage error: bad `BIBLEAN_SERVER`, `BIBLEAN_ATTACHMENT` or arguments (exit 2). -/
  | usage (msg : String)
  /-- No valid token on file descriptor 3 (exit 3). -/
  | noToken
  /-- The server refused or the file did not open (exit 1). -/
  | failed (msg : String)

/-- The exit code of a failure: 2 usage, 3 no token, 1 otherwise (contract §5). -/
def Failure.exitCode : Failure → UInt32
  | .usage _ => 2
  | .noToken => 3
  | .failed _ => 1

/-- The message of a failure (no token, no title, no body). -/
def Failure.message : Failure → String
  | .usage m => m
  | .noToken => "no valid token on file descriptor 3"
  | .failed m => m

/-- The file the token is read from: the inherited file descriptor 3. -/
def tokenFd : System.FilePath := "/dev/fd/3"

/-- Reads the token once from `path` (default `/dev/fd/3`): up to the first `\n` or the end of
the file, at most 66 bytes, then `Token.ofLine?`. `none` when the descriptor is not open or
does not hold a valid token. -/
def readToken (path : System.FilePath := tokenFd) : IO (Option Http.Token) := do
  try
    let h ← IO.FS.Handle.mk path .read
    let mut buf := ByteArray.empty
    for _ in [0:67] do
      if buf.size > 65 || buf.data.contains 10 then break
      let c ← h.read 66
      if c.isEmpty then break
      buf := buf ++ c
    return Http.Token.ofLine? buf
  catch _ => return none

/-- Limits for the PDF: the body may be as large as the parser accepts
(`Limits.maxInputBytes`); two minutes. -/
def fileLimits : Http.Limits :=
  { maxBodyBytes := (SafePdf.Limits.default).maxInputBytes, timeoutMs := 120000 }

/-- Limits for JSON answers: 16 MiB, thirty seconds. -/
def jsonLimits : Http.Limits := { timeoutMs := 30000 }

/-- `GET path` on the session's server. -/
def get (s : Session) (path : String) (lim : Http.Limits) : IO Http.Response :=
  Http.exchange s.origin s.token "GET" path none lim

/-- `GET /api/items/{key}` as JSON; `none` on any failure. -/
def itemDetail? (s : Session) (key : String) : IO (Option JVal) := do
  try
    let r ← get s s!"/api/items/{key}" jsonLimits
    return if r.status == 200 then parseJson? r.body else none
  catch _ => return none

/-- The whole launch (see the module documentation). `env` reads the environment (tests pass
their own), `argPage` is a `--page` argument, `tokenPath` the token descriptor. -/
def openFromBibLean (env : String → IO (Option String) := fun n => IO.getEnv n)
    (argPage : Option Nat := none) (tokenPath : System.FilePath := tokenFd) :
    IO (Except Failure Opened) := do
  let some server ← env "BIBLEAN_SERVER"
    | return .error (.usage "BIBLEAN_SERVER is not set (not launched by bib-lean)")
  let some origin := Origin.parse? server
    | return .error (.usage
        "BIBLEAN_SERVER must be http://127.0.0.1:PORT or http://localhost:PORT (loopback only)")
  let some key ← env "BIBLEAN_ATTACHMENT"
    | return .error (.usage "BIBLEAN_ATTACHMENT is not set (not launched by bib-lean)")
  unless keyOk key do return .error (.usage "BIBLEAN_ATTACHMENT is not an item key")
  let some token ← readToken tokenPath | return .error .noToken
  let s : Session := { origin, key, token }
  let path := s!"/api/attachments/{key}/file"
  let r ← try get s path fileLimits
    catch e => return .error (.failed s!"{e}")
  unless r.status == 200 do
    let code := (errorCode? r.body).map (s!" ({·})") |>.getD ""
    return .error (.failed s!"GET {path} answered HTTP {r.status}{code}")
  let document ← match SafePdf.Api.openBytes r.body with
    | .ok d => pure d
    | .error e => return .error (.failed s!"attachment {key}: cannot open the PDF: {e}")
  let att ← itemDetail? s key
  let parent ← match att.bind parentKey? with
    | some p => itemDetail? s p
    | none => pure none
  let requested := (pageOf? (← env "BIBLEAN_PAGE")).orElse fun _ => argPage
  let page := requested.filter (· < document.pageCount)
  return .ok { session := s, title := titleOf key att parent, requested, page,
               bytes := r.body, document }

end SafePdf.Shell.App.BibLean.Launch
