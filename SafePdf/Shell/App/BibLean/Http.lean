import Std.Async.TCP
import Std.Async.Timer

/-!
# Minimal HTTP/1.1 client for bib-lean's loopback server (task 10.1; Plan.md §6 Phase 10)

The viewer's half of bib-lean's reader contract (`bib-lean/docs/READER-CONTRACT.md` §2–§3)
speaks HTTP/1.1 to `BIBLEAN_SERVER`, which is always loopback. The model,
`bib-lean/BibLean/Client/Http.lean`, runs `curl` with the token in a 0600 temporary file;
here the request goes over a plain TCP socket (`Std.Async.TCP`, part of the Lean v4.36.0
toolchain — no new dependency, no child process, and the token never touches the disk).

Unverified shell code (Plan.md §10 `SafePdf/Shell/`), but split so that everything that
reads server bytes is **pure and IO-free** and checked by `#guard`s below:

* `Origin.parse?` — `BIBLEAN_SERVER` must be `http://127.0.0.1:PORT` or
  `http://localhost:PORT` (one trailing `/` allowed, port 1–65535); every other host,
  scheme, user part or path is refused. The client only ever connects to `127.0.0.1`
  (it never resolves a name), so a non-loopback server is unreachable by construction.
* `Token.ofLine?` — the bearer token: exactly 64 lowercase hex digits, optionally followed by
  one `\n` (contract §2). `Token` has no `ToString`/`Repr`, so it cannot be printed by
  accident; its bytes go only into the `Authorization: Bearer` header (`requestBytes`).
* `requestBytes` — the request: `METHOD PATH HTTP/1.1`, `Host`, `Authorization`, no `Origin`
  (contract §3: a viewer that is not a web page sends none), `Connection: close`, and
  `Content-Length` for a body. A path containing anything but `pathOk` characters is refused.
* `parseResponse` — status line, header fields (names lower-cased; obsolete line folding,
  bare LF line ends, a malformed or duplicated-but-different `Content-Length` and any
  transfer coding other than `chunked` are errors), then the body framed by
  `Content-Length`, `chunked` (`decodeChunked`, trailers skipped) or the end of the
  connection. `1xx` answers are errors (the client never sends `Expect`).

`exchange` is the only `IO`: connect to `127.0.0.1:port`, send, read until the response is
complete (or the server closes), bounded by `Limits` (header bytes, body bytes, overall
time; `Async.race` against a libuv timer). Nothing is logged; errors carry the method, the
path (which holds only the attachment key) and the status, never the token or a body.
-/

namespace SafePdf.Shell.App.BibLean.Http

/-! ## Server origin -/

/-- The server named by `BIBLEAN_SERVER`: always loopback. -/
structure Origin where
  /-- The host as written (`127.0.0.1` or `localhost`), sent in the `Host` header. -/
  host : String
  /-- The TCP port (1–65535). -/
  port : UInt16
  deriving DecidableEq, Repr

/-- Parses `BIBLEAN_SERVER`: `http://127.0.0.1:PORT` or `http://localhost:PORT`, at most one
trailing `/`, `PORT` one to five decimal digits in 1–65535. Anything else (another host, an
IPv6 or non-loopback address, `https`, user info, a path or query) is `none`. -/
def Origin.parse? (s : String) : Option Origin :=
  let s := if s.endsWith "/" then (s.dropEnd 1).toString else s
  let port? (pre host : String) : Option Origin :=
    if s.startsWith pre then
      let p := (s.drop pre.length).toString
      if !p.isEmpty && p.length ≤ 5 && p.all Char.isDigit then
        match p.toNat? with
        | some n => if 1 ≤ n && n ≤ 65535 then some ⟨host, n.toUInt16⟩ else none
        | none => none
      else none
    else none
  (port? "http://127.0.0.1:" "127.0.0.1").orElse fun _ => port? "http://localhost:" "localhost"

/-- The `Host` header value. -/
def Origin.hostHeader (o : Origin) : String := s!"{o.host}:{o.port}"

/-- The socket address the client connects to: `127.0.0.1:port`, whatever `host` says
(`localhost` is never resolved). -/
def Origin.address (o : Origin) : Std.Net.SocketAddress :=
  .v4 ⟨Std.Net.IPv4Addr.ofParts 127 0 0 1, o.port⟩

#guard Origin.parse? "http://127.0.0.1:8080" = some ⟨"127.0.0.1", 8080⟩
#guard Origin.parse? "http://127.0.0.1:8080/" = some ⟨"127.0.0.1", 8080⟩
#guard Origin.parse? "http://localhost:1" = some ⟨"localhost", 1⟩
#guard Origin.parse? "http://127.0.0.1:65535" = some ⟨"127.0.0.1", 65535⟩
#guard Origin.parse? "http://127.0.0.1:65536" = none
#guard Origin.parse? "http://127.0.0.1:0" = none
#guard Origin.parse? "http://127.0.0.1:" = none
#guard Origin.parse? "http://127.0.0.1:80//" = none
#guard Origin.parse? "http://127.0.0.1:80/api" = none
#guard Origin.parse? "http://10.0.0.1:8080" = none
#guard Origin.parse? "http://127.0.0.1.evil.example:80" = none
#guard Origin.parse? "http://user@127.0.0.1:80" = none
#guard Origin.parse? "https://127.0.0.1:443" = none
#guard Origin.parse? "http://[::1]:8080" = none
#guard Origin.parse? "http://example.com:80" = none
#guard Origin.parse? "http://127.0.0.1:+80" = none
#guard Origin.parse? "" = none

/-! ## Token -/

/-- The bearer token: 64 lowercase hex digits as ASCII bytes. Deliberately without
`ToString`, `Repr` or `Inhabited` instances (it can only be put into a request). -/
structure Token where
  private mk ::
  /-- The 64 ASCII bytes. -/
  bytes : ByteArray

/-- A lowercase hex digit (ASCII). -/
def isLowerHex (b : UInt8) : Bool := (48 ≤ b && b ≤ 57) || (97 ≤ b && b ≤ 102)

/-- The token from what file descriptor 3 delivered: exactly 64 lowercase hex digits,
optionally followed by a single `\n` (contract §2). Everything else is `none`. -/
def Token.ofLine? (b : ByteArray) : Option Token :=
  let core := if b.size == 65 && b[64]? == some 10 then b.extract 0 64 else b
  if core.size == 64 && core.data.all isLowerHex then some ⟨core⟩ else none

#guard (Token.ofLine? ("0123456789abcdef".toUTF8 ++ "0123456789abcdef".toUTF8 ++
  "0123456789abcdef".toUTF8 ++ "0123456789abcdef".toUTF8 ++ "\n".toUTF8)).isSome
#guard (Token.ofLine? (String.ofList (List.replicate 64 'a')).toUTF8).isSome
#guard (Token.ofLine? (String.ofList (List.replicate 64 'A')).toUTF8).isNone
#guard (Token.ofLine? (String.ofList (List.replicate 63 'a')).toUTF8).isNone
#guard (Token.ofLine? (String.ofList (List.replicate 65 'a')).toUTF8).isNone
#guard (Token.ofLine? ((String.ofList (List.replicate 64 'a')) ++ "\r\n").toUTF8).isNone
#guard (Token.ofLine? ((String.ofList (List.replicate 64 'a')) ++ "\n\n").toUTF8).isNone
#guard (Token.ofLine? ByteArray.empty).isNone

/-! ## Requests -/

/-- Characters allowed in a request path: unreserved and sub-delimiter characters, `/`,
`:`, `@`, `?`, `=`, `&`, `%` (no space, control character, `#` or non-ASCII). -/
def pathChar (c : Char) : Bool :=
  c.isAlphanum || "-._~/:@?=&%!$'()*+,;".contains c

/-- A request path: starts with `/`, only `pathChar`s. -/
def pathOk (p : String) : Bool := p.startsWith "/" && p.all pathChar

#guard pathOk "/api/attachments/ABCD2345/file"
#guard !pathOk "/api/x y"
#guard !pathOk "/api/x\r\nHost: evil"
#guard !pathOk "api/x"

/-- A request method: one to sixteen uppercase ASCII letters. -/
def methodOk (m : String) : Bool := !m.isEmpty && m.length ≤ 16 && m.all Char.isUpper

/-- The bytes of one request. `none` for an invalid method or path, or a content type
with a control character. The token goes only into `Authorization: Bearer`. -/
def requestBytes (o : Origin) (tok : Token) (method path : String)
    (body : Option (ByteArray × String) := none) : Option ByteArray := do
  unless methodOk method && pathOk path do none
  let head := s!"{method} {path} HTTP/1.1\r\nHost: {o.hostHeader}\r\nAccept: */*\r\n"
  let mut tail := "Connection: close\r\n"
  if let some (b, ct) := body then
    unless ct.all (fun c => ' ' ≤ c && c.toNat < 127) do none
    tail := tail ++ s!"Content-Type: {ct}\r\nContent-Length: {b.size}\r\n"
  let pre := head.toUTF8 ++ "Authorization: Bearer ".toUTF8 ++ tok.bytes ++ "\r\n".toUTF8 ++
    (tail ++ "\r\n").toUTF8
  return match body with
    | some (b, _) => pre ++ b
    | none => pre

/-! ## Responses -/

/-- A complete response. -/
structure Response where
  /-- The status code. -/
  status : Nat
  /-- Header fields in order, names lower-cased, values trimmed. -/
  headers : Array (String × String)
  /-- The body (after `chunked` decoding). -/
  body : ByteArray

/-- The value of header `name` (lower-case), the first one if repeated. -/
def Response.header? (r : Response) (name : String) : Option String :=
  (r.headers.find? (·.1 == name)).map (·.2)

/-- Size limits and the time limit of one exchange. -/
structure Limits where
  /-- Status line plus header fields. -/
  maxHeaderBytes : Nat := 64 * 1024
  /-- Decoded body. -/
  maxBodyBytes : Nat := 16 * 1024 * 1024
  /-- The whole exchange (connect, send, receive), in milliseconds. -/
  timeoutMs : Nat := 60000

/-- How the body is delimited (RFC 9112 §6). -/
inductive Framing where
  /-- `Content-Length: n`. -/
  | length (n : Nat)
  /-- `Transfer-Encoding: chunked`. -/
  | chunked
  /-- Until the server closes the connection. -/
  | close
  deriving DecidableEq, Repr

/-- The first index `i ≥ start` with `b[i..i+4] = CR LF CR LF`; the result is the index just
after it. -/
def findHeaderEnd (b : ByteArray) (start : Nat := 0) : Option Nat :=
  go start
where
  /-- Scans from `i`. -/
  go (i : Nat) : Option Nat :=
    if h : i + 3 < b.size then
      if b[i] == 13 && b[i+1] == 10 && b[i+2] == 13 && b[i+3] == 10 then some (i + 4)
      else go (i + 1)
    else none
  termination_by b.size - i

#guard findHeaderEnd "HTTP/1.1 200 OK\r\n\r\nbody".toUTF8 = some 19
#guard findHeaderEnd "HTTP/1.1 200 OK\r\n".toUTF8 = none

/-- A header-field name: an RFC 9110 token. -/
def tokenChar (c : Char) : Bool := c.isAlphanum || "!#$%&'*+-.^_`|~".contains c

/-- Parses the head (status line and fields, without the final blank line). Every line must
end in CR LF (a bare LF is an error), no obsolete folding. -/
def parseHead (head : ByteArray) : Except String (Nat × Array (String × String)) := do
  let some s := String.fromUTF8? head | throw "response head is not UTF-8"
  let lines := s.splitOn "\r\n"
  -- `head` ends with CR LF, so the last piece is empty.
  let lines := if lines.getLast? == some "" then lines.dropLast else lines
  let some statusLine := lines.head? | throw "empty response head"
  if lines.any (·.contains '\n') || lines.any (·.contains '\r') then
    throw "response head with a bare line feed or carriage return"
  let parts := statusLine.splitOn " "
  let status ← match parts with
    | v :: code :: _ =>
      unless v == "HTTP/1.1" || v == "HTTP/1.0" do throw "not an HTTP/1.x response"
      unless code.length == 3 && code.all Char.isDigit do throw "malformed status code"
      pure (code.toNat?.getD 0)
    | _ => throw "malformed status line"
  let mut hs : Array (String × String) := #[]
  for l in lines.tail do
    if l.startsWith " " || l.startsWith "\t" then throw "obsolete header line folding"
    match l.splitOn ":" with
    | name :: rest =>
      if name.isEmpty || !name.all tokenChar then throw "malformed header name"
      hs := hs.push (name.toLower, (":".intercalate rest).trimAscii.toString)
    | [] => throw "malformed header line"
  return (status, hs)

/-- The body framing of a response with `status` and `headers`. -/
def framingOf (status : Nat) (hs : Array (String × String)) : Except String Framing := do
  if status < 200 then throw s!"unexpected informational status {status}"
  if status == 204 || status == 304 then return .length 0
  let tes := hs.filter (·.1 == "transfer-encoding")
  if !tes.isEmpty then
    if tes.size == 1 && (tes.map (·.2.toLower)) == #["chunked"] then return .chunked
    throw "unsupported transfer coding"
  let cls := hs.filter (·.1 == "content-length")
  match cls[0]? with
  | none => return .close
  | some (_, v) =>
    unless cls.all (·.2 == v) do throw "conflicting Content-Length headers"
    unless !v.isEmpty && v.length ≤ 15 && v.all Char.isDigit do
      throw "malformed Content-Length"
    return .length (v.toNat?.getD 0)

#guard (framingOf 200 #[("content-length", "12")]).toOption = some (.length 12)
#guard (framingOf 200 #[("content-length", "12"), ("content-length", "12")]).toOption = some (.length 12)
#guard (framingOf 200 #[("content-length", "12"), ("content-length", "13")]).toOption = none
#guard (framingOf 200 #[("content-length", "-1")]).toOption = none
#guard (framingOf 200 #[("content-length", "1 2")]).toOption = none
#guard (framingOf 200 #[("transfer-encoding", "Chunked"), ("content-length", "5")]).toOption = some .chunked
#guard (framingOf 200 #[("transfer-encoding", "gzip, chunked")]).toOption = none
#guard (framingOf 200 #[]).toOption = some .close
#guard (framingOf 204 #[]).toOption = some (.length 0)
#guard (framingOf 100 #[]).toOption = none

/-- Index of the first CR LF at or after `i`. -/
def findCrlf (b : ByteArray) (i : Nat) : Option Nat :=
  if h : i + 1 < b.size then
    if b[i] == 13 && b[i+1] == 10 then some i else findCrlf b (i + 1)
  else none
termination_by b.size - i

/-- A hex digit's value. -/
def hexVal (b : UInt8) : Option Nat :=
  if 48 ≤ b && b ≤ 57 then some (b.toNat - 48)
  else if 97 ≤ b && b ≤ 102 then some (b.toNat - 87)
  else if 65 ≤ b && b ≤ 70 then some (b.toNat - 55)
  else none

/-- The chunk size at the start of a chunk-size line (hex digits, then an optional
`;extension`); at most 15 digits. -/
def chunkSize? (line : ByteArray) : Option Nat := do
  let digits := line.data.toList.takeWhile (fun b => (hexVal b).isSome)
  if digits.isEmpty || digits.length > 15 then none
  let rest := line.data.toList.drop digits.length
  unless rest.isEmpty || rest.head? == some 59 || rest.head? == some 32 ||
    rest.head? == some 9 do none
  digits.foldlM (fun n b => (hexVal b).map (16 * n + ·)) 0

/-- Result of decoding a chunked body. -/
inductive Chunked where
  /-- The whole body, and the index just after the last trailer line. -/
  | done (body : ByteArray) (next : Nat)
  /-- More bytes are needed. -/
  | partial'
  deriving Inhabited

/-- Decodes a `chunked` body starting at `i` (RFC 9112 §7.1): chunks until the zero-size
chunk, then trailer lines (ignored) until an empty line. At most `maxBody` decoded bytes.
`fuel` bounds the number of chunks and trailer lines (each consumes at least two bytes, so
`b.size` is enough). -/
def decodeChunked (b : ByteArray) (i : Nat) (maxBody : Nat) (acc : ByteArray := .empty)
    (fuel : Nat := b.size + 1) : Except String Chunked :=
  match fuel with
  | 0 => .error "malformed chunked body"
  | fuel + 1 =>
    match findCrlf b i with
    | none => .ok .partial'
    | some e =>
      match chunkSize? (b.extract i e) with
      | none => .error "malformed chunk size"
      | some 0 => trailers (e + 2) fuel
      | some n =>
        if acc.size + n > maxBody then .error "response body too large"
        else if e + 2 + n + 2 > b.size then .ok .partial'
        else if b[e + 2 + n]? != some 13 || b[e + 3 + n]? != some 10 then
          .error "chunk not followed by CR LF"
        else decodeChunked b (e + 4 + n) maxBody (acc ++ b.extract (e + 2) (e + 2 + n)) fuel
where
  /-- Skips trailer lines from `j` up to the empty line. -/
  trailers (j : Nat) (fuel : Nat) : Except String Chunked :=
    match fuel with
    | 0 => .error "malformed chunked trailer"
    | fuel + 1 =>
      match findCrlf b j with
      | none => .ok .partial'
      | some e => if e == j then .ok (.done acc (j + 2)) else trailers (e + 2) fuel

/-- What `parseResponse` found. -/
inductive Parsed where
  /-- A complete response. -/
  | done (r : Response)
  /-- More bytes are needed. -/
  | more
  deriving Inhabited

/-- Parses the bytes received so far. `eof`: the server closed the connection (then a
response that is still incomplete is an error, and a `close`-framed body ends here). -/
def parseResponse (b : ByteArray) (eof : Bool) (lim : Limits := {}) : Except String Parsed := do
  let some hEnd := findHeaderEnd b
    | if b.size > lim.maxHeaderBytes then throw "response head too large"
      if eof then throw "connection closed before the response head ended"
      return .more
  if hEnd > lim.maxHeaderBytes then throw "response head too large"
  let (status, hs) ← parseHead (b.extract 0 (hEnd - 2))
  match ← framingOf status hs with
  | .length n =>
    if n > lim.maxBodyBytes then throw "response body too large"
    if b.size ≥ hEnd + n then return .done ⟨status, hs, b.extract hEnd (hEnd + n)⟩
    if eof then throw "connection closed before the response body ended"
    return .more
  | .chunked =>
    match ← decodeChunked b hEnd lim.maxBodyBytes with
    | .done body _ => return .done ⟨status, hs, body⟩
    | .partial' =>
      if eof then throw "connection closed inside a chunked body"
      return .more
  | .close =>
    if b.size - hEnd > lim.maxBodyBytes then throw "response body too large"
    if eof then return .done ⟨status, hs, b.extract hEnd b.size⟩
    return .more

/-- `parseResponse` summarised for the `#guard`s: status and body text, `"more"`, or the
error. -/
def summary (s : String) (eof : Bool) (lim : Limits := {}) : String :=
  match parseResponse s.toUTF8 eof lim with
  | .ok (.done r) => s!"{r.status} {String.fromUTF8? r.body |>.getD "<binary>"}"
  | .ok .more => "more"
  | .error e => s!"error: {e}"

#guard summary "HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\nhello" false = "200 hello"
#guard summary "HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\nhelloEXTRA" false = "200 hello"
#guard summary "HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\nhel" false = "more"
#guard summary "HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\nhel" true =
  "error: connection closed before the response body ended"
#guard summary "HTTP/1.1 401 Unauthorized\r\ncontent-length: 2\r\n\r\n{}" false = "401 {}"
#guard summary "HTTP/1.1 200 OK\r\nContent-Length: 5\r\n" false = "more"
#guard summary "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n6;x=1\r\n world\r\n0\r\n\r\n" false =
  "200 hello world"
#guard summary "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\na\r\n0123456789\r\n0\r\nX-T: 1\r\n\r\n" false =
  "200 0123456789"
#guard summary "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n" false = "more"
#guard summary "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhelloXX0\r\n\r\n" false =
  "error: chunk not followed by CR LF"
#guard summary "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\nzz\r\n" false =
  "error: malformed chunk size"
#guard summary "HTTP/1.1 200 OK\r\n\r\nuntil close" false = "more"
#guard summary "HTTP/1.1 200 OK\r\n\r\nuntil close" true = "200 until close"
#guard summary "HTTP/1.1 200 OK\r\nContent-Length: 50\r\n\r\n" false { maxBodyBytes := 10 } =
  "error: response body too large"
#guard summary "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n20\r\n" false { maxBodyBytes := 10 } =
  "error: response body too large"
#guard summary "HTTP/1.1 200 OK\r\nX: 1\r\n folded\r\n\r\n" false = "error: obsolete header line folding"
#guard summary "HTTP/1.1 200 OK\nContent-Length: 0\r\n\r\n" false =
  "error: response head with a bare line feed or carriage return"
#guard summary "HTTP/1.1 100 Continue\r\n\r\n" false = "error: unexpected informational status 100"
#guard summary "SMTP 220 hi\r\n\r\n" false = "error: not an HTTP/1.x response"
#guard summary "HTTP/1.1 2000 OK\r\n\r\n" false = "error: malformed status code"
#guard summary "HTTP/1.1 200 OK\r\nBad Name: x\r\n\r\n" false = "error: malformed header name"
#guard summary "HTTP/1.1 200" true = "error: connection closed before the response head ended"
#guard summary ("HTTP/1.1 200 OK\r\nX: " ++ String.ofList (List.replicate 100 'a')) false
  { maxHeaderBytes := 50 } = "error: response head too large"

/-- Whether parsing the bytes received so far can finish: always, except for a `chunked`
body whose bytes do not yet end in CR LF CR LF (the end of the last chunk or trailer). Keeps
`exchange` from decoding a long chunked body again after every read. -/
def worthParsing (b : ByteArray) (eof : Bool) : Bool :=
  eof ||
  match findHeaderEnd b with
  | none => true
  | some hEnd =>
    match parseHead (b.extract 0 (hEnd - 2)) >>= fun (st, hs) => framingOf st hs with
    | .ok .chunked =>
      b.size ≥ 4 && b[b.size - 4]? == some 13 && b[b.size - 3]? == some 10 &&
        b[b.size - 2]? == some 13 && b[b.size - 1]? == some 10
    | _ => true

#guard worthParsing "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhel".toUTF8 false = false
#guard worthParsing "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n0\r\n\r\n".toUTF8 false
#guard worthParsing "HTTP/1.1 200 OK\r\nContent-Length: 9\r\n\r\nab".toUTF8 false

/-! ## JSON answers

A small JSON reader for the server's answers (RFC 8259), so the viewer does not link Lean's
`Lean.Data.Json` (which pulls the whole `Lean` library into the executable: 14 MB → 144 MB).
Total: every recursive call consumes `fuel`, which starts at the input size plus one, and
nesting is limited to `maxDepth`. Numbers are kept as their text. -/

/-- A JSON value. -/
inductive JVal where
  /-- `null`. -/
  | null
  /-- `true` / `false`. -/
  | bool (b : Bool)
  /-- A number, as written. -/
  | num (text : String)
  /-- A string. -/
  | str (s : String)
  /-- An array. -/
  | arr (xs : Array JVal)
  /-- An object (members in order; the first of duplicated names wins in `get?`). -/
  | obj (kvs : Array (String × JVal))
  deriving Inhabited

/-- Member `k` of an object. -/
def JVal.get? : JVal → String → Option JVal
  | .obj kvs, k => (kvs.find? (·.1 == k)).map (·.2)
  | _, _ => none

/-- The string, if it is one. -/
def JVal.str? : JVal → Option String
  | .str s => some s
  | _ => none

/-- Deepest nesting accepted. -/
def maxDepth : Nat := 64

/-- JSON whitespace. -/
def isWs (c : UInt8) : Bool := c == 32 || c == 9 || c == 10 || c == 13

/-- The first non-whitespace index at or after `i`. -/
def skipWs (b : ByteArray) (i : Nat) : Nat :=
  if h : i < b.size then (if isWs b[i] then skipWs b (i + 1) else i) else i
termination_by b.size - i

/-- Four hex digits at `i`. -/
def hex4 (b : ByteArray) (i : Nat) : Option Nat := do
  let d (k : Nat) : Option Nat := b[i + k]? >>= hexVal
  return (((← d 0) * 16 + (← d 1)) * 16 + (← d 2)) * 16 + (← d 3)

/-- The UTF-8 bytes of a code point (`U+FFFD` for a surrogate or out-of-range value). -/
def utf8Of (n : Nat) : ByteArray :=
  (String.singleton (if (0xD800 ≤ n && n < 0xE000) || n > 0x10FFFF then '\uFFFD'
    else Char.ofNat n)).toUTF8

/-- A string body from `i` (just after the opening quote) to the closing quote; returns the
string and the index after the quote. -/
def jString (b : ByteArray) (i : Nat) (acc : ByteArray := .empty) (fuel : Nat := b.size + 1) :
    Except String (String × Nat) :=
  match fuel with
  | 0 => .error "JSON string too long"
  | fuel + 1 =>
    match b[i]? with
    | none => .error "unterminated JSON string"
    | some 34 =>
      match String.fromUTF8? acc with
      | some s => .ok (s, i + 1)
      | none => .error "JSON string is not UTF-8"
    | some 92 =>
      match b[i + 1]? with
      | some 34 => jString b (i + 2) (acc.push 34) fuel
      | some 92 => jString b (i + 2) (acc.push 92) fuel
      | some 47 => jString b (i + 2) (acc.push 47) fuel
      | some 98 => jString b (i + 2) (acc.push 8) fuel
      | some 102 => jString b (i + 2) (acc.push 12) fuel
      | some 110 => jString b (i + 2) (acc.push 10) fuel
      | some 114 => jString b (i + 2) (acc.push 13) fuel
      | some 116 => jString b (i + 2) (acc.push 9) fuel
      | some 117 =>
        match hex4 b (i + 2) with
        | none => .error "malformed \\u escape"
        | some hi =>
          if 0xD800 ≤ hi && hi < 0xDC00 && b[i + 6]? == some 92 && b[i + 7]? == some 117 then
            match hex4 b (i + 8) with
            | some lo =>
              if 0xDC00 ≤ lo && lo < 0xE000 then
                jString b (i + 12)
                  (acc ++ utf8Of (0x10000 + (hi - 0xD800) * 0x400 + (lo - 0xDC00))) fuel
              else jString b (i + 6) (acc ++ utf8Of hi) fuel
            | none => .error "malformed \\u escape"
          else jString b (i + 6) (acc ++ utf8Of hi) fuel
      | _ => .error "malformed JSON escape"
    | some c =>
      if c < 32 then .error "control character in a JSON string"
      else jString b (i + 1) (acc.push c) fuel

/-- Whether `b` holds the ASCII text `w` at `i`. -/
def hasAt (b : ByteArray) (i : Nat) (w : String) : Bool :=
  b.extract i (i + w.utf8ByteSize) == w.toUTF8

/-- A number character (`-+.eE` and digits). -/
def numChar (c : UInt8) : Bool := (48 ≤ c && c ≤ 57) || c == 45 || c == 43 || c == 46 ||
  c == 101 || c == 69

/-- The end of the run of `numChar`s from `i`. -/
def numEnd (b : ByteArray) (i : Nat) : Nat :=
  if h : i < b.size then (if numChar b[i] then numEnd b (i + 1) else i) else i
termination_by b.size - i

mutual
/-- A value at `i` (after whitespace); returns it and the index after it. -/
def jValue (b : ByteArray) (i depth : Nat) : Nat → Except String (JVal × Nat)
  | 0 => .error "JSON input too complex"
  | fuel + 1 =>
    let i := skipWs b i
    match b[i]? with
    | none => .error "unexpected end of JSON"
    | some 123 =>
      if depth ≥ maxDepth then .error "JSON nested too deeply"
      else
        let j := skipWs b (i + 1)
        if b[j]? == some 125 then .ok (.obj #[], j + 1) else jMembers b j depth #[] fuel
    | some 91 =>
      if depth ≥ maxDepth then .error "JSON nested too deeply"
      else
        let j := skipWs b (i + 1)
        if b[j]? == some 93 then .ok (.arr #[], j + 1) else jItems b j depth #[] fuel
    | some 34 => (jString b (i + 1)).map fun (s, j) => (.str s, j)
    | some c =>
      if hasAt b i "true" then .ok (.bool true, i + 4)
      else if hasAt b i "false" then .ok (.bool false, i + 5)
      else if hasAt b i "null" then .ok (.null, i + 4)
      else if numChar c then
        let j := numEnd b i
        match String.fromUTF8? (b.extract i j) with
        | some t => .ok (.num t, j)
        | none => .error "malformed JSON number"
      else .error "unexpected character in JSON"
termination_by structural fuel => fuel

/-- Array items from `i` (at an item). -/
def jItems (b : ByteArray) (i depth : Nat) (acc : Array JVal) : Nat → Except String (JVal × Nat)
  | 0 => .error "JSON input too complex"
  | fuel + 1 => do
    let (v, j) ← jValue b i (depth + 1) fuel
    let j := skipWs b j
    match b[j]? with
    | some 44 => jItems b (j + 1) depth (acc.push v) fuel
    | some 93 => return (.arr (acc.push v), j + 1)
    | _ => throw "expected , or ] in a JSON array"
termination_by structural fuel => fuel

/-- Object members from `i` (at a member's name). -/
def jMembers (b : ByteArray) (i depth : Nat) (acc : Array (String × JVal)) :
    Nat → Except String (JVal × Nat)
  | 0 => .error "JSON input too complex"
  | fuel + 1 => do
    let i := skipWs b i
    unless b[i]? == some 34 do throw "expected a member name in a JSON object"
    let (k, j) ← jString b (i + 1)
    let j := skipWs b j
    unless b[j]? == some 58 do throw "expected : in a JSON object"
    let (v, j) ← jValue b (j + 1) (depth + 1) fuel
    let j := skipWs b j
    match b[j]? with
    | some 44 => jMembers b (j + 1) depth (acc.push (k, v)) fuel
    | some 125 => return (.obj (acc.push (k, v)), j + 1)
    | _ => throw "expected , or } in a JSON object"
termination_by structural fuel => fuel
end

/-- Parses a whole JSON text (nothing but whitespace may follow the value). -/
def parseJson (b : ByteArray) : Except String JVal := do
  let (v, j) ← jValue b 0 0 (b.size + 1)
  if skipWs b j == b.size then return v else throw "trailing bytes after JSON"

/-- `parseJson` of a string, then the string at path `ks` (for the `#guard`s). -/
def jPath (s : String) (ks : List String) : Option String := do
  let v ← (parseJson s.toUTF8).toOption
  (← ks.foldlM (fun v k => v.get? k) v).str?

#guard jPath "{\"a\": {\"b\": \"x\\u00e9\\ud83d\\ude00\\n\"}}" ["a", "b"] = some "xé😀\n"
#guard jPath " {\"a\":[1,2.5e3,-0,true,false,null,{}],\"b\":\"\\\"\\\\\\/\"} " ["b"] = some "\"\\/"
#guard jPath "{\"a\":\"x\"} x" ["a"] = none
#guard jPath "{\"a\":\"x\",}" ["a"] = none
#guard jPath "{\"a\":\"\u0001\"}" ["a"] = none
#guard jPath "{\"a\":\"\\ud800\"}" ["a"] = some "\uFFFD"
#guard jPath "{\"a\":\"x\",\"a\":\"y\"}" ["a"] = some "x"
#guard jPath (String.join (List.replicate 100 "[") ++ String.join (List.replicate 100 "]")) [] = none
#guard jPath "[" [] = none
#guard jPath "" [] = none

/-! ## The exchange (IO) -/

open Std.Async in
/-- One request/response over a fresh connection to `127.0.0.1:o.port`. Reads until
`parseResponse` has a complete answer or the server closes; the whole exchange is bounded by
`lim.timeoutMs`. Throws (with the method and path only) on connection errors, a malformed or
oversized answer, or the time limit. -/
def exchange (o : Origin) (tok : Token) (method path : String)
    (body : Option (ByteArray × String) := none) (lim : Limits := {}) : IO Response := do
  let some req := requestBytes o tok method path body
    | throw (IO.userError s!"invalid request {method} {path}")
  let what := s!"{method} {path}"
  let act : Async (Except String Response) := do
    let c ← TCP.Socket.Client.mk
    c.connect o.address
    c.send req
    let mut buf := ByteArray.empty
    let mut res : Except String Response := .error "no response"
    -- At most one iteration per received byte (each `recv?` returns at least one byte or
    -- `none` at the end of the connection), so the loop is bounded by the size limits.
    for _ in [0:lim.maxHeaderBytes + 2 * lim.maxBodyBytes + 2] do
      let chunk ← c.recv? 65536
      let eof := chunk.isNone
      if let some ch := chunk then buf := buf ++ ch
      unless worthParsing buf eof do continue
      match parseResponse buf eof lim with
      | .ok (.done r) => res := .ok r; break
      | .ok .more =>
        if eof then res := .error "incomplete response"; break
      | .error e => res := .error e; break
    try c.shutdown catch _ => pure ()
    return res
  let timeout : Async (Except String Response) := do
    sleep (Std.Time.Millisecond.Offset.ofNat lim.timeoutMs)
    return .error s!"no complete answer within {lim.timeoutMs} ms"
  let r ← try Async.block (Async.race act timeout)
    catch e => throw (IO.userError s!"{what}: cannot reach the library's server on port {o.port}: {e}")
  match r with
  | .ok resp => return resp
  | .error e => throw (IO.userError s!"{what}: {e}")

end SafePdf.Shell.App.BibLean.Http
