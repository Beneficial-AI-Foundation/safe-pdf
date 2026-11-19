import SafePdf

/-!
# Inspector view interface (unverified shell, Plan.md §6 MVP / visibility track)

Shared types of the inspector: the per-run `Config`, the per-file `Input` handed to every
view, and the `View` record that the registry in `SafePdf.Shell.Inspect` lists. A later phase
adds a view (`objects`, `xref`, `streams`, `pages`, `svg`, ...) by writing one module under
`SafePdf/Shell/Views/` and adding one entry to `Inspect.views`.

Also holds the small rendering helpers views share: readable `Error` text, millisecond
formatting and hand-rolled JSON string escaping (no Lake dependency, no `Lean` import).
-/

namespace SafePdf.Shell

/-- Options that apply to every view in one inspector run. -/
structure Config where
  /-- Emit machine-readable JSON instead of text (views that support it). -/
  json : Bool := false
  /-- Views that deduplicate (e.g. `objects`) show every occurrence instead. -/
  all : Bool := false
  /-- Resource limits passed to the parser. -/
  limits : Limits := Limits.default

/-- Everything the inspector knows about one input file when it runs a view. -/
structure Input where
  /-- The path as given on the command line. -/
  path : String
  /-- File size in bytes, from the file system metadata. -/
  size : Nat
  /-- The file contents. Empty when the file was not read because it exceeds
  `Limits.maxInputBytes`; then `result` is `.error (.limitExceeded .inputBytes)`. -/
  bytes : ByteArray
  /-- Result of `SafePdf.parseWith`. -/
  result : Except Error Document
  /-- Wall-clock time spent in the parser, in nanoseconds. -/
  parseNanos : Nat

/-- An inspector view: a named way of printing one input. -/
structure View where
  /-- Name used on the command line. -/
  name : String
  /-- One-line description for `--list-views`. -/
  description : String
  /-- Print the view for one input. -/
  run : Config → Input → IO Unit

/-- Human-readable name of a resource limit. -/
def renderLimitKind : LimitKind → String
  | .inputBytes => "input size"
  | .decodedStreamBytes => "decoded stream size"
  | .decodedTotalBytes => "total decoded size"
  | .imagePixels => "image pixels"
  | .objectDepth => "object nesting depth"
  | .objects => "object count"
  | .xobjectDepth => "XObject nesting depth"
  | .gstateDepth => "graphics-state nesting depth"
  | .opsPerPage => "operators per page"
  | .revisions => "xref revision count"
  | .filters => "filters per stream"

/-- Human-readable rendering of a core `Error`. -/
def renderError : Error → String
  | .malformed off msg => s!"malformed input at byte {off}: {msg}"
  | .limitExceeded k => s!"resource limit exceeded: {renderLimitKind k}"
  | .unsupported what => s!"unsupported: {what}"
  | .cycle off what => s!"reference cycle at byte {off}: {what}"
  | .encryption what => s!"encryption: {what}"

/-- Left-pad `s` with `c` to at least `n` characters. -/
def padLeft (n : Nat) (c : Char) (s : String) : String :=
  String.ofList (List.replicate (n - s.length) c) ++ s

/-- Format nanoseconds as milliseconds with three decimals, e.g. `0.012`. -/
def formatMs (nanos : Nat) : String :=
  s!"{nanos / 1000000}.{padLeft 3 '0' (toString ((nanos / 1000) % 1000))}"

/-- Lowercase hex digit. -/
def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- Escape one character for a JSON string literal. -/
def jsonEscapeChar (c : Char) : String :=
  match c with
  | '"' => "\\\""
  | '\\' => "\\\\"
  | '\n' => "\\n"
  | '\r' => "\\r"
  | '\t' => "\\t"
  | c =>
    if c.toNat < 0x20 then
      "\\u00" ++ (hexDigit (c.toNat / 16)).toString ++ (hexDigit (c.toNat % 16)).toString
    else c.toString

/-- A JSON string literal (with quotes) for `s`. -/
def jsonString (s : String) : String :=
  "\"" ++ String.join (s.toList.map jsonEscapeChar) ++ "\""

/-- A single-line JSON object from already-rendered `(key, value)` pairs. -/
def jsonObject (fields : List (String × String)) : String :=
  "{" ++ ", ".intercalate (fields.map fun (k, v) => jsonString k ++ ": " ++ v) ++ "}"

end SafePdf.Shell
