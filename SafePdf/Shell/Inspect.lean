import SafePdf.Shell.Views.Common
import SafePdf.Shell.Views.Summary
import SafePdf.Shell.Views.Objects
import SafePdf.Shell.Views.Resolve
import SafePdf.Shell.Views.Xref
import SafePdf.Shell.Views.Streams
import SafePdf.Shell.Views.Pages
import SafePdf.Shell.Views.Svg

/-!
# Inspector (unverified shell, Plan.md §6 MVP / visibility track)

The debug CLI that shows what the parser sees, one view at a time:

    inspect [--json] [--all] [--view NAME] <file>... [view]
    inspect --list-views
    inspect --help

For each file it checks the size against `Limits.maxInputBytes` before reading, reads the
bytes, times `SafePdf.parseWith`, then runs the selected view (default `summary`).

**Adding a view.** Write `SafePdf/Shell/Views/<Name>.lean` defining a `View`, import it here
and append it to `views`. Nothing else changes.

**Exit codes.** 0 ok; 1 parse error; 2 usage or I/O error. With several files the exit code
is the maximum over the files.

**Trailing view argument.** With two or more positional arguments, the last one names a view
when it is not an existing path and contains neither `/` nor `.` (so `inspect a.pdf b.pdf`
inspects two files, and `inspect a.pdf bogus` reports an unknown view). `--view NAME` is
unambiguous.
-/

namespace SafePdf.Shell.Inspect

open SafePdf.Shell

/-- The view registry. Later phases append `objects`, `xref`, `streams`, `pages`, `svg`, ... -/
def views : List View :=
  [ Views.Summary.view, Views.Objects.view, Views.Resolve.view, Views.Xref.xrefView,
    Views.Xref.revisionsView, Views.Xref.repairView, Views.Streams.view, Views.Pages.view,
    Views.Pages.outlineView, Views.Svg.opsView, Views.Svg.svgView ]

/-- The view used when none is named. -/
def defaultView : String := "summary"

/-- Look a view up by name. -/
def findView (name : String) : Option View :=
  views.find? (·.name == name)

/-- Usage text. -/
def usage : String :=
  "usage: inspect [--json] [--all] [--view NAME] <file>... [view]
       inspect --list-views
       inspect --help

Runs a view (default: summary) on each file. Options:
  --json         machine-readable output (one JSON object per file, one line each)
  --all          show superseded definitions too (objects view)
  --view NAME    select a view explicitly
  --list-views   list available views
  --help         show this text
A trailing positional argument names the view when it is not an existing path and
contains no '/' or '.'.
Exit codes: 0 ok, 1 parse error, 2 usage or I/O error (maximum over all files)."

/-- `name  description` lines for every registered view. -/
def viewListing : String :=
  let width := views.foldl (fun w v => max w v.name.length) 0
  "\n".intercalate (views.map fun v => s!"  {v.name}{String.ofList (List.replicate (width - v.name.length + 2) ' ')}{v.description}")

/-- Parsed command line. -/
structure Args where
  json : Bool := false
  all : Bool := false
  help : Bool := false
  listViews : Bool := false
  view : Option String := none
  positionals : List String := []

/-- Parse the command line; `.error msg` on a usage error. -/
def parseArgs : List String → Args → Except String Args
  | [], a => .ok { a with positionals := a.positionals.reverse }
  | "--json" :: rest, a => parseArgs rest { a with json := true }
  | "--all" :: rest, a => parseArgs rest { a with all := true }
  | "--help" :: rest, a => parseArgs rest { a with help := true }
  | "-h" :: rest, a => parseArgs rest { a with help := true }
  | "--list-views" :: rest, a => parseArgs rest { a with listViews := true }
  | "--view" :: name :: rest, a => parseArgs rest { a with view := some name }
  | ["--view"], _ => .error "--view needs a view name"
  | arg :: rest, a =>
    if arg.startsWith "-" && arg != "-" then .error s!"unknown option '{arg}'"
    else parseArgs rest { a with positionals := arg :: a.positionals }

/-- Read at most `cap` bytes from `h` in chunks; stops at end of file. `fuel` bounds the
number of reads. -/
def readCapped (h : IO.FS.Handle) (cap : Nat) : Nat → ByteArray → IO ByteArray
  | 0, acc => pure acc
  | fuel + 1, acc => do
    if acc.size ≥ cap then return acc
    let want := min (1 <<< 20) (cap - acc.size)
    let chunk ← h.read want.toUSize
    if chunk.size == 0 then return acc
    readCapped h cap fuel (acc ++ chunk)

/-- Load one file: check its size, read it, time the parse. `.error msg` on an I/O error. -/
def load (cfg : Config) (path : String) : IO (Except String Input) := do
  try
    let p : System.FilePath := path
    let md ← p.metadata
    if md.type == .dir then return .error "is a directory"
    let size := md.byteSize.toNat
    let maxBytes := cfg.limits.maxInputBytes
    if size > maxBytes then
      return .ok { path, size, bytes := ByteArray.empty,
                   result := .error (.limitExceeded .inputBytes), parseNanos := 0 }
    let h ← IO.FS.Handle.mk p .read
    -- Read one byte past the limit so a file that grew since `metadata` is still caught.
    let cap := maxBytes + 1
    let bytes ← readCapped h cap (cap / (1 <<< 20) + 2) ByteArray.empty
    let t0 ← IO.monoNanosNow
    -- `lazyPure` evaluates the parse when this action runs, between the two clock reads,
    -- so the compiler cannot float the pure call past either of them.
    let result ← IO.lazyPure fun _ => SafePdf.parseWith cfg.limits bytes
    let t1 ← IO.monoNanosNow
    return .ok { path, size := max size bytes.size, bytes, result, parseNanos := t1 - t0 }
  catch e =>
    return .error (toString e)

/-- Run `view` on one file; returns that file's exit code. -/
def runFile (cfg : Config) (view : View) (path : String) : IO UInt32 := do
  match ← load cfg path with
  | .error msg =>
    IO.eprintln s!"inspect: {path}: {msg}"
    return 2
  | .ok input =>
    view.run cfg input
    return match input.result with
      | .ok _ => 0
      | .error _ => 1

/-- Does the last positional argument name a view rather than a file? -/
def isViewArg (arg : String) : IO Bool := do
  if (findView arg).isSome then
    return !(← (arg : System.FilePath).pathExists)
  if arg.any (fun c => c == '/' || c == '.') then return false
  return !(← (arg : System.FilePath).pathExists)

/-- Run the inspector CLI. -/
def run (argv : List String) : IO UInt32 := do
  let args ← match parseArgs argv {} with
    | .ok a => pure a
    | .error msg =>
      IO.eprintln s!"inspect: {msg}\n{usage}"
      return 2
  if args.help then
    IO.println usage
    return 0
  if args.listViews then
    IO.println viewListing
    return 0
  -- Split off a trailing view name.
  let (files, trailing) ← do
    match args.positionals.reverse with
    | last :: init@(_ :: _) =>
      if ← isViewArg last then pure (init.reverse, some last)
      else pure (args.positionals, none)
    | _ => pure (args.positionals, none)
  if files.isEmpty then
    IO.eprintln usage
    return 2
  let viewName ← match args.view, trailing with
    | some v, some t =>
      if v != t then
        IO.eprintln s!"inspect: conflicting views '{v}' and '{t}'"
        return 2
      pure v
    | some v, none => pure v
    | none, some t => pure t
    | none, none => pure defaultView
  let some view := findView viewName
    | IO.eprintln s!"inspect: unknown view '{viewName}'; available views:\n{viewListing}"
      return 2
  let cfg : Config := { json := args.json, all := args.all }
  let mut code : UInt32 := 0
  let mut first := true
  for path in files do
    if !first && !cfg.json then IO.println ""
    first := false
    let c ← runFile cfg view path
    code := max code c
  return code

end SafePdf.Shell.Inspect
