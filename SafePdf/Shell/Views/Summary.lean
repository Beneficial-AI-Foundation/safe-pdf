import SafePdf.Shell.Views.Common

/-!
# `summary` view (default)

Path, size, header offset and version, parse result and parse time. The text form keeps the
exact phrase `<N> bytes` on the `size:` line: the differential runner (task 0.7) extracts it.
-/

namespace SafePdf.Shell.Views.Summary

open SafePdf.Shell

/-- `major.minor` of a header version. -/
def renderVersion : Option (Nat × Nat) → String
  | some (major, minor) => s!"{major}.{minor}"
  | none => "unknown"

/-- Text form of the summary. -/
def text (i : Input) : List String :=
  let header :=
    match i.result with
    | .ok d => s!"header:     offset {d.headerOffset}, version {renderVersion d.version}"
    | .error _ => "header:     not found"
  let parse :=
    match i.result with
    | .ok _ => "parse:      ok"
    | .error e => s!"parse:      error: {renderError e}"
  [ s!"file:       {i.path}"
  , s!"size:       {i.size} bytes"
  , header
  , parse
  , s!"parse time: {formatMs i.parseNanos} ms" ]

/-- Single-line JSON form of the summary. -/
def json (i : Input) : String :=
  let (ok, off, ver, err) : String × String × String × String :=
    match i.result with
    | .ok d =>
      let ver := match d.version with
        | some (major, minor) => jsonString s!"{major}.{minor}"
        | none => "null"
      ("true", toString d.headerOffset, ver, "null")
    | .error e => ("false", "null", "null", jsonString (renderError e))
  jsonObject
    [ ("path", jsonString i.path), ("bytes", toString i.size), ("ok", ok),
      ("headerOffset", off), ("version", ver), ("error", err),
      ("parseMs", formatMs i.parseNanos) ]

/-- The `summary` view. -/
def view : View where
  name := "summary"
  description := "path, size, header offset and version, parse result, parse time (default)"
  run cfg i :=
    if cfg.json then IO.println (json i)
    else (text i).forM IO.println

end SafePdf.Shell.Views.Summary
