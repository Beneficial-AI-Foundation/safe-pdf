import SafePdf.Shell.Views.Common

/-!
# `summary` view (default)

Path, size, header offset and version, parse result and parse time, and how the document
opened (task 2.11): `open: strict|repaired|failed`, xref revisions, object (entry) count,
root reference, encryption. The text form keeps the exact phrase `<N> bytes` on the `size:`
line: the differential runner (task 0.7) extracts it.
-/

namespace SafePdf.Shell.Views.Summary

open SafePdf.Shell

/-- `major.minor` of a header version. -/
def renderVersion : Option (Nat × Nat) → String
  | some (major, minor) => s!"{major}.{minor}"
  | none => "unknown"

/-- How the document opened: `strict`, `repaired` or `failed`. -/
def openMode (r : Except Error Document) : String :=
  match r with
  | .ok d => if d.repaired then "repaired" else "strict"
  | .error _ => "failed"

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
  , s!"open:       {openMode i.result}" ]
  ++ (match i.result with
      | .ok d =>
        [ s!"revisions:  {d.revisions}"
        , s!"objects:    {d.objectCount}"
        , s!"root:       {d.root.1} {d.root.2} R"
        , s!"encrypted:  {d.encrypted}" ]
      | .error _ => [])
  ++ [ s!"parse time: {formatMs i.parseNanos} ms" ]

/-- Single-line JSON form of the summary. -/
def json (i : Input) : String :=
  let (revs, objs, root, enc) : String × String × String × String :=
    match i.result with
    | .ok d => (toString d.revisions, toString d.objectCount,
        jsonString s!"{d.root.1} {d.root.2} R", toString d.encrypted)
    | .error _ => ("null", "null", "null", "null")
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
      ("open", jsonString (openMode i.result)), ("revisions", revs), ("objects", objs),
      ("root", root), ("encrypted", enc),
      ("parseMs", formatMs i.parseNanos) ]

/-- The `summary` view. -/
def view : View where
  name := "summary"
  description := "path, size, header, parse result, open mode (strict/repaired), revisions, objects, root, parse time (default)"
  run cfg i :=
    if cfg.json then IO.println (json i)
    else (text i).forM IO.println

end SafePdf.Shell.Views.Summary
