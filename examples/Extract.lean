import SafePdf.Api

/-!
# Example client of the library API (task 8.4; Plan.md §6 Phase 8, `docs/api.md`)

`lake exe extract [--render] FILE [PAGE]` opens `FILE` with `SafePdf.Api.openFile` and prints
the page count, the outline titles (indented by depth, with their target page), the links and
annotations of the page, and the page's text with the bounding box of each line. `PAGE` is
1-based and defaults to 1. `--render` also renders the page at 72 dpi and prints the image
size.

This file is unverified client code: it only calls `SafePdf.Api`.
-/

open SafePdf.Api

/-- A rational with three decimals. -/
def fmt (q : Rat) : String :=
  let neg := q < 0
  let a := if neg then -q else q
  let m := (a * 1000 + 1 / 2).floor.toNat
  let frac := toString (m % 1000)
  let frac := String.ofList (List.replicate (3 - frac.length) '0') ++ frac
  (if neg then "-" else "") ++ s!"{m / 1000}.{frac}"

/-- A box as `[llx lly urx ury]`. -/
def fmtBox (b : Box) : String := s!"[{fmt b.llx} {fmt b.lly} {fmt b.urx} {fmt b.ury}]"

/-- A target as text. -/
def fmtTarget : Target → String
  | .none => "-"
  | .page i _ => s!"page {i + 1}"
  | .danglingDest _ => "dangling destination"
  | .unresolved n => s!"unresolved \"{n}\""
  | .uri u => s!"URI {u}"
  | .action k => s!"action {k}"

/-- A rotation in degrees. -/
def degrees : Rotation → Nat
  | .r0 => 0
  | .r90 => 90
  | .r180 => 180
  | .r270 => 270

/-- Print the report for page `pg` (0-based) of `d`. -/
def report (d : Document) (pg : Nat) (render : Bool) : IO Unit := do
  IO.println s!"pages: {d.pageCount}{if d.repaired then " (repaired)" else ""}"
  let ol := outline d
  IO.println s!"outline: {ol.length} item(s)"
  for it in ol do
    IO.println s!"  {String.ofList (List.replicate (2 * it.depth) ' ')}{it.title}  -> {fmtTarget it.target}"
  match pageInfo d pg with
  | .error e => IO.println s!"page {pg + 1}: {e}"
  | .ok info =>
    IO.println s!"page {pg + 1} (label {info.label}): crop box {fmtBox info.cropBox}, rotation {degrees info.rotation}"
    match pageLinks d pg with
    | .ok ls => for l in ls do IO.println s!"  link {fmtBox l.rect} -> {fmtTarget l.target}"
    | .error e => IO.println s!"  links: {e}"
    match pageAnnotations d pg with
    | .ok as =>
      for a in as do
        IO.println s!"  annotation /{a.subtype} {fmtBox a.rect}{(a.contents.map (s!": {·}")).getD ""}"
    | .error e => IO.println s!"  annotations: {e}"
    match pageText d pg with
    | .error e => IO.println s!"  text: {e}"
    | .ok t =>
      IO.println s!"  text: {t.lines.size} line(s), {t.glyphs.size} glyph(s)"
      for l in t.lines do
        IO.println s!"  {fmtBox l.box} {l.text}"
    if render then
      match renderPage d pg 1 with
      | .ok img => IO.println s!"  rendered at 72 dpi: {img.w} x {img.h} RGBA ({img.data.size} bytes)"
      | .error e => IO.println s!"  render: {e}"

/-- Entry point. -/
def main (args : List String) : IO UInt32 := do
  let (render, args) := if args.contains "--render" then (true, args.filter (· != "--render"))
    else (false, args)
  match args with
  | [path] | [path, _] =>
    let pg := match args with
      | [_, p] => (p.toNat?.getD 1) - 1
      | _ => 0
    try
      match ← openFile path with
      | .error e =>
        IO.eprintln s!"extract: {path}: {e}"
        return 1
      | .ok d =>
        report d pg render
        return 0
    catch e =>
      IO.eprintln s!"extract: {path}: {e}"
      return 1
  | _ =>
    IO.eprintln "usage: extract [--render] FILE [PAGE]"
    return 2
