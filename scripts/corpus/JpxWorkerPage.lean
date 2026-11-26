import SafePdf.Shell.Worker.Client

/-!
# Source-PDF page comparison (jpeg2000 Plan §9)

The production viewer client sends the original document bytes to the confined worker.
Only the client writes the returned RGBA to disk. Page numbers in the corpus report start at 1.
-/

open SafePdf.Shell.Worker

/-- Render with the default budgets, default layers and no extra rotation or font substitution. -/
def main (args : List String) : IO Unit := do
  let [worker, pdf, pageArg, scaleArg, output] := args
    | throw <| IO.userError "expected worker, PDF, one-based page, scale denominator, RGBA path"
  let some page := pageArg.toNat? | throw <| IO.userError "invalid page"
  let some denom := scaleArg.toNat? | throw <| IO.userError "invalid scale"
  if page == 0 || denom == 0 then throw <| IO.userError "page and scale must be positive"
  let client ← spawn worker {} #[] { noSubst := true }
  try
    let bytes ← IO.FS.readBinFile pdf
    let pages ← match ← client.request (.openDoc bytes false) (some 60000) with
      | .ok (.docInfo n ..) => pure n
      | .ok (.error _ msg) => throw <| IO.userError msg
      | .error e => throw <| IO.userError (toString e)
      | _ => throw <| IO.userError "unexpected openDoc response"
    if page > pages then throw <| IO.userError s!"page {page} exceeds worker page count {pages}"
    match ← client.request (.render (page - 1) (1 / (denom : Rat)) 0 none) (some 120000) with
    | .ok (.image w h rgba) =>
      unless w > 0 && h > 0 && rgba.size == w * h * 4 do
        throw <| IO.userError "invalid worker image dimensions or buffer"
      IO.FS.writeBinFile output rgba
      IO.println s!"{pages} {w} {h}"
    | .ok (.error _ msg) => throw <| IO.userError msg
    | .error e => throw <| IO.userError (toString e)
    | _ => throw <| IO.userError "unexpected render response"
  finally
    client.close
