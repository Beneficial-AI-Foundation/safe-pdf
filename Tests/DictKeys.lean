import SafePdf

/-!
# Duplicate-key check without the quadratic (task 13.2)

`ObjParse.parseDict` and `Content.Ops.inlineDict` test each key against an ordered key set
(`ObjParse.KeySet`, a `Std.TreeSet`) that mirrors the accumulator (`SeenOf`); `hasKey` stays
the specification. Checks:

* a dictionary of 40000 distinct keys parses, in order, within a generous time bound (the
  quadratic scan took 15 s);
* a repeated key is rejected, at the repeated key's offset (as before the change);
* the same two facts for the dictionary of an inline image in a content stream, and for the
  abbreviation expansion that follows it.
-/

namespace SafePdf.Tests.DictKeys

open SafePdf SafePdf.Core

/-- Reports a failed check; 1 on failure. -/
def check (what : String) (ok : Bool) : IO Nat := do
  if ok then return 0
  IO.println s!"  FAIL dict-keys: {what}"
  return 1

/-- `/K0 0 /K1 1 …` with `n` distinct keys. -/
def entries (n : Nat) : String :=
  String.intercalate " " ((List.range n).map fun i => s!"/K{i} {i}")

def run : IO Nat := do
  let mut f := 0
  let n := 40000
  let lim : Limits := {}
  -- Object parser.
  let src := s!"<< {entries n} >>".toUTF8
  let t0 ← IO.monoMsNow
  let r := ObjParse.parseObject lim src 0
  let t1 ← IO.monoMsNow
  match r with
  | .ok (.dict d, _) =>
    f := f + (← check "object: key count" (d.length == n))
    f := f + (← check "object: source order"
      (d.map (·.1) == (List.range n).map fun i => Name.ofString s!"K{i}"))
  | _ => f := f + (← check "object: parses" false)
  f := f + (← check s!"object: 40000 keys in under 3 s ({t1 - t0} ms)" (t1 - t0 < 3000))
  let pre := s!"<< {entries n} "
  let dup := (pre ++ "/K7 1 >>").toUTF8
  match ObjParse.parseObject lim dup 0 with
  | .error (.malformed off _) =>
    f := f + (← check "object: duplicate at the repeated key" (off == pre.utf8ByteSize))
  | _ => f := f + (← check "object: duplicate rejected" false)
  -- Inline image dictionary in a content stream.
  let cs := s!"q BI /W 1 /H 1 /BPC 8 /CS /G {entries n} ID \x00 EI Q".toUTF8
  let t2 ← IO.monoMsNow
  let tr := Content.Ops.tokenize lim cs
  let t3 ← IO.monoMsNow
  f := f + (← check "inline: no warnings" (tr.warnings == 0))
  match tr.ops.find? (·.op == Content.Ops.kwBI) with
  | some op =>
    match op.operands with
    | [.dict d] => f := f + (← check "inline: key count" (d.length == n + 4))
    | _ => f := f + (← check "inline: one dict operand" false)
  | none => f := f + (← check "inline: BI emitted" false)
  f := f + (← check s!"inline: 40000 keys in under 3 s ({t3 - t2} ms)" (t3 - t2 < 3000))
  let csDup := s!"q BI /W 1 /H 1 {entries n} /K3 1 ID \x00 EI Q".toUTF8
  let trd := Content.Ops.tokenize lim csDup
  f := f + (← check "inline: duplicate warns" (trd.warnings > 0))
  f := f + (← check "inline: duplicate emits no BI"
    ((trd.ops.find? (·.op == Content.Ops.kwBI)).isNone))
  return f

end SafePdf.Tests.DictKeys
