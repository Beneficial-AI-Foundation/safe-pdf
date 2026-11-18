import SafePdf
-- Randomized Core-vs-Spec lexer agreement check (orchestrator, wave 6). Run: lake env lean --run scripts/lexdiff.lean
open SafePdf

def alphabet : Array UInt8 := "  \n\r\t%()<>[]{}/#\\0123456789.+-abfnrtAFxRobjtrue7".toUTF8.data

def gen (seed : Nat) (n : Nat) : ByteArray := Id.run do
  let mut s := seed
  let mut b := ByteArray.empty
  for _ in [0:n] do
    s := (s * 6364136223846793005 + 1442695040888963407) % 18446744073709551616
    let k := (s >>> 33) % (alphabet.size + 8)
    b := b.push (if k < alphabet.size then alphabet[k]?.getD 32 else UInt8.ofNat (s >>> 40 % 256))
  return b

def agree (b : ByteArray) (pos : Nat) : Bool :=
  let l := b.data.toList.drop pos
  match Core.Lex.next b pos, Spec.Lex.next l with
  | .ok none, .ok none => true
  | .ok (some (t, p)), .ok (some (t', r)) => t == t' && p == b.size - r.length
  | .error e, .error e' => e.kind == e'.kind && e.offset == e'.offset + pos
  | _, _ => false

def main : IO UInt32 := do
  let mut bad := 0
  let mut total := 0
  for seed in [0:3000] do
    let b := gen seed (1 + seed % 40)
    for pos in [0:b.size] do
      total := total + 1
      unless agree b pos do
        bad := bad + 1
        if bad ≤ 8 then
          IO.println s!"DISAGREE seed={seed} pos={pos} bytes={b.data.toList.drop pos} core={repr (Core.Lex.next b pos)} spec={repr (Spec.Lex.next (b.data.toList.drop pos))}"
  IO.println s!"checked {total} (input,pos) pairs, {bad} disagreements"
  return if bad == 0 then 0 else 1
