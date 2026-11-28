/-! Planted violation for the guard self-test (scripts/test-hygiene.sh). -/
def pureWrapper (n : Nat) : Nat := runST (fun _ => (pure n : ST _ Nat))
