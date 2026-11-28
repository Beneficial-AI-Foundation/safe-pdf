/-! Planted violation for the guard self-test (scripts/test-hygiene.sh). -/
def impl (n : Nat) : Nat := n
@[implemented_by impl] def spec (n : Nat) : Nat := n + 0
