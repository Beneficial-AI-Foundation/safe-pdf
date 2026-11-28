/-! Planted violation for the guard self-test (scripts/test-hygiene.sh). -/
partial def loop (n : Nat) : Nat := loop (n + 1)
