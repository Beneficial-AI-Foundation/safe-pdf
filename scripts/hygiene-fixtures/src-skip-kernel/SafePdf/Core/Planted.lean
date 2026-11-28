/-! Planted violation for the guard self-test (scripts/test-hygiene.sh). -/
set_option debug.skipKernelTC true in
theorem t : 2 + 2 = 4 := rfl
