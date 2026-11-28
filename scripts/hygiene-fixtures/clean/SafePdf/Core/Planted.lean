/-! Planted violation for the guard self-test (scripts/test-hygiene.sh). -/
namespace Planted
inductive Color where | red | green deriving Repr
structure P where
  x : Nat
  y : Nat
def sumTo (n : Nat) : Nat := if h : n = 0 then 0 else n + sumTo (n - 1)
termination_by n
decreasing_by omega
def getFirst (xs : Array Nat) (h : 0 < xs.size) : Nat := xs[0]'h
theorem sumTo_zero : sumTo 0 = 0 := by simp [sumTo]
end Planted
