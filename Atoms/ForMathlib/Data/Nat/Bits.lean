import Mathlib.Data.Nat.Bits

namespace Nat

theorem bodd_add_of_eq_add {a b c : ℕ} (h : a = b + c) : (a + b).bodd = c.bodd := by
  rw [h, Nat.bodd_add, Nat.bodd_add, Bool.xor_right_comm, Bool.xor_self, Bool.false_xor]

end Nat
