import Mathlib.Order.Lattice

namespace Bool

theorem xor_xor_cancel_left (a b : Bool) : xor a (xor a b) = b := by
  cases a <;> cases b <;> rfl

theorem cond_rec_prop {α : Sort*} {p : α → Prop} {a b : α} (c : Bool) (ha : p a) (hb : p b) :
    p (cond c a b) := by
  cases c <;> assumption

theorem cond_sup_cond {α : Type*} [SemilatticeSup α] (c : Bool) (a b : α) :
    cond c a b ⊔ cond c b a = a ⊔ b := by
  cases c
  · exact sup_comm _ _
  · rfl

end Bool

instance Bool.subsingletonSubtypeEqTrueIff {p : Prop} : Subsingleton {b : Bool // b = true ↔ p} :=
  ⟨fun ⟨_, hb⟩ ⟨_, hc⟩ => Subtype.ext (Bool.eq_iff_iff.2 (hb.trans hc.symm))⟩
