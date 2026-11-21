import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Cover

section UpperBound

variable {α : Type*} [PartialOrder α] {a b w z : α}

theorem CovBy.eq_of_le_of_le (ha : a ⋖ z) (hb : b ⋖ z) (hab : a ≠ b) (haw : a ≤ w)
    (hbw : b ≤ w) (hwz : w ≤ z) : w = z := by
  rcases ha.eq_or_eq haw hwz with rfl | h
  · exact (hb.2 (lt_of_le_of_ne hbw hab.symm) ha.lt).elim
  · exact h

end UpperBound

variable {α : Type*} [Preorder α] [Fintype α] [DecidableLE α]

instance decidableCovByOfFintype : DecidableRel (α := α) (· ⋖ ·) := fun a b =>
  haveI := decidableLTOfDecidableLE (α := α)
  decidable_of_iff (a < b ∧ ∀ c, a < c → ¬ c < b)
    ⟨fun h => ⟨h.1, fun _ hc => h.2 _ hc⟩, fun h => ⟨h.1, fun _ hc => h.2 hc⟩⟩
