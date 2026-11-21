import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Minimal

variable {α : Type*} [LE α] [Fintype α] [DecidableLE α]

instance decidableMaximalOfFintype (p : α → Prop) [DecidablePred p] (x : α) :
    Decidable (Maximal p x) :=
  decidable_of_iff (p x ∧ ∀ y, p y → x ≤ y → y ≤ x) ⟨fun h => ⟨h.1, fun _ hy => h.2 _ hy⟩,
    fun h => ⟨h.1, fun _ hy => h.2 hy⟩⟩
