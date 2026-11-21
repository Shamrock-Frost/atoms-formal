import Mathlib.Order.Basic

namespace Prod

variable {α β : Type*} [LE α] [LE β] [DecidableLE α] [DecidableLE β]

instance decidableLE : DecidableLE (α × β) := fun a b =>
  inferInstanceAs (Decidable (a.1 ≤ b.1 ∧ a.2 ≤ b.2))

end Prod
