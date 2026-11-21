import Mathlib.Data.Fintype.Defs
import Mathlib.Logic.Relation

namespace Relation

variable {α β : Type*} {rα : α → α → Prop} {rβ : β → β → Prop} {f : α → β}

instance decidableFibration [Fintype α] [Fintype β] [DecidableRel rα] [DecidableRel rβ]
    [DecidableEq β] : Decidable (Fibration rα rβ f) :=
  inferInstanceAs (Decidable (∀ a b, rβ b (f a) → ∃ a', rα a' a ∧ f a' = b))

end Relation
