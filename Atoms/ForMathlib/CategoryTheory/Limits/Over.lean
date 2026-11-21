import Mathlib.CategoryTheory.Limits.Over

open CategoryTheory Limits

namespace CategoryTheory.Under

instance hasFiniteLimits {C : Type*} [Category* C] [Limits.HasFiniteLimits C] {X : C} :
    Limits.HasFiniteLimits (Under X) :=
  ⟨fun _ _ _ ↦ inferInstance⟩

end CategoryTheory.Under
