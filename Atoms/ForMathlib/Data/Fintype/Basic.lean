import Mathlib.Data.Fintype.Basic

namespace Set

variable {α β : Type*} [Fintype α] [DecidableEq β] {f : α → β} {s : Set α} {t : Set β}

omit [DecidableEq β] in
instance decidableMapsTo [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)] :
    Decidable (MapsTo f s t) :=
  inferInstanceAs (Decidable (∀ x, x ∈ s → f x ∈ t))

instance decidableInjOn [DecidableEq α] [DecidablePred (· ∈ s)] : Decidable (InjOn f s) :=
  inferInstanceAs (Decidable (∀ x, x ∈ s → ∀ y, y ∈ s → f x = f y → x = y))

instance decidableSurjOn [Fintype β] [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)] :
    Decidable (SurjOn f s t) :=
  inferInstanceAs (Decidable (∀ y, y ∈ t → ∃ x, x ∈ s ∧ f x = y))

instance decidableBijOn [DecidableEq α] [Fintype β] [DecidablePred (· ∈ s)]
    [DecidablePred (· ∈ t)] : Decidable (BijOn f s t) :=
  inferInstanceAs (Decidable (MapsTo f s t ∧ InjOn f s ∧ SurjOn f s t))

end Set
