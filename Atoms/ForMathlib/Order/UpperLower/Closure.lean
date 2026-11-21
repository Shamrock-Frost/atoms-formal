import Mathlib.Data.Fintype.Basic
import Mathlib.Order.UpperLower.Closure

namespace LowerSet

variable {α : Type*} [Preorder α]

instance decidableMemLowerClosure [Fintype α] [DecidableLE α] (s : Set α) [DecidablePred (· ∈ s)] :
    DecidablePred (· ∈ lowerClosure s) := fun y =>
  decidable_of_iff (∃ x, x ∈ s ∧ y ≤ x) (by simp)

instance decidableMemMk (s : Set α) (hs : IsLowerSet s) [DecidablePred (· ∈ s)] :
    DecidablePred (· ∈ (⟨s, hs⟩ : LowerSet α)) := fun x =>
  inferInstanceAs (Decidable (x ∈ s))

instance decidableMemCoe (s : LowerSet α) [DecidablePred (· ∈ s)] :
    DecidablePred (· ∈ (s : Set α)) := fun x =>
  inferInstanceAs (Decidable (x ∈ s))

instance decidableMemTop : DecidablePred (· ∈ (⊤ : LowerSet α)) := fun _ =>
  isTrue (mem_top)

instance decidableMemBot : DecidablePred (· ∈ (⊥ : LowerSet α)) := fun _ =>
  isFalse (notMem_bot)

instance decidableMemSup (s t : LowerSet α) [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)] :
    DecidablePred (· ∈ s ⊔ t) := fun x =>
  decidable_of_iff (x ∈ s ∨ x ∈ t) mem_sup_iff.symm

instance decidableMemInf (s t : LowerSet α) [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)] :
    DecidablePred (· ∈ s ⊓ t) := fun x =>
  decidable_of_iff (x ∈ s ∧ x ∈ t) mem_inf_iff.symm

instance decidableMemIic [DecidableLE α] (a : α) : DecidablePred (· ∈ Iic a) := fun x =>
  decidable_of_iff (x ≤ a) mem_Iic_iff.symm

instance decidableLE [Fintype α] (s t : LowerSet α) [DecidablePred (· ∈ s)]
    [DecidablePred (· ∈ t)] : Decidable (s ≤ t) :=
  decidable_of_iff (∀ x, x ∈ s → x ∈ t) Iff.rfl

instance decidableEq [Fintype α] (s t : LowerSet α) [DecidablePred (· ∈ s)]
    [DecidablePred (· ∈ t)] : Decidable (s = t) :=
  decidable_of_iff (∀ x, x ∈ s ↔ x ∈ t) SetLike.ext_iff.symm

end LowerSet
