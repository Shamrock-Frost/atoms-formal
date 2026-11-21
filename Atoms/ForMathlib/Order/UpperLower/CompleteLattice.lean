import Mathlib.Order.Minimal
import Mathlib.Order.UpperLower.CompleteLattice

namespace LowerSet

variable {α : Type*} [Preorder α] {s t : LowerSet α} {a : α}

theorem maximal_mem_sup_iff :
    Maximal (· ∈ s ⊔ t) a ↔
      (a ∈ s ∨ a ∈ t) ∧ (a ∈ s → Maximal (· ∈ s) a) ∧ (a ∈ t → Maximal (· ∈ t) a) := by
  refine ⟨fun h => ⟨h.prop, fun ha => h.mono (fun _ => Or.inl) ha,
    fun ha => h.mono (fun _ => Or.inr) ha⟩, fun ⟨ha, hs, ht⟩ => ⟨ha, fun b hb hab => ?_⟩⟩
  rcases hb with hb | hb
  · exact (hs (s.lower hab hb)).2 hb hab
  · exact (ht (t.lower hab hb)).2 hb hab

end LowerSet
