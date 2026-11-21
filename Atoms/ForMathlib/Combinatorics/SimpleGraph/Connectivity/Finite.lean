import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

namespace Relation

variable {α : Type*} {r : α → α → Prop} [Std.Symm r]

theorem reflTransGen_iff_reachable_fromRel {a b : α} :
    ReflTransGen r a b ↔ (SimpleGraph.fromRel r).Reachable a b := by
  rw [SimpleGraph.reachable_iff_reflTransGen]
  refine ⟨fun h => ?_, ReflTransGen.mono (fun _ _ hab => hab.2.elim id (Std.Symm.symm _ _)) a b⟩
  induction h with
  | refl => exact ReflTransGen.refl
  | @tail b c _ hbc ih =>
    rcases eq_or_ne b c with rfl | hne
    · exact ih
    · exact ih.tail ⟨hne, Or.inl hbc⟩

instance decidableReflTransGen [Fintype α] [DecidableEq α] [DecidableRel r] (a b : α) :
    Decidable (ReflTransGen r a b) :=
  decidable_of_iff _ reflTransGen_iff_reachable_fromRel.symm

end Relation
