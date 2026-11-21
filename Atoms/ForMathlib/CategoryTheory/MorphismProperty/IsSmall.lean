import Mathlib.CategoryTheory.MorphismProperty.IsSmall

universe w

namespace CategoryTheory.MorphismProperty

variable {C : Type*} [Category C]

instance isSmall_bot : (⊥ : MorphismProperty C).IsSmall.{w} := by
  have h : (⊥ : MorphismProperty C) =
      ofHoms (X := PEmpty.elim) (Y := PEmpty.elim) fun i : PEmpty.{w + 1} ↦ i.elim := by
    ext _ _ f
    exact ⟨fun hf ↦ hf.elim, fun hf ↦ by cases hf with | mk i => exact i.elim⟩
  rw [h]
  infer_instance

instance isSmall_sup (W W' : MorphismProperty C) [IsSmall.{w} W] [IsSmall.{w} W'] :
    IsSmall.{w} (W ⊔ W') := by
  rw [sup_eq_iSup]
  have (b : Bool) : IsSmall.{w} (cond b W W') := by cases b <;> assumption
  infer_instance

end CategoryTheory.MorphismProperty
