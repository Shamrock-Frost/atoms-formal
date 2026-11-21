import Mathlib.CategoryTheory.Limits.Shapes.Preorder.TransfiniteCompositionOfShape

universe w v u

namespace CategoryTheory.TransfiniteCompositionOfShape

variable {C : Type u} [Category.{v} C] {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J]
  [WellFoundedLT J] {X Y : C} {f : X ⟶ Y}

theorem map_bot_comp_incl_app (c : TransfiniteCompositionOfShape J f) (j : J) :
    c.F.map (homOfLE bot_le : ⊥ ⟶ j) ≫ c.incl.app j = c.isoBot.hom ≫ f := by
  have := c.incl.naturality (homOfLE bot_le : ⊥ ⟶ j)
  simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at this
  rw [this, ← Category.id_comp (c.incl.app ⊥), ← c.isoBot.hom_inv_id, Category.assoc, c.fac]

end CategoryTheory.TransfiniteCompositionOfShape
