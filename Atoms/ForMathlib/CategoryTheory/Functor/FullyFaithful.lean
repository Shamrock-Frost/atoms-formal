import Mathlib.CategoryTheory.EqToHom

namespace CategoryTheory.Functor

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {D : Type u₁} [Category.{v₁} D] {E : Type u₂} [Category.{v₂} E]
  {F : Type u₃} [Category.{v₃} F]

theorem ext_of_comp_faithful (P : E ⥤ F) [P.Faithful] {G₁ G₂ : D ⥤ E}
    (hobj : ∀ d, G₁.obj d = G₂.obj d) (h : G₁ ⋙ P = G₂ ⋙ P) : G₁ = G₂ := by
  refine Functor.ext hobj fun d d' g => ?_
  apply P.map_injective
  simp only [Functor.map_comp, eqToHom_map]
  exact Functor.congr_hom h g

end CategoryTheory.Functor
