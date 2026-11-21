import Mathlib.CategoryTheory.Monoidal.ExternalProduct.Basic
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

namespace CategoryTheory.MonoidalCategory

open Limits

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {J₁ : Type u₁} {J₂ : Type u₂} {C : Type u₃} {K : Type u₄}
  [Category.{v₁} J₁] [Category.{v₂} J₂] [Category.{v₃} C] [MonoidalCategory C]
  [Category.{v₄} K]

instance preservesColimitsOfShape_externalProductLeft (F : J₁ ⥤ C) [HasColimitsOfShape K C]
    [∀ c : C, PreservesColimitsOfShape K (tensorLeft c)] :
    PreservesColimitsOfShape K
      ((Functor.curry.obj (externalProductBifunctor J₁ J₂ C)).obj F) :=
  preservesColimitsOfShape_of_evaluation _ _ fun j =>
    preservesColimitsOfShape_of_natIso
      (NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => by simp) :
        (evaluation J₂ C).obj j.2 ⋙ tensorLeft (F.obj j.1) ≅
          (Functor.curry.obj (externalProductBifunctor J₁ J₂ C)).obj F ⋙
            (evaluation (J₁ × J₂) C).obj j)

instance preservesColimitsOfShape_externalProductRight (G : J₂ ⥤ C) [HasColimitsOfShape K C]
    [∀ c : C, PreservesColimitsOfShape K (tensorRight c)] :
    PreservesColimitsOfShape K
      ((Functor.curry.obj (externalProductBifunctor J₁ J₂ C)).flip.obj G) :=
  preservesColimitsOfShape_of_evaluation _ _ fun j =>
    preservesColimitsOfShape_of_natIso
      (NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => by simp) :
        (evaluation J₁ C).obj j.1 ⋙ tensorRight (G.obj j.2) ≅
          (Functor.curry.obj (externalProductBifunctor J₁ J₂ C)).flip.obj G ⋙
            (evaluation (J₁ × J₂) C).obj j)

end CategoryTheory.MonoidalCategory
