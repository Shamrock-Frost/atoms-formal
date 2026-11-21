import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

universe u

namespace SSet

open CategoryTheory Opposite Simplicial

def asSmall : SSet.{u} ⥤ ((AsSmall.{u} SimplexCategory)ᵒᵖ ⥤ Type u) :=
  (Functor.whiskeringLeft (AsSmall.{u} SimplexCategory)ᵒᵖ SimplexCategoryᵒᵖ (Type u)).obj
    AsSmall.down.op

def asSmallEquivalence : SSet.{u} ≌ ((AsSmall.{u} SimplexCategory)ᵒᵖ ⥤ Type u) :=
  (AsSmall.equiv : SimplexCategory ≌ AsSmall.{u} SimplexCategory).op.congrLeft

instance : asSmall.{u}.IsEquivalence :=
  asSmallEquivalence.isEquivalence_functor

def asSmallStdSimplexIso (a : AsSmall.{u} SimplexCategory) :
    asSmall.obj Δ[(ULift.down a).len] ≅ yoneda.obj a :=
  NatIso.ofComponents
    (fun b => ({
      toFun := fun x => ⟨x.down⟩
      invFun := fun x => ⟨x.down⟩
      left_inv := fun x => by cases x; rfl
      right_inv := fun x => by cases x; rfl
    } : _ ≃ _).toIso)
    (by
      intro b c f
      ext x
      rfl)

end SSet
