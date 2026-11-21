import Atoms.TestCategory.Simplicial.Contraction

open CategoryTheory Limits MorphismProperty Simplicial

namespace Atoms.TestCategory

open Homotopical

universe v u

def lastVertexFunctor (C : Cat.{u, u}) :
    (elementsFunctor (AsSmall.{u} SimplexCategory)).obj (SSet.asSmall.obj (nerve C)) ⟶ C :=
  Cat.Hom.ofFunctor (Functor.nerveEvalTerminal (D := AsSmall.down ⋙ SimplexCategory.toCat)
    (fun n => Fin.isTerminalLast (ULift.down n).len) C)

def lastVertexSliceEquivalence (C : Cat.{u, u}) (c : C) :
    CostructuredArrow (lastVertexFunctor C).toFunctor c ≌
      ((SSet.asSmall.obj (nerve (Over c))).Elements)ᵒᵖ :=
  Functor.nerveOverEquivalence (D := AsSmall.down ⋙ SimplexCategory.toCat) C c
    (fun n => Fin.isTerminalLast (ULift.down n).len)

namespace BasicLocalizer

theorem asphericalFunctor_lastVertexFunctor (𝒲 : BasicLocalizer.{u}) (C : Cat.{u, u}) :
    𝒲.AsphericalFunctor (lastVertexFunctor C) := fun c =>
  𝒲.aspherical_of_equivalence (lastVertexSliceEquivalence C c).symm
    (𝒲.pshAspherical_sSetAsSmall_of_contraction (overNerveContraction (A := C) c))

end BasicLocalizer

theorem elementsFunctor_map_nerveMap_comp_lastVertexFunctor {C D : Cat.{u, u}} (F : C ⟶ D) :
    (elementsFunctor (AsSmall.{u} SimplexCategory)).map
        (SSet.asSmall.map (CategoryTheory.nerveFunctor.map F)) ≫ lastVertexFunctor D =
      lastVertexFunctor C ≫ F :=
  Cat.Hom.ext (Functor.nerveEvalTerminal_comp (D := AsSmall.down ⋙ SimplexCategory.toCat)
    (fun n => Fin.isTerminalLast (ULift.down n).len) C F.toFunctor).symm

namespace BasicLocalizer

theorem W_iff_wSSet_nerveMap (𝒲 : BasicLocalizer.{u}) {C D : Cat.{u, u}} (F : C ⟶ D) :
    𝒲.W F ↔ 𝒲.wSSet (CategoryTheory.nerveFunctor.map F) := by
  have hC := 𝒲.W_of_asphericalFunctor (𝒲.asphericalFunctor_lastVertexFunctor C)
  have hD := 𝒲.W_of_asphericalFunctor (𝒲.asphericalFunctor_lastVertexFunctor D)
  have hsq := elementsFunctor_map_nerveMap_comp_lastVertexFunctor F
  change _ ↔ 𝒲.W ((elementsFunctor (AsSmall.{u} SimplexCategory)).map _)
  constructor
  · intro hF
    refine 𝒲.W.of_postcomp _ _ hD ?_
    rw [hsq]
    exact 𝒲.W.comp_mem _ _ hC hF
  · intro hN
    refine 𝒲.W.of_precomp _ _ hC ?_
    rw [← hsq]
    exact 𝒲.W.comp_mem _ _ hN hD

end BasicLocalizer

end Atoms.TestCategory
