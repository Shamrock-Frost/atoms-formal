import Atoms.ForMathlib.CategoryTheory.Category.Cat.TwistedArrow
import Atoms.TestCategory.BasicLocalizer.Homotopy

open CategoryTheory Limits Opposite

namespace Atoms.TestCategory

universe u

namespace BasicLocalizer

variable (𝒲 : BasicLocalizer.{u})

theorem aspherical_costructuredArrow_twistedArrowTarget (A : Cat.{u, u}) (b : A) :
    𝒲.Aspherical (Cat.of (CostructuredArrow (Cat.twistedArrowTarget A).toFunctor b)) := by
  have : HasInitial (Cat.of (Over b)ᵒᵖ) := (Over.mkIdTerminal (X := b)).op.hasInitial
  exact (𝒲.aspherical_iff_of_W (Cat.twistedArrowTargetSliceCompose A b).toCatHom
    (𝒲.W_of_adjunction (v := (Cat.twistedArrowTargetFibreInclusion A b).toCatHom)
      (Cat.twistedArrowTargetSliceComposeAdjunction A b))).2 (𝒲.aspherical_of_hasInitial _)

theorem W_twistedArrowTarget (A : Cat.{u, u}) : 𝒲.W (Cat.twistedArrowTarget A) :=
  𝒲.W_of_asphericalFunctor fun b => 𝒲.aspherical_costructuredArrow_twistedArrowTarget A b

theorem W_twistedArrowSource (A : Cat.{u, u}) : 𝒲.W (Cat.twistedArrowSource A) :=
  (Cat.twistedArrowOpIso_hom_comp_twistedArrowTarget A) ▸
    𝒲.W.comp_mem _ _ (MorphismProperty.isomorphisms_le_of_containsIdentities 𝒲.W _
      (MorphismProperty.isomorphisms.infer_property _))
      (𝒲.W_twistedArrowTarget _)

theorem W_twistedArrowMap_iff {A B : Cat.{u, u}} (F : A ⟶ B) :
    𝒲.W (Cat.twistedArrowMap F) ↔ 𝒲.W F := by
  rw [← 𝒲.W.postcomp_iff (Cat.twistedArrowMap F) _ (𝒲.W_twistedArrowTarget B),
    Cat.twistedArrowMap_comp_twistedArrowTarget, 𝒲.W.precomp_iff _ F (𝒲.W_twistedArrowTarget A)]

theorem W_opFunctor_map_iff {A B : Cat.{u, u}} (f : A ⟶ B) :
    𝒲.W (Cat.opFunctor.map f) ↔ 𝒲.W f := by
  rw [← 𝒲.W.precomp_iff _ (Cat.opFunctor.map f) (𝒲.W_twistedArrowSource A),
    ← Cat.twistedArrowMap_comp_twistedArrowSource, 𝒲.W.postcomp_iff _ _ (𝒲.W_twistedArrowSource B),
    W_twistedArrowMap_iff]

theorem aspherical_opFunctor_obj_iff (C : Cat.{u, u}) :
    𝒲.Aspherical (Cat.opFunctor.obj C) ↔ 𝒲.Aspherical C := by
  let p : C ⟶ Cat.of (Discrete PUnit.{u + 1}) :=
    ((Functor.const ↥C).obj (⟨⟨⟩⟩ : Cat.of (Discrete PUnit.{u + 1}))).toCatHom
  rw [𝒲.aspherical_iff_W (Cat.opFunctor.map p) (𝒲.terminal_aspherical _),
    𝒲.aspherical_iff_W p (𝒲.terminal_aspherical _), W_opFunctor_map_iff]

theorem W_of_forall_aspherical_structuredArrow {A B : Cat.{u, u}} (f : A ⟶ B)
    (h : ∀ b : B, 𝒲.Aspherical (Cat.of (StructuredArrow b f.toFunctor))) : 𝒲.W f := by
  rw [← W_opFunctor_map_iff]
  refine 𝒲.W_of_asphericalFunctor fun b => ?_
  have hop := (𝒲.aspherical_opFunctor_obj_iff
    (Cat.of (StructuredArrow (unop b) f.toFunctor))).2 (h (unop b))
  exact 𝒲.aspherical_of_equivalence (structuredArrowOpEquivalence f.toFunctor (unop b)) hop

end BasicLocalizer

end Atoms.TestCategory
