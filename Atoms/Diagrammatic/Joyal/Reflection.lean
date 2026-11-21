import Atoms.Diagrammatic.Joyal.FaceNerveCylinder
import Atoms.Diagrammatic.Marked.NaturalMarking
import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Cisinski.Quillen

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra Simplicial

universe u

namespace Atoms.Diagrammatic

open Atoms.Homotopical MarkedSSet.modelCategoryCartesian

noncomputable def MarkedDiagSet.Coinductive.markedFaceNerve :
    MarkedDiagSet.Coinductive.{u} 1 ⥤ MarkedSSet :=
  Atoms.Diagrammatic.markedFaceNerve

noncomputable def MarkedDiagSet.Coinductive.markedFaceNerveAdjunction :
    MarkedDiagSet.Coinductive.markedFaceNerve.{u} ⊣
      MarkedPresheaf.nerve markedFaceNerveSite (fun x => epi_markedFaceNerveSite_map_toSelf x) ⋙
        MarkedDiagSet.toCoinductive 1 :=
  Atoms.Diagrammatic.markedFaceNerveAdjunction

private theorem mono_of_reducedGenerators {A B : MarkedDiagSet.{u}} {j : A ⟶ B}
    (hj : (compositorHorns ⊔ invertorHorns ⊔ markingGeneratorsAbove 1 ⊔ invertorGenerators) j) :
    Mono j := by
  refine inductiveGenerators_le_monomorphisms 1 j ?_
  rcases hj with ((hj | hj) | hj) | hj
  · exact Or.inl (Or.inl (compositorHorns_le_markedHorns _ hj))
  · exact Or.inl (Or.inl (invertorHorns_le_markedHorns _ hj))
  · exact Or.inl (Or.inr hj)
  · exact Or.inr hj

theorem isQuillen_markedFaceNerveAdjunction_of_weakEquivalence
    (h : ∀ ⦃A B : MarkedDiagSet.{u}⦄ (j : A ⟶ B),
      (compositorHorns ⊔ invertorHorns ⊔ markingGeneratorsAbove 1 ⊔ invertorGenerators) j →
        WeakEquivalence (markedFaceNerve.map j)) :
    MarkedDiagSet.Coinductive.markedFaceNerveAdjunction.{u}.IsQuillen := by
  refine ExactCylinder.isQuillen_of_map_contraction markedExactCylinder.{u} cartesianCylinder
    (coinductiveGenerators 1) cartesianGenerators
    (markedExactCylinder.{u}.trivialCofibrationsSetGenerated_of_embedding
      (BoundedEmbedding.separated (MarkedSite.topology atomMarking)) (coinductiveGenerators 1)
      (coinductiveGenerators_le_monomorphisms 1))
    (cartesianCylinder.{u}.trivialCofibrationsSetGenerated_of_embedding
      (BoundedEmbedding.separated (MarkedSite.topology edgeMarking)) cartesianGenerators
      cartesianGenerators_le_monomorphisms)
    markedFaceNerveAdjunction
    (fun Y ↦ (weakEquivalence_iff _).1 (weakEquivalence_markedFaceNerve_map_contraction_app Y))
    fun Z hZ ↦ ?_
  have hZ' : IsFibrant Z := (isFibrant_iff_isFibrant Z).2 hZ
  refine (isFibrant_coinductive_iff_isFibrant 1 _).1 ((isFibrant_coinductive_iff 1 _).2 ?_)
  refine hasMarkedRLP_coinductiveGenerators_of_hasMarkedRLP 1 _ ?_
  refine hasMarkedRLP_iff.2 fun A B j hj q ↦ ?_
  have := mono_of_reducedGenerators hj
  have : Cofibration (markedFaceNerve.map j) :=
    (cofibration_iff _).2 (markedFaceNerve.map_mono j)
  have := h j hj
  let q' := (markedFaceNerveAdjunction.homEquiv A Z).symm q
  have sq : CommSq q' (markedFaceNerve.map j) (terminal.from Z) (terminal.from _) :=
    ⟨terminal.hom_ext _ _⟩
  refine ⟨markedFaceNerveAdjunction.homEquiv B Z sq.lift, ?_⟩
  rw [← markedFaceNerveAdjunction.homEquiv_naturality_left, sq.fac_left, Equiv.apply_symm_apply]

end Atoms.Diagrammatic
