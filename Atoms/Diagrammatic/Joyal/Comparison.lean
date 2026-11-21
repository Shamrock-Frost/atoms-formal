import Atoms.Diagrammatic.Joyal.CoreFiltration
import Atoms.Diagrammatic.Joyal.FaceNerveGenerators
import Atoms.Diagrammatic.Joyal.Quillen
import Atoms.Diagrammatic.Joyal.Reflection

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra Atoms.Shape Atoms.Homotopical

universe u

namespace Atoms.Diagrammatic

theorem weakEquivalence_sSetDiagSetAdj_counit_app (X : DiagSet.Infty.{u} 1) (hX : IsFibrant X) :
    WeakEquivalence (DiagSet.Infty.sSetDiagSetAdj.counit.app X) := by
  have key (Y : DiagSet.{u}) (hC : IsInftyCategory 1 Y) :
      WeakEquivalence ((DiagSet.toInfty 1).map (sSetDiagSetAdj.counit.app Y)) := by
    have hι : WeakEquivalence ((DiagSet.toInfty 1).map (coreFiltration 1 Y).ι) :=
      weakEquivalence_of_weakEquivalence_markedAboveFunctor_map 1 _
        (weakEquivalence_markedAboveFunctor_map_coreFiltration_ι Y fun B hB hd =>
          nonempty_coherentContraction Y
            (fun G _ a => hasLiftingProperty_boundary_coneRestrictionMap_outputVertex Y hC G a)
            B hB hd)
    obtain ⟨e, he⟩ := exists_iso_comp_coreFiltration_ι_eq_counit_app Y
    have h : WeakEquivalence
        ((DiagSet.toInfty 1).map e.hom ≫ (DiagSet.toInfty 1).map (coreFiltration 1 Y).ι) :=
      inferInstance
    rw [← Functor.map_comp, he] at h
    exact h
  exact key X (isInftyCategory_of_isFibrant 1 X hX)

open Atoms.Homotopical.MarkedSSet.modelCategoryCartesian in
theorem isQuillen_markedFaceNerveAdjunction :
    MarkedDiagSet.Coinductive.markedFaceNerveAdjunction.{u}.IsQuillen :=
  isQuillen_markedFaceNerveAdjunction_of_weakEquivalence
    weakEquivalence_markedFaceNerve_map_of_generators

open Atoms.Homotopical.MarkedSSet.modelCategoryCartesian SSet.modelCategoryJoyal in
theorem weakEquivalence_of_weakEquivalence_toDiagSet_map {K K' : SSet.{u}} (f : K ⟶ K')
    (hf : WeakEquivalence (SSet.toDiagSetInfty.map f)) :
    WeakEquivalence f := by
  have (W : MarkedDiagSet.Coinductive.{u} 1) : IsCofibrant W := by
    rw [isCofibrant_iff, cofibration_iff]
    let W' : MarkedDiagSet.{u} := W
    exact monomorphisms.infer_property (initial.to W')
  have : WeakEquivalence ((DiagSet.Infty.flat 1).map (SSet.toDiagSetInfty.map f)) :=
    (weakEquivalence_flat_map_iff 1 _).2 hf
  have : WeakEquivalence (faceNerve.map (SSet.toDiagSet.map f)) :=
    isQuillen_markedFaceNerveAdjunction.weakEquivalence_map
      ((DiagSet.Infty.flat 1).map (SSet.toDiagSetInfty.map f))
  obtain ⟨l, hl⟩ := exists_weakEquivalence_faceNerve_toDiagSet
  have := hl K
  have : WeakEquivalence (l.app K ≫ (MarkedPresheaf.flat edgeMarking).map f) := by
    rw [← l.naturality f]
    have := hl K'
    dsimp
    infer_instance
  exact (Atoms.Homotopical.weakEquivalence_flat_map_iff f).1
    (weakEquivalence_of_precomp (l.app K) _)

open SSet.modelCategoryJoyal in
theorem isQuillenEquivalence_sSetDiagSetAdj :
    DiagSet.Infty.sSetDiagSetAdj.{u}.IsQuillenEquivalence := by
  have hQ := isQuillen_sSetDiagSetAdj
  have (W : SSet.{u}) : IsCofibrant W := by
    rw [isCofibrant_iff, cofibration_iff]
    exact monomorphisms.infer_property _
  refine hQ.isQuillenEquivalence_iff.2 ⟨fun f hf =>
    weakEquivalence_of_weakEquivalence_toDiagSet_map f hf, fun X _ _ _ q _ _ => ?_⟩
  have := hQ.weakEquivalence_map q
  have := weakEquivalence_sSetDiagSetAdj_counit_app X inferInstance
  infer_instance

end Atoms.Diagrammatic
