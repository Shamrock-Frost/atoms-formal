import Atoms.Diagrammatic.KanComparison
import Atoms.Diagrammatic.Subdivision.Basic
import Atoms.Homotopical.Simplicial.CartesianKan
import Atoms.Homotopical.Simplicial.SubdivisionQuillen

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra Simplicial Opposite
open Atoms.Homotopical Atoms.Shape

universe u

namespace Atoms.Diagrammatic

open SSet.modelCategoryQuillen in
private theorem isQuillenEquivalence_sSetDiagSetAdj_comp_sdExAdjunction :
    (sSetDiagSetAdj.{u}.comp DiagSet.sdExAdjunction).IsQuillenEquivalence :=
  isQuillenEquivalence_sdExAdjunction.of_iso _ DiagSet.toDiagSetCompSdIso.symm

open MarkedSSet.modelCategoryCartesian in
theorem DiagSet.kanWeak_sd_map_of_weakEquivalence {X Y : DiagSet.Infty.{u} 1} (f : X ⟶ Y)
    [WeakEquivalence f] : kanWeak (DiagSet.sd.map f) := by
  have (W : MarkedDiagSet.Coinductive.{u} 1) : IsCofibrant W := by
    rw [isCofibrant_iff, cofibration_iff]
    let W' : MarkedDiagSet.{u} := W
    exact monomorphisms.infer_property (initial.to W')
  have (W : MarkedSSet.{u}) : IsCofibrant W := by
    rw [isCofibrant_iff, cofibration_iff]
    exact monomorphisms.infer_property (initial.to W)
  have := (isQuillen_flatForgetAdjunction 1).weakEquivalence_map f
  have := isQuillen_markedFaceNerveAdjunction.weakEquivalence_map ((DiagSet.Infty.flat 1).map f)
  open SSet.modelCategoryQuillen in
  exact (weakEquivalence_iff _).1 (isQuillen_forgetSharpAdjunction_kan.weakEquivalence_map
    (MarkedDiagSet.Coinductive.markedFaceNerve.map ((DiagSet.Infty.flat 1).map f)))

open MarkedSSet.modelCategoryCartesian SSet.modelCategoryQuillen in
theorem DiagSet.isInftyCategory_ex_obj (K : SSet.{u}) [K.KanComplex] :
    IsInftyCategory 0 (DiagSet.ex.obj K) := by
  have h₁ : IsFibrant ((MarkedPresheaf.sharp edgeMarking).obj K) :=
    (MarkedSSet.modelCategoryCartesian.isFibrant_iff_isFibrant _).2
      (cartesian_isFibrant_sharp_of_kanComplex K)
  have h₂ := isFibrant_forget_obj 1 _
    (isQuillen_markedFaceNerveAdjunction.isFibrant_obj ((MarkedPresheaf.sharp edgeMarking).obj K))
  have h₃ : IsInftyCategory 1 (DiagSet.ex.obj K) :=
    (isInftyCategory_iff_rlp 1 _).2 fun _ _ i hi => h₂ i (reversibleCylinder.le_anodyne _ i hi)
  have : (DiagSet.toSSet.obj (DiagSet.ex.obj K)).KanComplex :=
    isQuillenEquivalence_sSetDiagSetAdj_comp_sdExAdjunction.toIsQuillen.isFibrant_obj K
  exact (kanComplex_toSSet_obj_iff h₃).1 this

open SSet.modelCategoryQuillen DiagSet.modelCategoryCisinski in
theorem DiagSet.isQuillen_sdExAdjunction : DiagSet.sdExAdjunction.{u}.IsQuillen := by
  have key := ExactCylinder.map_mem_weakEquivalences reversibleCylinder.{u}
    simplicialCylinder.{u} (inftyGenerators 0) ⊥ DiagSet.sdExAdjunction (fun Y => by
      have : WeakEquivalence ((DiagSet.toInfty 1).map (reversibleCylinder.contraction.app Y)) :=
        (weakEquivalence_iff _).2 (reversibleCylinder.contraction_mem_weakEquivalences
          (inftyGenerators 1) (inftyGenerators_le_monomorphisms 1) Y)
      exact DiagSet.kanWeak_sd_map_of_weakEquivalence
        ((DiagSet.toInfty 1).map (reversibleCylinder.contraction.app Y)))
    (fun Z hZ => by
      have : SSet.KanComplex Z := (isFibrant_bot_iff_kanComplex Z).1 hZ
      exact (ExactCylinder.modelCategory.isFibrant_iff reversibleCylinder (inftyGenerators 0)
        (inftyGenerators_le_monomorphisms 0) _).1
        ((isFibrant_infty_iff 0 _).2 (DiagSet.isInftyCategory_ex_obj Z)))
  rw [weakEquivalences_infty_zero_eq_hornWeak, hornWeak_eq_infinityEquivalences] at key
  exact
    { cofibrations_le := fun _ _ f hf => by
        have : Mono f := hf
        exact DiagSet.sd.map_mono f
      trivialCofibrations_le := fun _ _ f hf => by
        have : Mono f := hf.1
        exact ⟨DiagSet.sd.map_mono f, key f hf.2⟩ }

open SSet.modelCategoryQuillen DiagSet.modelCategoryCisinski in
theorem DiagSet.isQuillenEquivalence_sdExAdjunction :
    DiagSet.sdExAdjunction.{u}.IsQuillenEquivalence :=
  DiagSet.isQuillen_sdExAdjunction.isQuillenEquivalence_of_comp
    isQuillenEquivalence_sSetDiagSetAdj_kan isQuillenEquivalence_sSetDiagSetAdj_comp_sdExAdjunction

open SSet.modelCategoryQuillen DiagSet.modelCategoryCisinski in
theorem DiagSet.kanWeak_sd_map_iff {X Y : DiagSet.{u}} (f : X ⟶ Y) :
    kanWeak (DiagSet.sd.map f) ↔ infinityEquivalences f := by
  have (W : DiagSet.{u}) : IsCofibrant W :=
    (isCofibrant_iff W).2 ((HomotopicalAlgebra.cofibration_iff _).2
      (monomorphisms.infer_property (initial.to W)))
  constructor
  · intro hf
    exact (weakEquivalence_iff _).1 ((DiagSet.isQuillen_sdExAdjunction.isQuillenEquivalence_iff.1
      DiagSet.isQuillenEquivalence_sdExAdjunction).1 f ((weakEquivalence_iff _).2 hf))
  · intro hf
    have : WeakEquivalence f := (weakEquivalence_iff _).2 hf
    exact (weakEquivalence_iff _).1 (DiagSet.isQuillen_sdExAdjunction.weakEquivalence_map f)

end Atoms.Diagrammatic
