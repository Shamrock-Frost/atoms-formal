import Atoms.Diagrammatic.KanComparison
import Atoms.Diagrammatic.Suspension.Hom
import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Over
import Atoms.Shape.SuspensionHorn

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra
open Atoms.Molecule Atoms.Shape Atoms.Homotopical

universe u

namespace Atoms.Diagrammatic

private theorem fibrations_infty_zero_eq :
    fibrations (DiagSet.Infty.{u} 0) = (monomorphisms DiagSet.{u} ⊓ hornWeak).rlp := by
  rw [← weakEquivalences_infty_zero_eq_hornWeak]
  rfl

theorem DiagSet.Infty.fibration_zero_iff_rlp_hornInclusions {X Y : DiagSet.Infty.{u} 0}
    (p : X ⟶ Y) (hY : IsFibrant Y) : Fibration p ↔ hornInclusions.rlp p := by
  rw [fibration_iff, fibrations_infty_zero_eq]
  exact rlp_trivialCofibrations_iff_rlp_hornInclusions p
    ((isHornFibrant_iff_isInftyCategory_zero Y).2 ((isFibrant_infty_iff 0 Y).1 hY))

private theorem fibration_zero_of_rlp_atomicHornInclusions {X Y : DiagSet.Infty.{u} 0}
    (p : X ⟶ Y) (hY : IsFibrant Y) (hp : atomicHornInclusions.rlp p) : Fibration p := by
  rw [fibration_iff, fibrations_infty_zero_eq, ← atomicHornWeak_eq_hornWeak]
  refine grayExactCylinder.{u}.rlp_trivialCofibrations_of_rlp_anodyne atomicHornInclusions
    (atomicHornInclusions_le_hornInclusions.trans hornInclusions_le_monomorphisms) p ?_
    ((isFibrant_atomicHornInclusions_iff Y).2 ((isAtomicHornFibrant_iff_isHornFibrant Y).2
      ((isHornFibrant_iff_isInftyCategory_zero Y).2 ((isFibrant_infty_iff 0 Y).1 hY))))
  rw [ExactCylinder.naiveFibrations, anodyne_atomicHornInclusions, MorphismProperty.rlp_saturation]
  exact hp

noncomputable def _root_.SSet.toDiagSetInftyZero : SSet.{u} ⥤ DiagSet.Infty.{u} 0 :=
  SSet.toDiagSet

def DiagSet.Infty.toSSetZero : DiagSet.Infty.{u} 0 ⥤ SSet.{u} := DiagSet.toSSet

noncomputable def DiagSet.Infty.sSetDiagSetAdjZero :
    SSet.toDiagSetInftyZero.{u} ⊣ DiagSet.Infty.toSSetZero.{u} :=
  Atoms.Diagrammatic.sSetDiagSetAdj

private theorem weakEquivalence_infty_zero_iff {A B : DiagSet.Infty.{u} 0} (f : A ⟶ B) :
    WeakEquivalence f ↔ infinityEquivalences.{u} f := by
  rw [weakEquivalence_iff, ← hornWeak_eq_infinityEquivalences,
    ← weakEquivalences_infty_zero_eq_hornWeak]
  rfl

open SSet.modelCategoryQuillen DiagSet.modelCategoryCisinski in
theorem isQuillenEquivalence_sSetDiagSetAdjZero :
    DiagSet.Infty.sSetDiagSetAdjZero.{u}.IsQuillenEquivalence := by
  have h := isQuillenEquivalence_sSetDiagSetAdj_kan.{u}
  refine ⟨⟨fun A B i hi => ?_, fun A B i hi => ?_⟩, fun {A X} _ hX f => ?_⟩
  · exact h.cofibrations_le i hi
  · exact ⟨(h.trivialCofibrations_le i hi).1, (HomotopicalAlgebra.weakEquivalence_iff _).1 <|
      (weakEquivalence_infty_zero_iff (SSet.toDiagSetInftyZero.map i)).2
        (h.trivialCofibrations_le i hi).2⟩
  · have hX' : IsFibrant (C := DiagSet.{u}) X :=
      (DiagSet.modelCategoryCisinski.isFibrant_iff X).2
        ((isHornFibrant_iff_isInftyCategory_zero X).2 ((isFibrant_infty_iff 0 X).1 hX))
    rw [weakEquivalence_infty_zero_iff]
    exact (HomotopicalAlgebra.weakEquivalence_iff _).symm.trans (h.weakEquivalence_iff f)

noncomputable abbrev pointPairInfty (n : ℕ∞) : DiagSet.Infty.{u} n :=
  (DiagSet.toInfty n).obj pointPair

noncomputable def bipointedSuspensionInfty (n : ℕ∞) :
    DiagSet.Infty.{u} n ⥤ Under (pointPairInfty.{u} (n + 1)) :=
  bipointedSuspension

noncomputable def bipointedHomInfty (n : ℕ∞) :
    Under (pointPairInfty.{u} (n + 1)) ⥤ DiagSet.Infty.{u} n :=
  bipointedHom

noncomputable def bipointedSuspensionAdjunctionInfty (n : ℕ∞) :
    bipointedSuspensionInfty.{u} n ⊣ bipointedHomInfty.{u} n :=
  bipointedSuspensionAdjunction

theorem mono_bipointedSuspension_map_right {A B : DiagSet.{u}} (i : A ⟶ B) [Mono i] :
    Mono (bipointedSuspension.map i).right := by
  let Q : MorphismProperty DiagSet.{u} :=
    ((monomorphisms DiagSet.{u}).under (X := pointPair.{u})).inverseImage bipointedSuspension
  have hQ : sphereInclusions.{u} ≤ Q := by
    rintro _ _ _ ⟨U⟩
    have h := congrArg CommaMorphism.right (bipointedSuspension_map_sphereInclusion.{u} U)
    simp only [Under.comp_right] at h
    have : IsIso (bipointedSuspensionSphereIso.{u} U).hom.right :=
      ((CategoryTheory.Under.forget _).mapIso (bipointedSuspensionSphereIso.{u} U)).isIso_hom
    have : Mono ((bipointedSuspension.map (sphereInclusion U)).right ≫
        (bipointedSuspensionBallIso.{u} U).hom.right) := by
      rw [h]
      exact @mono_comp _ _ _ _ _ _ inferInstance _ (mono_sphereInclusion (atomSuspension.obj U))
    exact mono_of_mono _ (bipointedSuspensionBallIso.{u} U).hom.right
  have hle := saturation_le.{u} _ Q hQ
  rw [← monomorphisms_eq_saturation_sphereInclusions] at hle
  exact hle i (monomorphisms.infer_property i)

noncomputable def bipointedSuspensionHornArrowIso (h : HornData) :
    CategoryTheory.Arrow.mk (bipointedSuspension.map (hornInclusion.{u} h)) ≅
      CategoryTheory.Arrow.mk (Under.homMk
        (U := Under.mk (closedSubpresheafSuspensionPoles.{u} h.atom (hornSubset h)
          (hornSubset h.suspension) (hornSubset_suspension h)))
        (V := suspendedBall.obj h.atom) (hornInclusion h.suspension)
        (closedSubpresheafSuspensionPoles_comp h.atom (hornSubset h) (hornSubset h.suspension)
          (hornSubset_suspension h))) :=
  Arrow.isoMk (bipointedSuspensionClosedSubpresheafIso h.atom (hornSubset h)
      (hornSubset h.suspension) (hornSubset_suspension h)) (bipointedSuspensionBallIso h.atom)
    (bipointedSuspension_map_closedSubpresheaf_ι h.atom (hornSubset h) (hornSubset h.suspension)
      (hornSubset_suspension h)).symm

theorem trivialCofibration_hornInclusion_suspension (h : AtomicHornData) :
    trivialCofibrations (DiagSet.Infty.{u} 1)
      ((DiagSet.toInfty 1).map (hornInclusion h.suspension.toHornData)) := by
  obtain ⟨x, hx⟩ := h.isAtomic
  refine ⟨(cofibration_iff _).1 ((cofibration_iff _).2 (inferInstanceAs
    (Mono (closedSubpresheaf _ _).ι))), (weakEquivalence_iff _).1 ?_⟩
  refine weakEquivalence_of_weakEquivalence_markedAboveFunctor_map 1 _ ?_
  obtain ⟨m, ⟨E⟩⟩ := exists_markedHornData_iso_markedAbove_hornInclusion h.suspension _
    (HornData.IsAtomic.suspension hx) (boundary_Iic_atomSuspension_zero h.atom x)
  have hm : markedExactCylinder.{u}.weakEquivalences (coinductiveGenerators 1)
      (markedHornInclusion m) :=
    markedExactCylinder.{u}.anodyne_le_weakEquivalences _ (coinductiveGenerators_le_monomorphisms 1)
      _ (markedExactCylinder.{u}.le_anodyne _ _
        ((le_sup_left.trans le_sup_left : markedHorns ≤ coinductiveGenerators 1) _
          (MorphismProperty.ofHoms.mk m)))
  exact (weakEquivalence_iff _).2
    (((markedExactCylinder.{u}.weakEquivalences _).arrow_mk_iso_iff E).1 hm)

private theorem cofibrations_le_bipointedSuspensionInfty_zero :
    cofibrations (DiagSet.Infty.{u} 0) ≤
      (cofibrations (Under (pointPairInfty.{u} (0 + 1)))).inverseImage
        (bipointedSuspensionInfty 0) := by
  intro A B i hi
  have : Mono (C := DiagSet.{u}) i := hi
  exact @mono_bipointedSuspension_map_right _ _ i this

theorem isQuillen_bipointedSuspensionAdjunctionZero :
    (bipointedSuspensionAdjunctionInfty.{u} 0).IsQuillen := by
  refine (bipointedSuspensionAdjunctionInfty.{u} 0).isQuillen_of_fibrations_between_fibrant
    cofibrations_le_bipointedSuspensionInfty_zero fun X Y p _ hY hp => ?_
  have hY' : IsInftyCategory 1 (Y.right : DiagSet.{u}) :=
    (isFibrant_infty_iff 1 Y.right).1 ((isFibrant_under_iff _ Y).1 hY)
  refine fibration_zero_of_rlp_atomicHornInclusions _ (isFibrant_bipointedHom hY') ?_
  rintro _ _ _ ⟨h⟩
  have hp' : Fibration (C := DiagSet.Infty.{u} 1) p.right := (fibrations_under_iff _ p).1 hp
  have hh := trivialCofibration_hornInclusion_suspension.{u} h
  have : Cofibration ((DiagSet.toInfty 1).map (hornInclusion.{u} h.suspension.toHornData)) :=
    (cofibration_iff _).2 hh.1
  have : WeakEquivalence ((DiagSet.toInfty 1).map (hornInclusion.{u} h.suspension.toHornData)) :=
    (weakEquivalence_iff _).2 hh.2
  have : HasLiftingProperty (C := DiagSet.Infty.{u} 1)
      ((DiagSet.toInfty 1).map (hornInclusion.{u} h.suspension.toHornData)) p.right :=
    ModelCategory.cm4a _ _
  have hl : HasLiftingProperty ((bipointedSuspensionInfty 0).map (hornInclusion.{u} h.toHornData))
      p :=
    (HasLiftingProperty.iff_of_arrow_iso_left (bipointedSuspensionHornArrowIso h.toHornData) p).2
      (@HasLiftingProperty.under _ _ _ _ _ _ _ _ _ this)
  exact ((bipointedSuspensionAdjunctionInfty.{u} 0).hasLiftingProperty_iff _ p).1 hl

open SSet.modelCategoryQuillen in
theorem isQuillen_sSetDiagSetAdjZero_comp_bipointedSuspensionAdjunctionInfty :
    (DiagSet.Infty.sSetDiagSetAdjZero.{u}.comp (bipointedSuspensionAdjunctionInfty 0)).IsQuillen :=
  isQuillenEquivalence_sSetDiagSetAdjZero.toIsQuillen.comp
    isQuillen_bipointedSuspensionAdjunctionZero

theorem DiagSet.fibration_bipointedHom_map {X Y : DiagSet.{u}} (F : X ⟶ Y)
    [Fibration ((DiagSet.toInfty 1).map F)] (a b : X.Vertex) :
    Fibration ((DiagSet.toInfty 0).map (bipointedHom.map (DiagSet.bipointMap F a b))) := by
  have : Fibration (C := Under (pointPairInfty.{u} (0 + 1))) (DiagSet.bipointMap F a b) :=
    (fibration_iff _).2 ((fibration_iff ((DiagSet.toInfty 1).map F)).1 inferInstance)
  exact isQuillen_bipointedSuspensionAdjunctionZero.fibration_map
    (C := DiagSet.Infty.{u} 0) (D := Under (pointPairInfty.{u} (0 + 1))) _

end Atoms.Diagrammatic
