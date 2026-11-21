import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.LeftPushoutProduct
import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Quillen
import Atoms.Homotopical.Cylinder.AbsoluteWeakEquivalence
import Atoms.Homotopical.Simplicial.Joyal
import Mathlib.AlgebraicTopology.ModelCategory.BrownLemma

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra Simplicial

universe u

namespace SSet.modelCategoryJoyal

open Atoms.Homotopical

private lemma leftAnodyneExtensions_joyalPoint (ε : Bool) :
    leftAnodyneExtensions (joyalPoint ε) :=
  leftFibrations.llp.comp_mem _ _ (MorphismProperty.of_isIso _ _)
    (leftAnodyneExtensions_coherentIso_vertex ε)

private lemma isAnodyneClass_leftAnodyneExtensions :
    IsAnodyneClass joyalInterval.{u}.cylinder leftHornInclusions leftAnodyneExtensions where
  isSaturated := inferInstanceAs (IsSaturated.{u} leftFibrations.llp)
  generators_le := le_llp_rlp _
  endpointBox_mem ε {_ _} i hi :=
    have := hi
    leftAnodyneExtensions_pushoutObjObjι_left (joyalInterval.{u}.endpointBoxPushoutObjObj ε i)
      (leftAnodyneExtensions_joyalPoint ε)
  bothBox_mem {_ _} i _ h :=
    leftAnodyneExtensions_pushoutObjObjι (joyalInterval.{u}.bothBoxPushoutObjObj i) h

theorem leftAnodyneExtensions_eq_anodyne :
    leftAnodyneExtensions.{u} = joyalInterval.{u}.cylinder.anodyne leftHornInclusions := by
  refine le_antisymm ?_ (joyalInterval.{u}.cylinder.anodyne_le _ _
    isAnodyneClass_leftAnodyneExtensions)
  rw [leftAnodyneExtensions, leftFibrations, ← saturation_eq_llp_rlp.{u}]
  exact saturation_le _ _ (joyalInterval.{u}.cylinder.le_anodyne _)

theorem leftFibrations_eq_naiveFibrations :
    leftFibrations.{u} = joyalInterval.{u}.cylinder.naiveFibrations leftHornInclusions := by
  rw [ExactCylinder.naiveFibrations, ← leftAnodyneExtensions_eq_anodyne, leftAnodyneExtensions,
    leftFibrations, rlp_llp_rlp]

theorem anodyne_innerHornInclusions_le_leftAnodyneExtensions :
    joyalInterval.{u}.cylinder.anodyne innerHornInclusions ≤ leftAnodyneExtensions.{u} :=
  leftAnodyneExtensions_eq_anodyne ▸
    joyalInterval.{u}.cylinder.anodyne_mono fun _ _ _ ⟨i, _, hi⟩ ↦ .intro i hi

theorem leftAnodyneExtensions_of_comp {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [Mono g]
    (hf : leftAnodyneExtensions f) (hfg : leftAnodyneExtensions (f ≫ g)) :
    leftAnodyneExtensions g := by
  rw [leftAnodyneExtensions_eq_anodyne] at hf hfg ⊢
  exact joyalInterval.{u}.cylinder.anodyne_of_comp leftHornInclusions
    leftHornInclusions_le_monomorphisms f g hf hfg inferInstance

end SSet.modelCategoryJoyal
