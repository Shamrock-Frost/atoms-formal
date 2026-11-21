import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.RightPushoutProduct
import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Quillen
import Atoms.Homotopical.Cylinder.AbsoluteWeakEquivalence
import Atoms.Homotopical.Simplicial.Joyal
import Mathlib.AlgebraicTopology.ModelCategory.BrownLemma

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra Simplicial

universe u

namespace SSet.modelCategoryJoyal

open Atoms.Homotopical

private lemma rightAnodyneExtensions_joyalPoint (ε : Bool) :
    rightAnodyneExtensions (joyalPoint ε) :=
  rightFibrations.llp.comp_mem _ _ (MorphismProperty.of_isIso _ _)
    (rightAnodyneExtensions_coherentIso_vertex ε)

private lemma isAnodyneClass_rightAnodyneExtensions :
    IsAnodyneClass joyalInterval.{u}.cylinder rightHornInclusions rightAnodyneExtensions where
  isSaturated := inferInstanceAs (IsSaturated.{u} rightFibrations.llp)
  generators_le := le_llp_rlp _
  endpointBox_mem ε {_ _} i hi :=
    have := hi
    rightAnodyneExtensions_pushoutObjObjι_left (joyalInterval.{u}.endpointBoxPushoutObjObj ε i)
      (rightAnodyneExtensions_joyalPoint ε)
  bothBox_mem {_ _} i _ h :=
    rightAnodyneExtensions_pushoutObjObjι (joyalInterval.{u}.bothBoxPushoutObjObj i) h

theorem rightAnodyneExtensions_eq_anodyne :
    rightAnodyneExtensions.{u} = joyalInterval.{u}.cylinder.anodyne rightHornInclusions := by
  refine le_antisymm ?_ (joyalInterval.{u}.cylinder.anodyne_le _ _
    isAnodyneClass_rightAnodyneExtensions)
  rw [rightAnodyneExtensions, rightFibrations, ← saturation_eq_llp_rlp.{u}]
  exact saturation_le _ _ (joyalInterval.{u}.cylinder.le_anodyne _)

theorem anodyne_innerHornInclusions_le_rightAnodyneExtensions :
    joyalInterval.{u}.cylinder.anodyne innerHornInclusions ≤ rightAnodyneExtensions.{u} :=
  rightAnodyneExtensions_eq_anodyne ▸
    joyalInterval.{u}.cylinder.anodyne_mono fun _ _ _ ⟨i, h0, _⟩ ↦ .intro i h0

theorem rightAnodyneExtensions_of_comp {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [Mono g]
    (hf : rightAnodyneExtensions f) (hfg : rightAnodyneExtensions (f ≫ g)) :
    rightAnodyneExtensions g := by
  rw [rightAnodyneExtensions_eq_anodyne] at hf hfg ⊢
  exact joyalInterval.{u}.cylinder.anodyne_of_comp rightHornInclusions
    rightHornInclusions_le_monomorphisms f g hf hfg inferInstance

private lemma weakEquivalence_joinMap_id_of_cofibration {K L : SSet.{u}} (f : K ⟶ L)
    [Cofibration f] [WeakEquivalence f] (Z : SSet.{u}) : WeakEquivalence (joinMap f (𝟙 Z)) := by
  refine weakEquivalence_of_hasLiftingProperty _ fun E B p hE hB hp ↦ ?_
  rw [isFibrant_iff_quasicategory] at hE hB
  rw [fibration_iff_isofibration] at hp
  refine (hasLiftingProperty_joinMap_id_iff f p).2 fun z ↦ ?_
  have : (Under.mk z).right.Quasicategory := hE
  have : (Under.mk (z ≫ p)).right.Quasicategory := hB
  have : Fibration ((slice Z).map (Under.homMk p : Under.mk z ⟶ Under.mk (z ≫ p))) :=
    (fibration_iff_isofibration _).2 (isofibration_slice_map p z)
  infer_instance

theorem weakEquivalence_joinMap_id {X Y : SSet.{u}} (f : X ⟶ Y) [WeakEquivalence f]
    (Z : SSet.{u}) : WeakEquivalence (joinMap f (𝟙 Z)) := by
  have (W : SSet.{u}) : IsCofibrant W := by
    rw [isCofibrant_iff, cofibration_iff]
    exact monomorphisms.infer_property _
  obtain ⟨h⟩ := (inferInstance : Nonempty (CofibrantBrownFactorization f))
  have := weakEquivalence_joinMap_id_of_cofibration h.i Z
  have := weakEquivalence_joinMap_id_of_cofibration h.s Z
  have : WeakEquivalence (joinMap h.p (𝟙 Z)) :=
    weakEquivalence_of_precomp_of_fac (f := joinMap h.s (𝟙 Z)) (fg := 𝟙 _) (by
      rw [joinMap_comp_joinMap_id, h.s_p]
      exact (joinRightUnder Z ⋙ Under.forget Z).map_id Y)
  rw [← h.fac, ← joinMap_comp_joinMap_id]
  infer_instance

end SSet.modelCategoryJoyal
