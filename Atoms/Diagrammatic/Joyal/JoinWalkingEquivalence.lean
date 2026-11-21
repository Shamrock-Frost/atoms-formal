import Atoms.Diagrammatic.JoinMonomorphism
import Atoms.Diagrammatic.Joyal.JoinGenerators
import Atoms.Diagrammatic.Localization.InversionHorn

open CategoryTheory CategoryTheory.WithInitial Limits MorphismProperty HomotopicalAlgebra
  Atoms.Shape Atoms.Molecule Atoms.Molecule.OGP

universe u

namespace Atoms.Diagrammatic

open scoped DiagSet.Join

theorem weakEquivalence_toInfty_pushoutObjObj_ι_atomicHorn (U : Atom) (x : U.ogp)
    (hx : x ⋖ U.top)
    (hs : U.ogp.boundary (LowerSet.Iic x) 0 false = U.ogp.boundary ⊤ 0 false) (V : Atom) :
    WeakEquivalence ((DiagSet.toInfty 1).map (Functor.PushoutObjObj.ofHasPushout 𝒥
      (hornInclusion.{u} (atomicHornDataOfCovBy U x hx).toHornData) (sphereInclusion.{u} V)).ι) :=
  (weakEquivalence_toInfty_map_iff_markedAbove 1 _).2
    (weakEquivalence_markedAboveFunctor_map_pushoutObjObj_ι_atomicHorn 1 U x hx hs V)

private theorem trivialCofibration_toInfty_pushoutObjObj_ι_of_mono {X₁ Y₁ X₂ Y₂ : DiagSet.{u}}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) [Mono f₁] [Mono f₂]
    (h : WeakEquivalence ((DiagSet.toInfty 1).map
      (Functor.PushoutObjObj.ofHasPushout 𝒥 f₁ f₂).ι)) :
    trivialCofibrations (DiagSet.Infty.{u} 1) ((DiagSet.toInfty 1).map
      (Functor.PushoutObjObj.ofHasPushout 𝒥 f₁ f₂).ι) :=
  ⟨(cofibration_iff _).1 ((cofibration_iff _).2 (mono_pushoutObjObj_ι_join f₁ f₂)),
    (weakEquivalence_iff _).1 h⟩

private theorem trivialCofibration_toInfty_pushoutObjObj_ι_of_saturation
    (S₁ S₂ : MorphismProperty DiagSet.{u})
    (h : ∀ ⦃X₁ Y₁ X₂ Y₂ : DiagSet.{u}⦄ (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂), S₁ f₁ → S₂ f₂ →
      trivialCofibrations (DiagSet.Infty.{u} 1) ((DiagSet.toInfty 1).map
        (Functor.PushoutObjObj.ofHasPushout 𝒥 f₁ f₂).ι))
    {X₁ Y₁ X₂ Y₂ : DiagSet.{u}} {f₁ : X₁ ⟶ Y₁} {f₂ : X₂ ⟶ Y₂}
    (h₁ : saturation.{u} S₁ f₁) (h₂ : saturation.{u} S₂ f₂) :
    trivialCofibrations (DiagSet.Infty.{u} 1) ((DiagSet.toInfty 1).map
      (Functor.PushoutObjObj.ofHasPushout 𝒥 f₁ f₂).ι) := by
  have : IsSaturated.{u} (trivialCofibrations (DiagSet.Infty.{u} 1)) := by
    rw [← fibrations_llp]
    infer_instance
  have : PreservesColimitsOfSize.{u, u} (DiagSet.toInfty.{u} 1) :=
    inferInstanceAs (PreservesColimitsOfSize (𝟭 DiagSet.{u}))
  exact pushoutObjObj_ι_join_mem_of_saturation
    ((trivialCofibrations (DiagSet.Infty.{u} 1)).inverseImage (DiagSet.toInfty 1)) S₁ S₂ h h₁ h₂

theorem trivialCofibration_toInfty_pushoutObjObj_ι_of_saturation_sourceHorns
    {X₁ Y₁ X₂ Y₂ : DiagSet.{u}} {f : X₁ ⟶ Y₁} (hf : saturation.{u} sourceHorns.{u} f)
    (j : X₂ ⟶ Y₂) [Mono j] :
    trivialCofibrations (DiagSet.Infty.{u} 1)
      ((DiagSet.toInfty 1).map (Functor.PushoutObjObj.ofHasPushout 𝒥 f j).ι) := by
  have hj : saturation.{u} sphereInclusions j := by
    rw [← monomorphisms_eq_saturation_sphereInclusions]
    exact ‹Mono j›
  refine trivialCofibration_toInfty_pushoutObjObj_ι_of_saturation sourceHorns sphereInclusions
    (fun _ _ _ _ f₁ f₂ h₁ h₂ => ?_) hf hj
  obtain ⟨⟨⟨W, x⟩, hx, hs⟩⟩ := h₁
  obtain ⟨V⟩ := h₂
  have : Mono (hornInclusion.{u} (atomicHornDataOfCovBy W x hx).toHornData) :=
    inferInstanceAs (Mono (Subfunctor.ι _))
  exact trivialCofibration_toInfty_pushoutObjObj_ι_of_mono _ _
    (weakEquivalence_toInfty_pushoutObjObj_ι_atomicHorn W x hx hs V)

theorem weakEquivalence_toInfty_pushoutObjObj_ι_walkingEquivalence (U : Atom)
    (hU : 1 < U.dimension) (V : Atom) :
    WeakEquivalence ((DiagSet.toInfty 1).map (Functor.PushoutObjObj.ofHasPushout 𝒥
      (toWalkingEquivalence.{u} U (zero_lt_one.trans hU)) (sphereInclusion.{u} V)).ι) :=
  (weakEquivalence_iff _).2 (trivialCofibration_toInfty_pushoutObjObj_ι_of_saturation_sourceHorns
    (saturation_sourceHorns_toWalkingEquivalence U hU) (sphereInclusion.{u} V)).2

theorem weakEquivalence_toInfty_pushoutObjObj_ι_of_inftyGenerators {X Y : DiagSet.{u}}
    {f : X ⟶ Y} (hf : inftyGenerators 1 f) (V : Atom) :
    WeakEquivalence ((DiagSet.toInfty 1).map
      (Functor.PushoutObjObj.ofHasPushout 𝒥 f (sphereInclusion.{u} V)).ι) := by
  rcases hf with ⟨⟨U, hU⟩⟩ | ⟨⟨U, hU⟩⟩
  · exact weakEquivalence_toInfty_pushoutObjObj_ι_compositor U hU V
      (weakEquivalence_toInfty_pushoutObjObj_ι_walkingEquivalence _
        (by rw [dimension_toMergerAtom]; omega) V)
  · exact weakEquivalence_toInfty_pushoutObjObj_ι_walkingEquivalence U (by exact_mod_cast hU) V

theorem trivialCofibration_toInfty_pushoutObjObj_ι_of_saturation_inftyGenerators
    {X₁ Y₁ X₂ Y₂ : DiagSet.{u}} {f : X₁ ⟶ Y₁} (hf : saturation.{u} (inftyGenerators 1) f)
    (j : X₂ ⟶ Y₂) [Mono j] :
    trivialCofibrations (DiagSet.Infty.{u} 1)
      ((DiagSet.toInfty 1).map (Functor.PushoutObjObj.ofHasPushout 𝒥 f j).ι) := by
  have hj : saturation.{u} sphereInclusions j := by
    rw [← monomorphisms_eq_saturation_sphereInclusions]
    exact ‹Mono j›
  refine trivialCofibration_toInfty_pushoutObjObj_ι_of_saturation (inftyGenerators 1)
    sphereInclusions (fun _ _ _ _ f₁ f₂ h₁ h₂ => ?_) hf hj
  obtain ⟨V⟩ := h₂
  have : Mono f₁ := inftyGenerators_le_monomorphisms 1 _ h₁
  exact trivialCofibration_toInfty_pushoutObjObj_ι_of_mono _ _
    (weakEquivalence_toInfty_pushoutObjObj_ι_of_inftyGenerators h₁ V)

end Atoms.Diagrammatic
