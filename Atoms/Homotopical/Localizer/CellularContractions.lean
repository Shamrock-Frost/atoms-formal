import Atoms.Homotopical.Localizer.AccessibleModel

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra

namespace Atoms.Homotopical

universe w v

variable {A : Type v} [SmallCategory A]

end Atoms.Homotopical

namespace HomotopicalAlgebra.ExactCylinder

open Atoms.Homotopical

universe w v

variable {A : Type v} [SmallCategory A]

variable (𝕀 : ExactCylinder.{max w v} (Aᵒᵖ ⥤ Type (max w v)))

def cellularContractions : MorphismProperty (Aᵒᵖ ⥤ Type (max w v)) :=
  MorphismProperty.ofHoms (fun i : CellularIndex A ↦ 𝕀.contraction.app i.subfunctor.toFunctor) ⊔
    MorphismProperty.ofHoms
      (fun i : CellularIndex.{w, v} A ↦ 𝕀.contraction.app i.congruence.quotient)

theorem isSmall_cellularContractions : (𝕀.cellularContractions).IsSmall.{max w v} :=
  MorphismProperty.isSmall_sup _ _

theorem endpointBox_mem_of_cellularContractions_le {V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))}
    [IsALocalizer V] (h : 𝕀.cellularContractions ≤ V) (ε : Bool)
    {K X : Aᵒᵖ ⥤ Type (max w v)} (i : K ⟶ X) (hi : Mono i) :
    (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)) ⊓ V) (𝕀.endpointBox ε i) := by
  have := 𝕀.isSaturated_endpointBox_preimage ε
    (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)) ⊓ V)
  have hi' : saturation.{max w v} (cellularGenerators.{w} A) i := by
    rw [← monomorphisms_eq_saturation_cellularGenerators A]
    exact hi
  refine saturation_le.{max w v} (cellularGenerators.{w} A)
    (NatTrans.leibnizPreimage (𝕀.endpoint ε)
      (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)) ⊓ V))
    (fun K X t ht ↦ ?_) i hi'
  obtain ⟨j⟩ := ht
  have hK : V ((𝕀.endpoint ε).app j.subfunctor.toFunctor) :=
    (IsALocalizer.endpoint_mem_iff_contraction_mem 𝕀 ε _).2 (h _ (Or.inl (ofHoms.mk j)))
  have hX : V ((𝕀.endpoint ε).app j.congruence.quotient) :=
    (IsALocalizer.endpoint_mem_iff_contraction_mem 𝕀 ε _).2 (h _ (Or.inr (ofHoms.mk j)))
  have hinr : (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)) ⊓ V)
      (pushout.inr ((𝕀.endpoint ε).app j.subfunctor.toFunctor) j.subfunctor.ι) :=
    MorphismProperty.of_isPushout (IsPushout.of_hasPushout _ _).flip
      ⟨𝕀.mono_endpoint ε _, hK⟩
  have e : pushout.inr _ _ ≫ 𝕀.endpointBox ε j.subfunctor.ι =
      (𝕀.endpoint ε).app j.congruence.quotient :=
    pushout.inr_desc _ _ (𝕀.endpoint_naturality ε _)
  refine ⟨𝕀.mono_endpointBox ε _ (cellularGenerators_le_monomorphisms A _ (ofHoms.mk j)), ?_⟩
  exact V.of_precomp _ _ hinr.2 ((congrArg (fun f ↦ V f) e).mpr hX)

theorem endpoint_mem_of_cellularContractions_le {V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))}
    [IsALocalizer V] (h : 𝕀.cellularContractions ≤ V) (ε : Bool)
    (Y : Aᵒᵖ ⥤ Type (max w v)) : V ((𝕀.endpoint ε).app Y) := by
  exact (MorphismProperty.of_retract (𝕀.endpointRetractArrow ε Y)
    (𝕀.endpointBox_mem_of_cellularContractions_le h ε (initial.to Y)
      (initial.mono_from _ _))).2

theorem contraction_mem_of_cellularContractions_le {V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))}
    [IsALocalizer V] (h : 𝕀.cellularContractions ≤ V) :
    CylinderCompatibleWith (Aᵒᵖ ⥤ Type (max w v)) V 𝕀 := fun X ↦
  (IsALocalizer.endpoint_mem_iff_contraction_mem 𝕀 false X).1
    (𝕀.endpoint_mem_of_cellularContractions_le h false X)

theorem weakEquivalences_eq_generatedALocalizer_cellularContractions
    (S : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))) [S.IsSmall.{max w v}]
    (hS : S ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v))) :
    𝕀.weakEquivalences S = generatedALocalizer (S ⊔ 𝕀.cellularContractions) := by
  have := 𝕀.isSmall_cellularContractions
  have hle := le_generatedALocalizer (S ⊔ 𝕀.cellularContractions)
  refine le_antisymm (𝕀.weakEquivalences_le_of_endpoint_mem S hS (le_sup_left.trans hle)
    fun ε X ↦ 𝕀.endpoint_mem_of_cellularContractions_le (le_sup_right.trans hle) ε X) ?_
  have := 𝕀.isALocalizer_weakEquivalences S hS
  refine generatedALocalizer_le
    (sup_le ((𝕀.le_anodyne S).trans (𝕀.anodyne_le_weakEquivalences S hS)) ?_)
  intro _ _ f hf
  rcases hf with hf | hf <;> cases hf <;> exact 𝕀.contraction_mem_weakEquivalences S hS _

end HomotopicalAlgebra.ExactCylinder
