import Atoms.Homotopical.Localizer.Accessible
import Atoms.Homotopical.Cylinder.ModelStructure

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra

namespace Atoms.Homotopical

universe w v

section SingleUniverse

variable {A : Type v} [SmallCategory A]

private theorem exists_trivialCofibrations_eq_saturation_aux
    {V : MorphismProperty (Aᵒᵖ ⥤ Type v)} [hV : IsAccessibleALocalizer.{v, v} V] :
    ∃ J : MorphismProperty (Aᵒᵖ ⥤ Type v), J.IsSmall.{v} ∧
      MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v) ⊓ V = saturation.{v} J := by
  obtain ⟨S, hS, hmono, rfl⟩ := hV.exists_lawvereCylinder
  exact (lawvereCylinder A).trivialCofibrationsSetGenerated S hmono

private theorem rlp_inf_eq_aux {V : MorphismProperty (Aᵒᵖ ⥤ Type v)}
    [hV : IsAccessibleALocalizer.{v, v} V] :
    (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v) ⊓ V).rlp ⊓ V =
      (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v)).rlp := by
  obtain ⟨S, hS, hmono, rfl⟩ := hV.exists_lawvereCylinder
  let := (lawvereCylinder A).modelCategory S hmono
  exact (MorphismProperty.rlp_eq_of_wfs (cofibrations (Aᵒᵖ ⥤ Type v))
    (trivialFibrations (Aᵒᵖ ⥤ Type v))).symm

private theorem isStableUnderRetracts_aux {V : MorphismProperty (Aᵒᵖ ⥤ Type v)}
    [IsALocalizer.{v, v} V] : V.IsStableUnderRetracts where
  of_retract {X Y Z W} {f g} h hg := by
    let T := MorphismProperty.ofHoms fun _ : Unit ↦ g
    have hT : T ≤ V := by
      rintro _ _ _ ⟨⟩
      exact hg
    have : T.IsSmall.{v} := isSmall_ofHoms.{v} fun _ : Unit ↦ g
    obtain ⟨S, -, -, hS⟩ := (isAccessibleALocalizer_generatedALocalizer T).exists_lawvereCylinder
    have hacc : (generatedALocalizer T).IsStableUnderRetracts := by
      rw [← hS]
      exact (lawvereCylinder A).weakEquivalences_isStableUnderRetracts S
    refine generatedALocalizer_le hT _ (hacc.of_retract h ?_)
    exact le_generatedALocalizer T _ (MorphismProperty.ofHoms.mk ())

end SingleUniverse

variable {A : Type v} [SmallCategory A]

theorem IsAccessibleALocalizer.exists_trivialCofibrations_eq_saturation
    {V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))} [hV : IsAccessibleALocalizer V] :
    ∃ J : MorphismProperty (Aᵒᵖ ⥤ Type (max w v)), J.IsSmall.{max w v} ∧
      MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)) ⊓ V = saturation.{max w v} J := by
  have := hV.inverseImage_asSmall
  obtain ⟨J, hJ, h⟩ := exists_trivialCofibrations_eq_saturation_aux (A := AsSmall.{max w v} A)
    (V := V.inverseImage (AsSmall.equiv : A ≌ AsSmall.{max w v} A).op.congrLeft.inverse)
  refine ⟨functorImage (AsSmall.equiv : A ≌ AsSmall.{max w v} A).op.congrLeft.inverse J,
    inferInstance, ?_⟩
  rw [← MorphismProperty.inverseImage_saturation_functor, ← h,
    MorphismProperty.inverseImage_inf,
    MorphismProperty.inverseImage_inverse_inverseImage_functor,
    ← MorphismProperty.monomorphisms_eq_inverseImage_of_isEquivalence]

theorem llp_rlp_cellularGenerators :
    (cellularGenerators.{w} A).rlp.llp = MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)) := by
  rw [← saturation_eq_llp_rlp, monomorphisms_eq_saturation_cellularGenerators]

theorem IsAccessibleALocalizer.isWeakFactorizationSystem_trivialCofibrations
    {V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))} [hV : IsAccessibleALocalizer V] :
    IsWeakFactorizationSystem (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)) ⊓ V)
      (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)) ⊓ V).rlp := by
  obtain ⟨J, hJ, hJeq⟩ := hV.exists_trivialCofibrations_eq_saturation
  rw [hJeq]
  exact isWeakFactorizationSystem_saturation J

theorem IsAccessibleALocalizer.isWeakFactorizationSystem_monomorphisms
    {V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))} [hV : IsAccessibleALocalizer V] :
    IsWeakFactorizationSystem (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)))
      ((MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)) ⊓ V).rlp ⊓ V) := by
  have := hV.inverseImage_asSmall
  have h := rlp_inf_eq_aux (A := AsSmall.{max w v} A)
    (V := V.inverseImage (AsSmall.equiv : A ≌ AsSmall.{max w v} A).op.congrLeft.inverse)
  have h' := congrArg (MorphismProperty.inverseImage ·
    (AsSmall.equiv : A ≌ AsSmall.{max w v} A).op.congrLeft.functor) h
  simp only [MorphismProperty.inverseImage_inf] at h'
  rw [← MorphismProperty.rlp_inverseImage_of_isEquivalence,
    ← MorphismProperty.rlp_inverseImage_of_isEquivalence, MorphismProperty.inverseImage_inf,
    MorphismProperty.inverseImage_inverse_inverseImage_functor,
    ← MorphismProperty.monomorphisms_eq_inverseImage_of_isEquivalence] at h'
  rw [h', monomorphisms_eq_saturation_cellularGenerators.{w} A]
  exact isWeakFactorizationSystem_saturation _

instance IsALocalizer.isStableUnderRetracts {V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))}
    [IsALocalizer V] : V.IsStableUnderRetracts := by
  have := IsALocalizer.inverseImage_asSmall (V := V)
  have := isStableUnderRetracts_aux (A := AsSmall.{max w v} A)
    (V := V.inverseImage (AsSmall.equiv : A ≌ AsSmall.{max w v} A).op.congrLeft.inverse)
  rw [← MorphismProperty.inverseImage_inverse_inverseImage_functor
    (AsSmall.equiv : A ≌ AsSmall.{max w v} A).op.congrLeft V]
  infer_instance

instance IsALocalizer.isSaturated_monomorphisms_inf {V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))}
    [IsALocalizer V] :
    IsSaturated.{max w v} (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)) ⊓ V) where
  isStableUnderRetracts :=
    ⟨fun h hg ↦ ⟨(MorphismProperty.monomorphisms _).of_retract h hg.1, V.of_retract h hg.2⟩⟩

@[instance_reducible]
def IsAccessibleALocalizer.modelCategory {V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))}
    [hV : IsAccessibleALocalizer V] : ModelCategory (Aᵒᵖ ⥤ Type (max w v)) :=
  have := hV.isWeakFactorizationSystem_trivialCofibrations
  monoModelCategory V hV.isWeakFactorizationSystem_monomorphisms.rlp

namespace IsAccessibleALocalizer.modelCategory

variable {V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))} [hV : IsAccessibleALocalizer V]

theorem cofibrations_eq :
    letI := hV.modelCategory
    cofibrations (Aᵒᵖ ⥤ Type (max w v)) = MorphismProperty.monomorphisms _ := rfl

theorem weakEquivalences_eq :
    letI := hV.modelCategory
    weakEquivalences (Aᵒᵖ ⥤ Type (max w v)) = V := rfl

theorem fibrations_eq :
    letI := hV.modelCategory
    fibrations (Aᵒᵖ ⥤ Type (max w v)) =
      (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)) ⊓ V).rlp := rfl

end IsAccessibleALocalizer.modelCategory

end Atoms.Homotopical
