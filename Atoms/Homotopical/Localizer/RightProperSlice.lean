import Atoms.Homotopical.Localizer.RightProper
import Atoms.Homotopical.Localizer.Transport

open CategoryTheory Limits Opposite Atoms Atoms.Homotopical MorphismProperty

namespace Atoms.Homotopical

universe v

instance isRightProper_inverseImage_sliceForget (A : Type v) [SmallCategory A]
    (V : MorphismProperty (Aᵒᵖ ⥤ Type v)) [IsALocalizer V]
    [IsRightProper V] (X : Aᵒᵖ ⥤ Type v) :
    IsRightProper (V.inverseImage (sliceForget X)) := by
  have h : MorphismProperty.monomorphisms _ ⊓ V.inverseImage (sliceForget X) =
      (MorphismProperty.monomorphisms _ ⊓ V).inverseImage (sliceForget X) := by
    rw [monomorphisms_eq_inverseImage_sliceForget]
    rfl
  refine isRightProper_inverseImage_of_rlp_map (sliceForget X) V fun q' hq' ↦ ?_
  rw [h, rlp_inverseImage_sliceForget_of_respectsIso] at hq'
  exact hq'

theorem isRightProper_inverseImage_presheafEquivalence {A B : Type v} [SmallCategory A]
    [SmallCategory B] (e : A ≌ B) (V : MorphismProperty (Bᵒᵖ ⥤ Type v)) [V.RespectsIso]
    [IsRightProper V] : IsRightProper (V.inverseImage e.op.congrLeft.functor) := by
  let E : (Aᵒᵖ ⥤ Type v) ≌ (Bᵒᵖ ⥤ Type v) := e.op.congrLeft
  have h : MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v) ⊓ V.inverseImage E.functor =
      (MorphismProperty.monomorphisms (Bᵒᵖ ⥤ Type v) ⊓ V).inverseImage E.functor := by
    ext X Y f
    simp [Functor.mono_map_iff_mono]
  refine isRightProper_inverseImage_of_rlp_map E.functor V fun q hq _ _ m hm ↦ ?_
  rw [h] at hq
  refine (E.symm.toAdjunction.hasLiftingProperty_iff m q).1 (hq _ ?_)
  exact (map_functor_map_inverse_iff E _ m).2 hm

theorem isRightProper_inverseImage_iff {A B : Type v} [SmallCategory A] [SmallCategory B]
    (e : A ≌ B) (V : MorphismProperty (Bᵒᵖ ⥤ Type v)) [V.RespectsIso] :
    IsRightProper (V.inverseImage e.op.congrLeft.functor) ↔ IsRightProper V := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ isRightProper_inverseImage_presheafEquivalence e V⟩
  rw [← inverseImage_inverseImage_congrLeft_op e V]
  exact isRightProper_inverseImage_presheafEquivalence e.symm _

end Atoms.Homotopical
