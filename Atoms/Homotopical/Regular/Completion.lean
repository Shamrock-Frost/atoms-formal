import Atoms.Homotopical.Regular.Saturation

open CategoryTheory Limits MorphismProperty

namespace Atoms.Homotopical

universe v

variable {A : Type v} [SmallCategory A]

instance isALocalizer_regularCompletion (V : MorphismProperty (Aᵒᵖ ⥤ Type v)) :
    IsALocalizer.{v, v} (regularCompletion V) :=
  isALocalizer_generatedALocalizer _

theorem le_regularCompletion (V : MorphismProperty (Aᵒᵖ ⥤ Type v)) :
    V ≤ regularCompletion V :=
  le_sup_left.trans (le_generatedALocalizer _)

instance isRegularALocalizer_regularCompletion (V : MorphismProperty (Aᵒᵖ ⥤ Type v)) :
    IsRegularALocalizer (regularCompletion V) :=
  ⟨fun X ↦ le_generatedALocalizer _ _ (le_sup_right (a := V) _ (ofHoms.mk X))⟩

theorem regularCompletion_le {V W : MorphismProperty (Aᵒᵖ ⥤ Type v)} [IsALocalizer W]
    [IsRegularALocalizer W] (h : V ≤ W) : regularCompletion V ≤ W := by
  refine generatedALocalizer_le (sup_le h ?_)
  intro _ _ _ hf
  cases hf
  exact IsRegularALocalizer.isRegular _

theorem regularCompletion_mono {V W : MorphismProperty (Aᵒᵖ ⥤ Type v)} (h : V ≤ W) :
    regularCompletion V ≤ regularCompletion W :=
  generatedALocalizer_mono (sup_le_sup_right h _)

instance IsAccessibleALocalizer.regularCompletion {V : MorphismProperty (Aᵒᵖ ⥤ Type v)}
    [hV : IsAccessibleALocalizer V] : IsAccessibleALocalizer.{v, v} (regularCompletion V) := by
  obtain ⟨S, hS, rfl⟩ := hV
  let S' : MorphismProperty (Aᵒᵖ ⥤ Type v) :=
    ofHoms fun p : CellularIndex A × Bool ↦
      regularizationMap (bif p.2 then p.1.subfunctor.toFunctor else p.1.congruence.quotient)
  have hS'' : (S ⊔ S').IsSmall.{v} := inferInstance
  have hacc : IsAccessibleALocalizer (generatedALocalizer.{v, v} (S ⊔ S')) := ⟨_, hS'', rfl⟩
  have : IsRegularALocalizer (generatedALocalizer.{v, v} (S ⊔ S')) := by
    refine (hacc.isRegularALocalizer_iff_of_saturation_eq (cellularGenerators A)
      (monomorphisms_eq_saturation_cellularGenerators A).symm).2 ?_
    rintro _ _ _ ⟨i⟩
    exact ⟨le_generatedALocalizer _ _ (le_sup_right (a := S) _ (ofHoms.mk (i, true))),
      le_generatedALocalizer _ _ (le_sup_right (a := S) _ (ofHoms.mk (i, false)))⟩
  have heq : Atoms.Homotopical.regularCompletion (generatedALocalizer.{v, v} S) =
      generatedALocalizer (S ⊔ S') := by
    refine le_antisymm (regularCompletion_le (generatedALocalizer_mono le_sup_left))
      (generatedALocalizer_le (sup_le ?_ ?_))
    · exact (le_generatedALocalizer S).trans (le_regularCompletion _)
    · intro _ _ _ hf
      cases hf
      exact (isRegularALocalizer_regularCompletion _).isRegular _
  rw [heq]
  exact hacc

instance isAccessibleALocalizer_regularCompletion_bot :
    IsAccessibleALocalizer.{v, v} (regularCompletion (⊥ : MorphismProperty (Aᵒᵖ ⥤ Type v))) := by
  have heq : regularCompletion (⊥ : MorphismProperty (Aᵒᵖ ⥤ Type v)) =
      regularCompletion (generatedALocalizer.{v, v} ⊥) := by
    apply le_antisymm
    · exact regularCompletion_mono bot_le
    · exact regularCompletion_le (generatedALocalizer_le bot_le)
  rw [heq]
  infer_instance

end Atoms.Homotopical
