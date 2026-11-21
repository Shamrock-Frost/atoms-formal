import Atoms.ForMathlib.CategoryTheory.MorphismProperty.Basic
import Atoms.ForMathlib.CategoryTheory.MorphismProperty.Composition
import Atoms.ForMathlib.CategoryTheory.MorphismProperty.Limits
import Atoms.ForMathlib.CategoryTheory.SmallObject.Basic

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra

namespace Atoms.Homotopical

universe w v

variable {A : Type v} [SmallCategory A]

class IsALocalizer (V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))) : Prop where
  hasTwoOutOfThreeProperty : V.HasTwoOutOfThreeProperty
  rlp_monomorphisms_le : (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v))).rlp ≤ V
  isStableUnderCobaseChange :
    (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)) ⊓ V).IsStableUnderCobaseChange
  isStableUnderTransfiniteComposition :
    (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)) ⊓
      V).IsStableUnderTransfiniteComposition.{max w v}

attribute [instance] IsALocalizer.hasTwoOutOfThreeProperty IsALocalizer.isStableUnderCobaseChange
  IsALocalizer.isStableUnderTransfiniteComposition

def generatedALocalizer (S : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))) :
    MorphismProperty (Aᵒᵖ ⥤ Type (max w v)) :=
  sInf {V | IsALocalizer V ∧ S ≤ V}

class IsAccessibleALocalizer (V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))) : Prop
    extends isALocalizer : IsALocalizer V where
  exists_generatedALocalizer_eq :
    ∃ S : MorphismProperty (Aᵒᵖ ⥤ Type (max w v)), S.IsSmall.{max w v} ∧ generatedALocalizer S = V

theorem isALocalizer_sInf (𝔙 : Set (MorphismProperty (Aᵒᵖ ⥤ Type (max w v))))
    (h : ∀ V ∈ 𝔙, IsALocalizer V) : IsALocalizer (sInf 𝔙) where
  hasTwoOutOfThreeProperty :=
    HasTwoOutOfThreeProperty.sInf fun V hV ↦ (h V hV).hasTwoOutOfThreeProperty
  rlp_monomorphisms_le _ _ f hf :=
    (MorphismProperty.sInf_iff 𝔙 f).2 fun V hV ↦ (h V hV).rlp_monomorphisms_le f hf
  isStableUnderCobaseChange :=
    ⟨fun sq hf ↦ by
      refine ⟨(inferInstance : IsSaturated.{max w v}
        (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)))).isStableUnderCobaseChange
          |>.of_isPushout sq hf.1, ?_⟩
      rw [MorphismProperty.sInf_iff]
      intro V hV
      exact ((h V hV).isStableUnderCobaseChange.of_isPushout sq
        ⟨hf.1, (MorphismProperty.sInf_iff 𝔙 _).1 hf.2 V hV⟩).2⟩
  isStableUnderTransfiniteComposition :=
    ⟨fun J _ _ _ _ ↦ ⟨by
      intro X Y f hf
      refine ⟨((inferInstance : IsSaturated.{max w v}
        (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)))).isStableUnderTransfiniteComposition
        |>.isStableUnderTransfiniteCompositionOfShape J).le f
          (transfiniteCompositionsOfShape_monotone J inf_le_left f hf), ?_⟩
      rw [MorphismProperty.sInf_iff]
      intro V hV
      exact (((h V hV).isStableUnderTransfiniteComposition
        |>.isStableUnderTransfiniteCompositionOfShape J).le f
          (transfiniteCompositionsOfShape_monotone J
            (inf_le_inf_left _ (sInf_le hV)) f hf)).2⟩⟩

instance isALocalizer_iInf {ι : Sort*} (V : ι → MorphismProperty (Aᵒᵖ ⥤ Type (max w v)))
    [∀ i, IsALocalizer (V i)] : IsALocalizer (⨅ i, V i) :=
  isALocalizer_sInf _ (by rintro _ ⟨i, rfl⟩; infer_instance)

theorem generatedALocalizer_iff (S : MorphismProperty (Aᵒᵖ ⥤ Type (max w v)))
    {X Y : Aᵒᵖ ⥤ Type (max w v)} (f : X ⟶ Y) :
    generatedALocalizer S f ↔
      ∀ V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v)), IsALocalizer V → S ≤ V → V f := by
  rw [generatedALocalizer, MorphismProperty.sInf_iff]
  simp only [Set.mem_ofPred_eq, and_imp]

instance isALocalizer_generatedALocalizer (S : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))) :
    IsALocalizer (generatedALocalizer S) :=
  isALocalizer_sInf _ fun _ hV ↦ hV.1

theorem le_generatedALocalizer (S : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))) :
    S ≤ generatedALocalizer S :=
  le_sInf fun _ hV ↦ hV.2

theorem generatedALocalizer_le {S V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))} [hV : IsALocalizer V]
    (h : S ≤ V) : generatedALocalizer S ≤ V :=
  sInf_le ⟨hV, h⟩

theorem generatedALocalizer_mono {S T : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))} (h : S ≤ T) :
    generatedALocalizer S ≤ generatedALocalizer T :=
  generatedALocalizer_le (h.trans (le_generatedALocalizer T))

instance isAccessibleALocalizer_generatedALocalizer (S : MorphismProperty (Aᵒᵖ ⥤ Type (max w v)))
    [S.IsSmall.{max w v}] : IsAccessibleALocalizer (generatedALocalizer S) where
  exists_generatedALocalizer_eq := ⟨S, inferInstance, rfl⟩

theorem IsAccessibleALocalizer.of_eq {S V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))}
    (hS : S.IsSmall.{max w v}) (h : generatedALocalizer S = V) : IsAccessibleALocalizer V :=
  h ▸ isAccessibleALocalizer_generatedALocalizer S

theorem IsALocalizer.isomorphisms_le {V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))}
    [hV : IsALocalizer V] : MorphismProperty.isomorphisms (Aᵒᵖ ⥤ Type (max w v)) ≤ V := by
  intro X Y f hf
  have : IsIso f := hf
  exact hV.rlp_monomorphisms_le _ (MorphismProperty.rlp_of_isIso _ f)

theorem IsALocalizer.of_terminal_from {V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))} [IsALocalizer V]
    {X Y : Aᵒᵖ ⥤ Type (max w v)} (f : X ⟶ Y) (hX : V (terminal.from X)) (hY : V (terminal.from Y)) :
    V f := by
  rw [show terminal.from X = f ≫ terminal.from Y from terminal.hom_ext _ _] at hX
  exact V.of_postcomp _ _ hY hX

theorem IsALocalizer.terminal_from_of_mem {V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))}
    [IsALocalizer V] {X Y : Aᵒᵖ ⥤ Type (max w v)} (f : X ⟶ Y) (hf : V f)
    (hX : V (terminal.from X)) : V (terminal.from Y) := by
  rw [show terminal.from X = f ≫ terminal.from Y from terminal.hom_ext _ _] at hX
  exact V.of_precomp _ _ hf hX

theorem IsALocalizer.terminal_from_of_iso {V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))}
    [hV : IsALocalizer V] {X Y : Aᵒᵖ ⥤ Type (max w v)} (e : X ≅ Y) (hY : V (terminal.from Y)) :
    V (terminal.from X) := by
  rw [show terminal.from X = e.hom ≫ terminal.from Y from terminal.hom_ext _ _]
  exact V.comp_mem _ _ (hV.isomorphisms_le _ (MorphismProperty.isomorphisms.infer_property _)) hY

instance IsALocalizer.respectsIso {V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))}
    [hV : IsALocalizer V] : V.RespectsIso :=
  respectsIso_of_isStableUnderComposition hV.isomorphisms_le

instance IsALocalizer.containsIdentities {V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))}
    [hV : IsALocalizer V] : V.ContainsIdentities :=
  ⟨fun X ↦ hV.isomorphisms_le _ (MorphismProperty.isomorphisms.infer_property (𝟙 X))⟩

instance IsALocalizer.isCellularlyClosed {V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))}
    [IsALocalizer V] :
    IsCellularlyClosed.{max w v} (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)) ⊓ V) where
  isStableUnderCobaseChange := inferInstance
  isStableUnderTransfiniteComposition := inferInstance

theorem IsALocalizer.coproducts_le {V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))} [IsALocalizer V]
    {T : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))}
    (hT : T ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)) ⊓ V) :
    MorphismProperty.coproducts.{max w v} T ≤
      MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)) ⊓ V := by
  have := IsCellularlyClosed.isStableUnderCoproducts.{max w v}
    (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)) ⊓ V)
  exact (coproducts_monotone hT).trans (MorphismProperty.coproducts_le _)

theorem IsALocalizer.transfiniteCompositions_pushouts_coproducts_le
    {V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))} [hV : IsALocalizer V]
    {T : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))}
    (hT : T ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)) ⊓ V) :
    (MorphismProperty.coproducts.{max w v} T).pushouts.transfiniteCompositions.{max w v} ≤
      MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)) ⊓ V := by
  exact (transfiniteCompositions_monotone.{max w v}
    ((pushouts_monotone (hV.coproducts_le hT)).trans MorphismProperty.pushouts_le)).trans
      (MorphismProperty.transfiniteCompositions_le _)

section AsSmall

variable {A : Type v} [SmallCategory A]

theorem IsALocalizer.inverseImage_asSmall {V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))}
    [hV : IsALocalizer.{w, v} V] :
    IsALocalizer.{max w v, max w v} (V.inverseImage
      (AsSmall.equiv : A ≌ AsSmall.{max w v} A).op.congrLeft.inverse) := by
  let E : (Aᵒᵖ ⥤ Type (max w v)) ≌ ((AsSmall.{max w v} A)ᵒᵖ ⥤ Type (max w v)) :=
    (AsSmall.equiv : A ≌ AsSmall.{max w v} A).op.congrLeft
  have hm := MorphismProperty.monomorphisms_eq_inverseImage_of_isEquivalence E.inverse
  have := hV.isStableUnderCobaseChange
  have := hV.isStableUnderTransfiniteComposition
  refine ⟨inferInstance, fun _ _ p hp ↦ hV.rlp_monomorphisms_le _ ?_, ?_, ?_⟩
  · rw [hm, MorphismProperty.rlp_inverseImage_of_isEquivalence] at hp
    exact hp
  · rw [hm, ← MorphismProperty.inverseImage_inf]
    infer_instance
  · rw [hm, ← MorphismProperty.inverseImage_inf]
    exact ⟨fun J _ _ _ _ ↦
      have : PreservesWellOrderContinuousOfShape J E.inverse := ⟨fun _ _ ↦ inferInstance⟩
      ⟨fun _ _ f hf ↦
      (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)) ⊓ V).transfiniteCompositionsOfShape_le
        J _ (MorphismProperty.transfiniteCompositionsOfShape_map_of_preserves J E.inverse f hf)⟩⟩

theorem IsALocalizer.inverseImage_asSmall_functor
    {V : MorphismProperty ((AsSmall.{max w v} A)ᵒᵖ ⥤ Type (max w v))}
    [hV : IsALocalizer.{max w v, max w v} V] :
    IsALocalizer.{w, v} (V.inverseImage
      (AsSmall.equiv : A ≌ AsSmall.{max w v} A).op.congrLeft.functor) := by
  let E : ((AsSmall.{max w v} A)ᵒᵖ ⥤ Type (max w v)) ≌ (Aᵒᵖ ⥤ Type (max w v)) :=
    (AsSmall.equiv : A ≌ AsSmall.{max w v} A).op.congrLeft.symm
  have hm : MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)) =
      (MorphismProperty.monomorphisms ((AsSmall.{max w v} A)ᵒᵖ ⥤ Type (max w v))).inverseImage
        (AsSmall.equiv : A ≌ AsSmall.{max w v} A).op.congrLeft.functor :=
    MorphismProperty.monomorphisms_eq_inverseImage_of_isEquivalence _
  have := hV.isStableUnderCobaseChange
  have := hV.isStableUnderTransfiniteComposition
  refine ⟨inferInstance, fun _ _ p hp ↦ hV.rlp_monomorphisms_le _ ?_, ?_, ?_⟩
  · rw [hm, MorphismProperty.rlp_inverseImage_of_isEquivalence] at hp
    exact hp
  · rw [hm, ← MorphismProperty.inverseImage_inf]
    infer_instance
  · rw [hm, ← MorphismProperty.inverseImage_inf]
    exact ⟨fun J _ _ _ _ ↦
      have : PreservesWellOrderContinuousOfShape J E.inverse := ⟨fun _ _ ↦ inferInstance⟩
      ⟨fun _ _ f hf ↦
      (MorphismProperty.monomorphisms ((AsSmall.{max w v} A)ᵒᵖ ⥤ Type (max w v)) ⊓
        V).transfiniteCompositionsOfShape_le J _
        (MorphismProperty.transfiniteCompositionsOfShape_map_of_preserves J E.inverse f hf)⟩⟩

theorem generatedALocalizer_inverseImage_asSmall (S : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))) :
    (generatedALocalizer.{w, v} S).inverseImage
        (AsSmall.equiv : A ≌ AsSmall.{max w v} A).op.congrLeft.inverse =
      generatedALocalizer.{max w v, max w v}
        (functorImage (AsSmall.equiv : A ≌ AsSmall.{max w v} A).op.congrLeft.functor S) := by
  have := IsALocalizer.inverseImage_asSmall (V := generatedALocalizer.{w, v} S)
  have := IsALocalizer.inverseImage_asSmall_functor (V := generatedALocalizer.{max w v, max w v}
      (functorImage (AsSmall.equiv : A ≌ AsSmall.{max w v} A).op.congrLeft.functor S))
  refine le_antisymm (fun X Y f hf ↦ ?_) (generatedALocalizer_le ?_)
  · have hle : generatedALocalizer.{w, v} S ≤
        (generatedALocalizer.{max w v, max w v} (functorImage
          (AsSmall.equiv : A ≌ AsSmall.{max w v} A).op.congrLeft.functor S)).inverseImage
          (AsSmall.equiv : A ≌ AsSmall.{max w v} A).op.congrLeft.functor :=
      generatedALocalizer_le fun K L s hs ↦ le_generatedALocalizer _ _ ⟨K, L, s, hs, rfl⟩
    exact (MorphismProperty.map_functor_map_inverse_iff
      (AsSmall.equiv : A ≌ AsSmall.{max w v} A).op.congrLeft _ f).1 (hle _ hf)
  · rintro _ _ g ⟨K, L, s, hs, e⟩
    refine (MorphismProperty.arrow_mk_iso_iff _ (eqToIso e)).1 ?_
    exact (MorphismProperty.map_functor_map_inverse_iff
      (AsSmall.equiv : A ≌ AsSmall.{max w v} A).op.congrLeft.symm _ s).2
        (le_generatedALocalizer S s hs)

theorem IsAccessibleALocalizer.inverseImage_asSmall
    {V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))} [hV : IsAccessibleALocalizer.{w, v} V] :
    IsAccessibleALocalizer.{max w v, max w v} (V.inverseImage
      (AsSmall.equiv : A ≌ AsSmall.{max w v} A).op.congrLeft.inverse) := by
  obtain ⟨S, hS, rfl⟩ := hV.exists_generatedALocalizer_eq
  rw [generatedALocalizer_inverseImage_asSmall]
  exact isAccessibleALocalizer_generatedALocalizer _

theorem generatedALocalizer_inverseImage_asSmall_functor
    (S : MorphismProperty ((AsSmall.{max w v} A)ᵒᵖ ⥤ Type (max w v))) :
    (generatedALocalizer.{max w v, max w v} S).inverseImage
        (AsSmall.equiv : A ≌ AsSmall.{max w v} A).op.congrLeft.functor =
      generatedALocalizer.{w, v}
        (functorImage (AsSmall.equiv : A ≌ AsSmall.{max w v} A).op.congrLeft.inverse S) := by
  have := IsALocalizer.inverseImage_asSmall_functor
    (V := generatedALocalizer.{max w v, max w v} S)
  have := IsALocalizer.inverseImage_asSmall (V := generatedALocalizer.{w, v}
      (functorImage (AsSmall.equiv : A ≌ AsSmall.{max w v} A).op.congrLeft.inverse S))
  refine le_antisymm (fun X Y f hf ↦ ?_) (generatedALocalizer_le ?_)
  · have hle : generatedALocalizer.{max w v, max w v} S ≤
        (generatedALocalizer.{w, v} (functorImage
          (AsSmall.equiv : A ≌ AsSmall.{max w v} A).op.congrLeft.inverse S)).inverseImage
          (AsSmall.equiv : A ≌ AsSmall.{max w v} A).op.congrLeft.inverse :=
      generatedALocalizer_le fun K L s hs ↦ le_generatedALocalizer _ _ ⟨K, L, s, hs, rfl⟩
    exact (MorphismProperty.map_functor_map_inverse_iff
      (AsSmall.equiv : A ≌ AsSmall.{max w v} A).op.congrLeft.symm _ f).1 (hle _ hf)
  · rintro _ _ g ⟨K, L, s, hs, e⟩
    refine (MorphismProperty.arrow_mk_iso_iff _ (eqToIso e)).1 ?_
    exact (MorphismProperty.map_functor_map_inverse_iff
      (AsSmall.equiv : A ≌ AsSmall.{max w v} A).op.congrLeft _ s).2
        (le_generatedALocalizer S s hs)

theorem IsAccessibleALocalizer.inverseImage_asSmall_functor
    {V : MorphismProperty ((AsSmall.{max w v} A)ᵒᵖ ⥤ Type (max w v))}
    [hV : IsAccessibleALocalizer.{max w v, max w v} V] :
    IsAccessibleALocalizer.{w, v} (V.inverseImage
      (AsSmall.equiv : A ≌ AsSmall.{max w v} A).op.congrLeft.functor) := by
  obtain ⟨S, hS, rfl⟩ := hV.exists_generatedALocalizer_eq
  rw [generatedALocalizer_inverseImage_asSmall_functor]
  exact isAccessibleALocalizer_generatedALocalizer _

end AsSmall

end Atoms.Homotopical
