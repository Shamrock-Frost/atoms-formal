import Atoms.Homotopical.Regular.Descent
import Atoms.TestCategory.Localizer.FibrantProductWeakness
import Atoms.TestCategory.Localizer.MinimalBaseChange
import Atoms.TestCategory.Localizer.RepresentableCompletion

open CategoryTheory Limits Opposite Atoms.Homotopical MorphismProperty

namespace Atoms.TestCategory

universe u

section Recognition

variable {A : Type u} [SmallCategory A]

theorem representableMaps_le_inverseImage_sliceForget (X : Aᵒᵖ ⥤ Type u) :
    representableMaps (CostructuredArrow yoneda X) ≤
      (representableCompletion A).inverseImage (sliceForget X) := by
  rintro _ _ _ ⟨i⟩
  exact (MorphismProperty.arrow_mk_iso_iff (representableCompletion A)
    (Arrow.isoOfNatIso (sliceForgetYonedaNatIso _) (Arrow.mk i.2.2))).2
    (yoneda_map_mem_representableCompletion A i.2.2.left)

theorem representableCompletion_forget_le (X : Aᵒᵖ ⥤ Type u) :
    representableCompletion (CostructuredArrow yoneda X) ≤
      (representableCompletion A).inverseImage (sliceForget X) :=
  regularCompletion_le (representableMaps_le_inverseImage_sliceForget X)

theorem representableCompletion_over_representable_eq [minimalBasicLocalizer.{u}.IsLocalTest A]
    (a : A) :
    representableCompletion (CostructuredArrow yoneda (yoneda.obj a)) =
      minimalBasicLocalizer.wPsh (CostructuredArrow yoneda (yoneda.obj a)) := by
  have : HasTerminal (CostructuredArrow yoneda (yoneda.obj a)) :=
    CostructuredArrow.mkIdTerminal.hasTerminal
  exact representableCompletion_eq_minimal_of_terminal _

instance isRightProper_representableCompletion_over_representable
    [minimalBasicLocalizer.{u}.IsLocalTest A] [IsRightProper (minimalBasicLocalizer.{u}.wPsh A)]
    (a : A) :
    IsRightProper (representableCompletion (CostructuredArrow yoneda (yoneda.obj a))) := by
  rw [representableCompletion_over_representable_eq]
  infer_instance

theorem completion_fibration_over {E B : Aᵒᵖ ⥤ Type u} (p : E ⟶ B)
    (hp : (MorphismProperty.monomorphisms _ ⊓ representableCompletion A).rlp p) :
    (MorphismProperty.monomorphisms _ ⊓
      representableCompletion (CostructuredArrow yoneda B)).rlp (sliceHom p (𝟙 B)) := by
  have hle : MorphismProperty.monomorphisms _ ⊓
      representableCompletion (CostructuredArrow yoneda B) ≤
      (MorphismProperty.monomorphisms _ ⊓ representableCompletion A).inverseImage
        (sliceForget B) := by
    rw [MorphismProperty.inverseImage_inf, ← monomorphisms_eq_inverseImage_sliceForget]
    exact inf_le_inf_left _ (representableCompletion_forget_le B)
  refine MorphismProperty.antitone_rlp hle _ ?_
  rw [rlp_inverseImage_sliceForget_of_respectsIso]
  exact (MorphismProperty.arrow_mk_iso_iff _ (sliceForgetMapSliceHomIso p (𝟙 B))).2 hp

theorem completion_fibration_locallyConstant_minimal [minimalBasicLocalizer.{u}.IsLocalTest A]
    [IsRightProper (minimalBasicLocalizer.{u}.wPsh A)] {E B : Aᵒᵖ ⥤ Type u} (p : E ⟶ B)
    (hp : (MorphismProperty.monomorphisms _ ⊓ representableCompletion A).rlp p) :
    LocallyConstant (minimalBasicLocalizer.wPsh A) p := by
  refine (locallyConstant_iff_yoneda p).2 fun a a' f b ↦ ?_
  have hq : (MorphismProperty.monomorphisms _ ⊓ representableCompletion A).rlp
      (pullback.fst b p) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback b p).flip hp
  have hwf : WeakFibration _ (sliceHom (pullback.fst b p) (𝟙 (yoneda.obj a'))) :=
    (isRightProper_representableCompletion_over_representable a').weakFibration_of_rlp _
      (completion_fibration_over _ hq)
  have hi := hwf _ (𝟙 _) (sliceHom_yoneda_map_mem_representableCompletion f)
  have hU := representableCompletion_forget_le (yoneda.obj a') _ hi
  exact minimalBasicLocalizer.representableCompletion_le_wPsh A
    _ ((sliceForget_map_baseChangeMap_sliceHom_mem_iff _ (yoneda.map f) b p).1 hU)

theorem completion_fibration_weakFibration_minimal [minimalBasicLocalizer.{u}.IsLocalTest A]
    [IsRightProper (minimalBasicLocalizer.{u}.wPsh A)] {E B : Aᵒᵖ ⥤ Type u} (p : E ⟶ B)
    (hp : (MorphismProperty.monomorphisms _ ⊓ representableCompletion A).rlp p) :
    WeakFibration (minimalBasicLocalizer.wPsh A) p :=
  weakFibration_of_locallyConstant A p (completion_fibration_locallyConstant_minimal p hp)

theorem completion_fibration_universal [minimalBasicLocalizer.{u}.IsLocalTest A]
    [IsRightProper (minimalBasicLocalizer.{u}.wPsh A)] {E B : Aᵒᵖ ⥤ Type u} (p : E ⟶ B)
    (hp : (MorphismProperty.monomorphisms _ ⊓ representableCompletion A).rlp p)
    (hw : minimalBasicLocalizer.wPsh A p) (K : Aᵒᵖ ⥤ Type u) (b : K ⟶ B) :
    minimalBasicLocalizer.wPsh A (pullback.fst b p) :=
  (isAccessibleALocalizer_minimal_wPsh A).mem_pullback_fst_of_weakFibration_of_mem
    p (completion_fibration_weakFibration_minimal p hp) hw K b

theorem completion_fibration_representable_pullback_mem [minimalBasicLocalizer.{u}.IsLocalTest A]
    [IsRightProper (minimalBasicLocalizer.{u}.wPsh A)] {E B : Aᵒᵖ ⥤ Type u} (p : E ⟶ B)
    (hp : (MorphismProperty.monomorphisms _ ⊓ representableCompletion A).rlp p)
    (hw : minimalBasicLocalizer.wPsh A p) (a : A) (b : yoneda.obj a ⟶ B) :
    representableCompletion A (pullback.fst b p) := by
  let e := sliceForgetMapSliceHomIso (pullback.fst b p) (𝟙 (yoneda.obj a))
  have hq := completion_fibration_universal p hp hw _ b
  have hY : minimalBasicLocalizer.wPsh (CostructuredArrow yoneda (yoneda.obj a))
      (sliceHom (pullback.fst b p) (𝟙 (yoneda.obj a))) := by
    rw [minimalBasicLocalizer.wPsh_costructuredArrow_eq (yoneda.obj a)]
    exact (MorphismProperty.arrow_mk_iso_iff _ e).2 hq
  rw [← representableCompletion_over_representable_eq a] at hY
  exact (MorphismProperty.arrow_mk_iso_iff _ e).1
    (representableCompletion_forget_le (yoneda.obj a) _ hY)

theorem completion_fibration_minimal_weak_mem [minimalBasicLocalizer.{u}.IsLocalTest A]
    [IsRightProper (minimalBasicLocalizer.{u}.wPsh A)] {E B : Aᵒᵖ ⥤ Type u} (p : E ⟶ B)
    (hp : (MorphismProperty.monomorphisms _ ⊓ representableCompletion A).rlp p)
    (hw : minimalBasicLocalizer.wPsh A p) :
    representableCompletion A p :=
  (isAccessible_representableCompletion A).mem_of_forall_pullback_fst_mem p
    (fun a b => completion_fibration_representable_pullback_mem p hp hw a b)

variable (A) in
theorem representableCompletion_eq_minimal [minimalBasicLocalizer.{u}.IsLocalTest A]
    [IsRightProper (minimalBasicLocalizer.{u}.wPsh A)] :
    representableCompletion A = minimalBasicLocalizer.wPsh A := by
  have hle := minimalBasicLocalizer.representableCompletion_le_wPsh A
  refine le_antisymm hle fun _ _ f hf => ?_
  obtain ⟨Z, i, π, hi, hπ, rfl⟩ :=
    (isAccessible_representableCompletion A).exists_factorization f
  have hwπ : minimalBasicLocalizer.wPsh A π :=
    MorphismProperty.of_precomp _ i π (hle _ hi.2) hf
  exact MorphismProperty.comp_mem _ i π hi.2 (completion_fibration_minimal_weak_mem π hπ hwπ)

theorem minimal_wPsh_le_of_representableMaps_le [minimalBasicLocalizer.{u}.IsLocalTest A]
    [IsRightProper (minimalBasicLocalizer.{u}.wPsh A)] (V : MorphismProperty (Aᵒᵖ ⥤ Type u))
    [IsALocalizer V] [IsRegularALocalizer V] (hV : representableMaps A ≤ V) :
    minimalBasicLocalizer.wPsh A ≤ V := by
  rw [← representableCompletion_eq_minimal A]
  exact regularCompletion_le hV

end Recognition

end Atoms.TestCategory
