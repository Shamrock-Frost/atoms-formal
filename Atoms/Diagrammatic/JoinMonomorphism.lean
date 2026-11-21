import Atoms.Diagrammatic.JoinClosedSubpresheaf
import Atoms.ForMathlib.CategoryTheory.Adhesive.Basic
import Atoms.ForMathlib.CategoryTheory.Limits.FunctorToTypes
import Atoms.ForMathlib.CategoryTheory.MorphismProperty.Leibniz
import Atoms.ForMathlib.CategoryTheory.Monoidal.DayConvolution.JoinSlice

open CategoryTheory CategoryTheory.WithInitial Limits MorphismProperty Atoms.Shape

universe u

namespace Atoms.Diagrammatic

open scoped DiagSet.Join

theorem pushoutObjObj_ι_join_mem_of_saturation (P S₁ S₂ : MorphismProperty DiagSet.{u})
    [IsSaturated.{u} P]
    (h : ∀ ⦃X₁ Y₁ X₂ Y₂ : DiagSet.{u}⦄ (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂), S₁ f₁ → S₂ f₂ →
      P (Functor.PushoutObjObj.ofHasPushout 𝒥 f₁ f₂).ι)
    {X₁ Y₁ X₂ Y₂ : DiagSet.{u}} {f₁ : X₁ ⟶ Y₁} {f₂ : X₂ ⟶ Y₂}
    (h₁ : saturation.{u} S₁ f₁) (h₂ : saturation.{u} S₂ f₂) :
    P (Functor.PushoutObjObj.ofHasPushout 𝒥 f₁ f₂).ι :=
  MorphismProperty.pushoutObjObj_ι_mem_of_saturation 𝒥 P S₁ S₂ h h₁ h₂
    (hB := fun _ _ _ _ ↦ inferInstance) (hB' := fun _ _ _ _ ↦ inferInstance)

theorem mono_pushoutObjObj_ι_join {X₁ Y₁ X₂ Y₂ : DiagSet.{u}} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    [Mono f₁] [Mono f₂] :
    Mono (Functor.PushoutObjObj.ofHasPushout 𝒥 f₁ f₂).ι := by
  have : IsSaturated.{u} (monomorphisms DiagSet.{u}) := by
    rw [monomorphisms_eq_saturation_sphereInclusions]
    infer_instance
  have hf (Z Z' : DiagSet.{u}) (f : Z ⟶ Z') [Mono f] : saturation.{u} sphereInclusions f := by
    rw [← monomorphisms_eq_saturation_sphereInclusions]
    exact ‹Mono f›
  refine pushoutObjObj_ι_join_mem_of_saturation (monomorphisms _) sphereInclusions
    sphereInclusions ?_ (hf _ _ f₁) (hf _ _ f₂)
  rintro _ _ _ _ _ _ ⟨U⟩ ⟨V⟩
  exact ((monomorphisms _).arrow_mk_iso_iff (pushoutObjObjSphereInclusionArrowIso U V)).2
    (mono_sphereInclusion _)

instance mono_joinMap {X X' Y Y' : DiagSet.{u}} (f : X ⟶ X') (g : Y ⟶ Y') [Mono f] [Mono g] :
    Mono (WithInitial.joinMap f g) := by
  have : IsIso (joinInclLeft X (⊥_ DiagSet.{u})) := isIso_joinInclLeft_of_isEmpty _ _
  have : IsIso (joinInclLeft X' (⊥_ DiagSet.{u})) := isIso_joinInclLeft_of_isEmpty _ _
  have : IsIso (joinInclRight (⊥_ DiagSet.{u}) Y) := isIso_joinInclRight_of_isEmpty _ _
  have : IsIso (joinInclRight (⊥_ DiagSet.{u}) Y') := isIso_joinInclRight_of_isEmpty _ _
  have h₁ : Mono (joinMap f (𝟙 (⊥_ DiagSet.{u}))) := by
    rw [← IsIso.inv_hom_id_assoc (joinInclLeft X _) (joinMap f _), joinInclLeft_comp_joinMap]
    infer_instance
  have h₂ : Mono (joinMap (𝟙 (⊥_ DiagSet.{u})) g) := by
    rw [← IsIso.inv_hom_id_assoc (joinInclRight _ Y) (joinMap _ g), joinInclRight_comp_joinMap]
    infer_instance
  have h₁' : Mono (joinMap f (𝟙 Y)) :=
    have : Mono (((𝒥).map f).app (⊥_ DiagSet.{u})) := h₁
    have := mono_pushoutObjObj_ι_join f (initial.to Y)
    (Functor.PushoutObjObj.ofHasPushout 𝒥 f (initial.to Y)).mono_map_app_of_mono_ι
  have h₂' : Mono (joinMap (𝟙 X') g) :=
    have : Mono (((𝒥).obj (⊥_ DiagSet.{u})).map g) := h₂
    have := mono_pushoutObjObj_ι_join (initial.to X') g
    (Functor.PushoutObjObj.ofHasPushout 𝒥 (initial.to X') g).mono_obj_map_of_mono_ι
  rw [← Category.comp_id f, ← Category.id_comp g, ← WithInitial.joinMap_comp_joinMap]
  infer_instance

theorem isPullback_joinMap {K L U V : DiagSet.{u}} (i : K ⟶ L) (j : U ⟶ V) [Mono i] [Mono j] :
    IsPullback (WithInitial.joinMap (𝟙 K) j) (WithInitial.joinMap i (𝟙 U))
      (WithInitial.joinMap i (𝟙 V)) (WithInitial.joinMap (𝟙 L) j) := by
  let sq := Functor.PushoutObjObj.ofHasPushout 𝒥 i j
  have := mono_pushoutObjObj_ι_join i j
  have : Mono (((𝒥).map i).app U) := mono_joinMap i (𝟙 U)
  have hp := (Adhesive.isPullback_of_isPushout_of_mono_left sq.isPushout).flip.paste_vert
    (IsPullback.of_vert_isIso_mono (fst := sq.inl) (snd := 𝟙 _) (f := sq.ι)
      (g := sq.inl ≫ sq.ι) ⟨(Category.id_comp _).symm⟩)
  rw [Category.comp_id, sq.inr_ι, sq.inl_ι] at hp
  exact hp

instance mono_joinInclLeft (X Y : DiagSet.{u}) : Mono (joinInclLeft X Y) := by
  have : IsIso (joinInclLeft X (⊥_ DiagSet.{u})) := isIso_joinInclLeft_of_isEmpty _ _
  rw [← Category.id_comp (joinInclLeft X Y), ← joinInclLeft_comp_joinMap (𝟙 X) (initial.to Y)]
  infer_instance

instance mono_joinInclRight (X Y : DiagSet.{u}) : Mono (joinInclRight X Y) := by
  have : IsIso (joinInclRight (⊥_ DiagSet.{u}) Y) := isIso_joinInclRight_of_isEmpty _ _
  rw [← Category.id_comp (joinInclRight X Y), ← joinInclRight_comp_joinMap (initial.to X) (𝟙 Y)]
  infer_instance

theorem mono_coprodDesc_joinInclLeft_joinInclRight (X Y : DiagSet.{u}) :
    Mono (coprod.desc (joinInclLeft X Y) (joinInclRight X Y)) := by
  let sq := Functor.PushoutObjObj.ofHasPushout 𝒥 (initial.to X) (initial.to Y)
  have := mono_pushoutObjObj_ι_join (initial.to X) (initial.to Y)
  let e₁ : ⊥_ DiagSet.{u} ≅ join (⊥_ DiagSet.{u}) (⊥_ DiagSet.{u}) :=
    @asIso _ _ _ _ _ (isIso_joinInclLeft_of_isEmpty _ _)
  let e₂ : X ≅ join X (⊥_ DiagSet.{u}) := @asIso _ _ _ _ _ (isIso_joinInclLeft_of_isEmpty _ _)
  let e₃ : Y ≅ join (⊥_ DiagSet.{u}) Y := @asIso _ _ _ _ _ (isIso_joinInclRight_of_isEmpty _ _)
  have hc := sq.isPushout.of_iso' e₁ e₂ e₃ (Iso.refl _) (f' := initial.to X)
    (g' := initial.to Y) (initialIsInitial.hom_ext _ _) (initialIsInitial.hom_ext _ _)
    (Category.comp_id _).symm (Category.comp_id _).symm
  have e : coprod.desc (joinInclLeft X Y) (joinInclRight X Y) =
      ((IsPushout.of_hasBinaryCoproduct' X Y).isoIsPushout _ _ hc).hom ≫ sq.ι := by
    apply coprod.hom_ext
    · refine (coprod.inl_desc _ _).trans (Eq.trans ?_
        (IsPushout.inl_isoIsPushout_hom_assoc _ _ _ hc sq.ι).symm)
      refine Eq.trans ?_ ((Category.assoc _ _ _).trans (congrArg (e₂.hom ≫ ·) sq.inl_ι)).symm
      exact ((joinInclLeft_comp_joinMap (𝟙 X) (initial.to Y)).trans (Category.id_comp _)).symm
    · refine (coprod.inr_desc _ _).trans (Eq.trans ?_
        (IsPushout.inr_isoIsPushout_hom_assoc _ _ _ hc sq.ι).symm)
      refine Eq.trans ?_ ((Category.assoc _ _ _).trans (congrArg (e₃.hom ≫ ·) sq.inr_ι)).symm
      exact ((joinInclRight_comp_joinMap (initial.to X) (𝟙 Y)).trans (Category.id_comp _)).symm
  rw [e]
  exact @mono_comp _ _ _ _ _ _ inferInstance _ this

end Atoms.Diagrammatic
