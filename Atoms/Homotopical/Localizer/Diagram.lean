import Atoms.ForMathlib.CategoryTheory.Products.Basic
import Atoms.Homotopical.Localizer.BaseChange
import Atoms.Homotopical.Localizer.InverseImage

open CategoryTheory Limits MorphismProperty Opposite

namespace Atoms.Homotopical

universe v

variable {A : Type v} [SmallCategory A]

def pointwiseClass (J : Type v) [SmallCategory J] (W : J → MorphismProperty (Aᵒᵖ ⥤ Type v)) :
    MorphismProperty ((A × J)ᵒᵖ ⥤ Type v) :=
  ⨅ j, (W j).inverseImage (fibreRestriction J j)

section Pointwise

variable {J : Type v} [SmallCategory J]

theorem pointwiseClass_iff (W : J → MorphismProperty (Aᵒᵖ ⥤ Type v))
    {X Y : (A × J)ᵒᵖ ⥤ Type v} (f : X ⟶ Y) :
    pointwiseClass J W f ↔ ∀ j, W j ((fibreRestriction J j).map f) :=
  MorphismProperty.iInf_iff _ f

private theorem isALocalizer_pointwiseClass_of_forall (W : J → MorphismProperty (Aᵒᵖ ⥤ Type v))
    [∀ j, IsALocalizer (W j)] : IsALocalizer (pointwiseClass J W) :=
  have (j : J) := IsALocalizer.inverseImage_of_adjunction (W := W j) (fibreExtensionAdjunction J j)
  isALocalizer_iInf _

theorem isALocalizer_pointwiseClass_discrete {ι : Type v}
    (W : ι → MorphismProperty (Aᵒᵖ ⥤ Type v)) [∀ i, IsALocalizer (W i)] :
    IsALocalizer (pointwiseClass (Discrete ι) fun i ↦ W i.as) :=
  isALocalizer_pointwiseClass_of_forall _

instance isALocalizer_pointwiseClass (J : Type v) [SmallCategory J]
    (W : MorphismProperty (Aᵒᵖ ⥤ Type v)) [IsALocalizer W] :
    IsALocalizer (pointwiseClass J fun _ ↦ W) :=
  isALocalizer_pointwiseClass_of_forall _

theorem fibreExtension_map_mem_pointwiseClass (j : J) {W : J → MorphismProperty (Aᵒᵖ ⥤ Type v)}
    [∀ k, IsALocalizer (W k)] {X Y : Aᵒᵖ ⥤ Type v} (t : X ⟶ Y)
    (ht : ∀ k, (k ⟶ j) → (MorphismProperty.monomorphisms _ ⊓ W k) t) :
    (MorphismProperty.monomorphisms _ ⊓ pointwiseClass J W) ((fibreExtension J j).map t) := by
  have : Mono t := (ht j (𝟙 j)).1
  refine ⟨MorphismProperty.monomorphisms.infer_property _, (pointwiseClass_iff _ _).2 fun k ↦ ?_⟩
  refine (IsALocalizer.coproducts_le (V := W k) le_rfl _ ?_).2
  refine MorphismProperty.colimitsOfShape_le_coproducts _ (k ⟶ j) _ ?_
  exact MorphismProperty.colimitsOfShape.mk' _ _ _ _ (isColimitFibreCofan J j k X)
    (isColimitFibreCofan J j k Y) (Discrete.natTrans fun _ ↦ t) (fun s ↦ ht k s.as)
    ((fibreRestriction J k).map ((fibreExtension J j).map t)) fun _ ↦ rfl

theorem rlp_fibreRestriction_map {J : Type v} [SmallCategory J]
    {W : MorphismProperty (Aᵒᵖ ⥤ Type v)} [IsALocalizer W]
    {X Y : (A × J)ᵒᵖ ⥤ Type v} (p : X ⟶ Y)
    (hp : (monomorphisms _ ⊓ pointwiseClass J fun _ ↦ W).rlp p) (j : J) :
    (monomorphisms _ ⊓ W).rlp ((fibreRestriction J j).map p) :=
  fun _ _ t ht ↦ ((fibreExtensionAdjunction J j).hasLiftingProperty_iff t p).1
    (hp _ (fibreExtension_map_mem_pointwiseClass j t fun _ _ ↦ ht))

instance isRightProper_pointwiseClass (J : Type v) [SmallCategory J]
    (W : MorphismProperty (Aᵒᵖ ⥤ Type v)) [IsALocalizer W] [IsRightProper W] :
    IsRightProper (pointwiseClass J fun _ ↦ W) where
  weakFibration_of_rlp p hp K L f b hf := by
    rw [pointwiseClass_iff] at hf ⊢
    intro j
    have hW := IsRightProper.weakFibration_of_rlp _ (rlp_fibreRestriction_map p hp j) _
      ((fibreRestriction J j).map b) (hf j)
    exact (mem_iff_of_isPullback W
      (isPullback_baseChangeMap _ ((fibreRestriction J j).map b) _)
      ((isPullback_baseChangeMap f b p).map (fibreRestriction J j))
      (PreservesPullback.iso _ b p) (PreservesPullback.iso_hom_fst _ b p)).2 hW

end Pointwise

section Discrete

variable {ι : Type v}

private def homOfFibres {X Y : (A × Discrete ι)ᵒᵖ ⥤ Type v}
    (l : ∀ i : ι, (fibreRestriction (Discrete ι) ⟨i⟩).obj X ⟶
      (fibreRestriction (Discrete ι) ⟨i⟩).obj Y) : X ⟶ Y where
  app x := (l x.unop.2.as).app (op x.unop.1)
  naturality x y g := by
    obtain ⟨⟨a, ⟨i⟩⟩⟩ := x
    obtain ⟨⟨b, ⟨i'⟩⟩⟩ := y
    have h := Discrete.eq_of_hom g.unop.2
    subst h
    have hg : g = (Prod.sectL A (⟨i'⟩ : Discrete ι)).op.map g.unop.1.op := by
      refine Quiver.Hom.unop_inj ?_
      exact Prod.ext rfl (Subsingleton.elim _ _)
    rw [hg]
    exact (l i').naturality g.unop.1.op

private theorem hasLiftingProperty_of_fibreRestriction
    {X Y E B : (A × Discrete ι)ᵒᵖ ⥤ Type v} (f : X ⟶ Y) (p : E ⟶ B)
    (h : ∀ i : ι, HasLiftingProperty ((fibreRestriction (Discrete ι) ⟨i⟩).map f)
      ((fibreRestriction (Discrete ι) ⟨i⟩).map p)) : HasLiftingProperty f p where
  sq_hasLift {u v} sq :=
    let l (i : ι) := have := h i; (sq.map (fibreRestriction (Discrete ι) ⟨i⟩)).lift
    ⟨⟨{ l := homOfFibres l
        fac_left := hom_ext_fibreRestriction _ fun k ↦ by
          have := h k.as
          rw [Functor.map_comp]
          exact (sq.map (fibreRestriction (Discrete ι) ⟨k.as⟩)).fac_left
        fac_right := hom_ext_fibreRestriction _ fun k ↦ by
          have := h k.as
          rw [Functor.map_comp]
          exact (sq.map (fibreRestriction (Discrete ι) ⟨k.as⟩)).fac_right }⟩⟩

theorem isAccessibleALocalizer_pointwiseClass_discrete
    (W : ι → MorphismProperty (Aᵒᵖ ⥤ Type v)) [∀ i, IsAccessibleALocalizer (W i)] :
    IsAccessibleALocalizer (pointwiseClass (Discrete ι) fun i ↦ W i.as) := by
  have := isALocalizer_pointwiseClass_discrete W
  choose T hT hTW using fun i ↦
    (inferInstance : IsAccessibleALocalizer (W i)).exists_trivialCofibrations_eq_saturation
  refine IsALocalizer.isAccessibleALocalizer_of_eq_saturation
    (J := ⨆ i, functorImage (fibreExtension (Discrete ι) ⟨i⟩) (T i)) (le_antisymm ?_ ?_)
  · rw [saturation_eq_llp_rlp]
    intro X Y f hf E B p hp
    refine hasLiftingProperty_of_fibreRestriction f p fun i ↦ ?_
    have hfi : saturation.{v} (T i) ((fibreRestriction _ ⟨i⟩).map f) := by
      have : Mono f := hf.1
      rw [← hTW i]
      exact ⟨MorphismProperty.monomorphisms.infer_property _,
        (pointwiseClass_iff _ f).1 hf.2 ⟨i⟩⟩
    refine saturation_le _ _ (MorphismProperty.le_llp_rlp _) _ hfi _ fun K L t ht ↦ ?_
    exact ((fibreExtensionAdjunction _ ⟨i⟩).hasLiftingProperty_iff t p).1
      (hp _ ((MorphismProperty.iSup_iff _ _).2 ⟨i, K, L, t, ht, rfl⟩))
  · refine saturation_le _ _ fun X Y g hg ↦ ?_
    obtain ⟨i, K, L, t, ht, e⟩ := (MorphismProperty.iSup_iff _ _).1 hg
    refine ((MorphismProperty.monomorphisms _ ⊓ _).arrow_mk_iso_iff (eqToIso e)).1 ?_
    refine fibreExtension_map_mem_pointwiseClass _ t fun k hk ↦ ?_
    obtain ⟨k⟩ := k
    obtain rfl : k = i := Discrete.eq_of_hom hk
    exact hTW k ▸ le_saturation (T k) t ht

theorem isAccessibleALocalizer_iInf
    (W : ι → MorphismProperty (Aᵒᵖ ⥤ Type v)) [∀ i, IsAccessibleALocalizer (W i)] :
    IsAccessibleALocalizer (⨅ i, W i) := by
  have hδ : (pointwiseClass (Discrete ι) fun i ↦ W i.as).inverseImage
      ((Functor.whiskeringLeft _ _ (Type v)).obj (CategoryTheory.Prod.fst A (Discrete ι)).op) =
        ⨅ i, W i := by
    ext X Y f
    rw [MorphismProperty.inverseImage_iff, pointwiseClass_iff, MorphismProperty.iInf_iff]
    exact ⟨fun h i ↦ h ⟨i⟩, fun h i ↦ h i.as⟩
  have := isAccessibleALocalizer_pointwiseClass_discrete W
  have : IsALocalizer ((pointwiseClass (Discrete ι) fun i ↦ W i.as).inverseImage
      ((Functor.whiskeringLeft _ _ (Type v)).obj (CategoryTheory.Prod.fst A (Discrete ι)).op)) :=
    hδ ▸ isALocalizer_iInf W
  rw [← hδ]
  refine IsAccessibleALocalizer.inverseImage _ fun f hf ↦ ?_
  rw [NatTrans.mono_iff_mono_app] at hf ⊢
  exact fun _ ↦ hf _

end Discrete

instance isAccessibleALocalizer_pointwiseClass (J : Type v) [SmallCategory J]
    (W : MorphismProperty (Aᵒᵖ ⥤ Type v)) [IsAccessibleALocalizer W] :
    IsAccessibleALocalizer (pointwiseClass J fun _ ↦ W) :=
  have (j : J) : IsALocalizer (W.inverseImage (fibreRestriction J j)) :=
    IsALocalizer.inverseImage_of_adjunction (fibreExtensionAdjunction J j)
  have (j : J) : IsAccessibleALocalizer (W.inverseImage (fibreRestriction J j)) :=
    IsAccessibleALocalizer.inverseImage _ fun f hf ↦ have : Mono f := hf; Functor.map_mono _ f
  isAccessibleALocalizer_iInf (A := A × J) _

end Atoms.Homotopical
