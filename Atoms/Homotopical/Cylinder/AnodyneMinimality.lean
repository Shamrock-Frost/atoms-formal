import Atoms.Homotopical.Cylinder.AbsoluteWeakEquivalence
import Atoms.Homotopical.Localizer.LeftProper
import Atoms.ForMathlib.CategoryTheory.Limits.FunctorToTypes
import Atoms.ForMathlib.CategoryTheory.Subfunctor.Basic

open CategoryTheory Limits MorphismProperty

namespace Atoms.Homotopical

universe w v

variable {A : Type v} [SmallCategory A]

section MonoSaturated

variable {B : Type v} [SmallCategory B]
  {Φ Ψ : (Bᵒᵖ ⥤ Type (max w v)) ⥤ (Aᵒᵖ ⥤ Type (max w v))} (α : Φ ⟶ Ψ)
  {C : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))}

private theorem mem_app_of_isPushout [PreservesColimitsOfShape WalkingSpan Φ]
    [PreservesColimitsOfShape WalkingSpan Ψ] [C.IsStableUnderCobaseChange]
    [C.IsStableUnderComposition] (hα : ∀ X, Mono (α.app X))
    (hΨ : ∀ {X Y : Bᵒᵖ ⥤ Type (max w v)} (f : X ⟶ Y), Mono f → Mono (Ψ.map f))
    (hcart : ∀ {X Y : Bᵒᵖ ⥤ Type (max w v)} (i : X ⟶ Y), Mono i →
      IsPullback (Φ.map i) (α.app X) (α.app Y) (Ψ.map i))
    (hP : ∀ ⦃X Y Z : Aᵒᵖ ⥤ Type (max w v)⦄ (f : X ⟶ Y) (g : Y ⟶ Z),
      Mono g → C f → C (f ≫ g) → C g)
    {X₀ X₁ X₂ X₃ : Bᵒᵖ ⥤ Type (max w v)} {f₁ : X₀ ⟶ X₁} {f₂ : X₀ ⟶ X₂} {g₁ : X₁ ⟶ X₃}
    {g₂ : X₂ ⟶ X₃} (h : IsPushout f₁ f₂ g₁ g₂) [Mono f₁] (h₀ : C (α.app X₀))
    (h₁ : C (α.app X₁)) (h₂ : C (α.app X₂)) : C (α.app X₃) := by
  have hpb := (hcart f₁ inferInstance).flip
  have := hα X₁
  have := hΨ f₁ inferInstance
  have hm : Mono (pushout.desc (Ψ.map f₁) (α.app X₁) hpb.w) :=
    HasEffectiveUnions.mono_pushoutDesc hpb
  have hC₁ : C (pushout.desc (Ψ.map f₁) (α.app X₁) hpb.w) :=
    hP (pushout.inr _ _) _ hm (C.of_isPushout (IsPushout.of_hasPushout _ _).flip h₀)
      (by rwa [pushout.inr_desc])
  have w₂ : α.app X₂ ≫ Ψ.map g₂ = Φ.map g₂ ≫ α.app X₃ := (α.naturality g₂).symm
  have wk : α.app X₀ ≫ Ψ.map f₂ ≫ pushout.inl (α.app X₂) (Φ.map g₂) =
      Φ.map f₁ ≫ Φ.map g₁ ≫ pushout.inr _ _ := by
    rw [← α.naturality_assoc f₂, pushout.condition, ← Φ.map_comp_assoc, ← Φ.map_comp_assoc,
      h.w]
  have hF := Φ.map_isPushout h.flip
  have hG := Ψ.map_isPushout h
  have outer : IsPushout (α.app X₀ ≫ Ψ.map f₂) (Φ.map f₁) (pushout.inl _ _)
      (pushout.inr (α.app X₀) (Φ.map f₁) ≫ pushout.desc _ _ wk) := by
    rw [← α.naturality f₂, pushout.inr_desc]
    exact hF.paste_horiz (IsPushout.of_hasPushout (α.app X₂) (Φ.map g₂))
  have left : IsPushout (Ψ.map f₂) (pushout.inl _ _) (pushout.inl _ _) (pushout.desc _ _ wk) :=
    ((IsPushout.of_hasPushout (α.app X₀) (Φ.map f₁)).paste_horiz_iff
      (pushout.inl_desc _ _ _).symm).1 outer
  have cube : IsPushout (pushout.desc _ _ wk) (pushout.desc (Ψ.map f₁) (α.app X₁) hpb.w)
      (pushout.desc (Ψ.map g₂) (α.app X₃) w₂) (Ψ.map g₁) := by
    refine (left.flip.paste_horiz_iff (pushout.hom_ext ?_ ?_)).1 ?_ |>.flip
    · rw [pushout.inl_desc_assoc, pushout.inl_desc_assoc, Category.assoc, pushout.inl_desc,
        ← Ψ.map_comp, ← Ψ.map_comp, h.w]
    · rw [pushout.inr_desc_assoc, pushout.inr_desc_assoc, Category.assoc, pushout.inr_desc]
      exact (α.naturality g₁).symm
    rw [pushout.inl_desc, pushout.inl_desc]
    exact hG
  rw [← pushout.inr_desc (Ψ.map g₂) (α.app X₃) w₂]
  exact C.comp_mem _ _ (C.of_isPushout (IsPushout.of_hasPushout _ _).flip h₂)
    (C.of_isPushout cube hC₁)

private theorem mem_app_iff_homOfLe [C.RespectsIso] (hα : ∀ X, Mono (α.app X))
    (hΨ : ∀ {X Y : Bᵒᵖ ⥤ Type (max w v)} (f : X ⟶ Y), Mono f → Mono (Ψ.map f))
    (hcart : ∀ {X Y : Bᵒᵖ ⥤ Type (max w v)} (i : X ⟶ Y), Mono i →
      IsPullback (Φ.map i) (α.app X) (α.app Y) (Ψ.map i))
    {X Y : Bᵒᵖ ⥤ Type (max w v)} (m : Y ⟶ X) [Mono m] :
    C (α.app Y) ↔ C (Subfunctor.homOfLe (inf_le_right :
      Subfunctor.range (α.app X) ⊓ Subfunctor.range (Ψ.map m) ≤ Subfunctor.range (Ψ.map m))) := by
  have := hα Y
  have := hΨ m inferInstance
  have hr : Subfunctor.range (α.app Y ≫ Ψ.map m) =
      Subfunctor.range (α.app X) ⊓ Subfunctor.range (Ψ.map m) := by
    refine Subfunctor.ext (funext fun a ↦ Set.ext fun q ↦ ⟨?_, ?_⟩)
    · rintro ⟨p, rfl⟩
      refine ⟨⟨(Φ.map m).app a p, ?_⟩, ⟨(α.app Y).app a p, rfl⟩⟩
      rw [← α.naturality m]
      rfl
    · rintro ⟨⟨p, rfl⟩, ⟨r, hr⟩⟩
      obtain ⟨t, -, rfl⟩ := ((Types.isPullback_iff _ _ _ _).1
        ((hcart m inferInstance).map ((evaluation _ _).obj a))).2.2 p r hr.symm
      exact ⟨t, hr⟩
  refine C.arrow_mk_iso_iff (Arrow.isoMk (asIso (Subfunctor.toRange (α.app Y ≫ Ψ.map m)) ≪≫
    Subfunctor.isoOfEq hr) (asIso (Subfunctor.toRange (Ψ.map m))) ?_)
  rw [← cancel_mono (Subfunctor.range (Ψ.map m)).ι]
  simp [Subfunctor.isoOfEq]

end MonoSaturated

section Chain

variable {Q : Aᵒᵖ ⥤ Type (max w v)} {C : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))}

private theorem mem_homOfLe_sup_sup [C.IsStableUnderCobaseChange]
    (hP : ∀ ⦃X Y Z : Aᵒᵖ ⥤ Type (max w v)⦄ (f : X ⟶ Y) (g : Y ⟶ Z),
      Mono g → C f → C (f ≫ g) → C g)
    {s t u b : Subfunctor Q} (hub : u ≤ b) (hbt : b ≤ t)
    (hu : C (Subfunctor.homOfLe (inf_le_right : s ⊓ u ≤ u)))
    (hb : C (Subfunctor.homOfLe (inf_le_right : s ⊓ b ≤ b))) :
    C (Subfunctor.homOfLe (le_sup_left : s ⊓ t ⊔ u ≤ s ⊓ t ⊔ u ⊔ b)) := by
  have h₁ : C (Subfunctor.homOfLe (le_sup_left : s ⊓ b ≤ s ⊓ b ⊔ u)) :=
    C.of_isPushout (Subfunctor.isPushout_of_bicartSq (A₁ := s ⊓ u) (A₂ := u) (A₃ := s ⊓ b)
      ⟨sup_comm _ _, ?_⟩).flip hu
  · have h₂ : C (Subfunctor.homOfLe (sup_le inf_le_right hub : s ⊓ b ⊔ u ≤ b)) :=
      hP _ _ inferInstance h₁ hb
    refine C.of_isPushout (Subfunctor.isPushout_of_bicartSq (A₁ := s ⊓ b ⊔ u)
      (A₂ := s ⊓ t ⊔ u) (A₃ := b) ⟨rfl, ?_⟩) h₂
    refine Subfunctor.ext (funext fun a ↦ Set.ext fun q ↦ ?_)
    have h₁ : q ∈ u.obj a → q ∈ b.obj a := fun hq ↦ hub a hq
    have h₂ : q ∈ b.obj a → q ∈ t.obj a := fun hq ↦ hbt a hq
    simp only [Subfunctor.max_obj, Subfunctor.min_obj, Set.mem_union, Set.mem_inter_iff]
    tauto
  · refine Subfunctor.ext (funext fun a ↦ Set.ext fun q ↦ ?_)
    have h₁ : q ∈ u.obj a → q ∈ b.obj a := fun hq ↦ hub a hq
    simp only [Subfunctor.min_obj, Set.mem_inter_iff]
    tauto

private theorem mem_homOfLe_iSup [C.IsStableUnderCobaseChange]
    [C.IsStableUnderTransfiniteComposition.{max w v}]
    (hP : ∀ ⦃X Y Z : Aᵒᵖ ⥤ Type (max w v)⦄ (f : X ⟶ Y) (g : Y ⟶ Z),
      Mono g → C f → C (f ≫ g) → C g)
    {J : Type (max w v)} [LinearOrder J] [WellFoundedLT J] (s : Subfunctor Q)
    (b : J → Subfunctor Q) (hb : Monotone b)
    (h : ∀ j, C (Subfunctor.homOfLe (inf_le_right : s ⊓ b j ≤ b j))) :
    C (Subfunctor.homOfLe (inf_le_right : s ⊓ ⨆ j, b j ≤ ⨆ j, b j)) := by
  classical
  let := WellFoundedLT.toOrderBot (WithTop J)
  let := SuccOrder.ofLinearWellFoundedLT (WithTop J)
  let U : WithTop J → Subfunctor Q := fun x ↦ ⨆ (z : J) (_ : (z : WithTop J) < x), b z
  have hbU : ∀ {z : J} {x : WithTop J}, (z : WithTop J) < x → b z ≤ U x :=
    fun {z} _ hz ↦ le_iSup₂_of_le (f := fun (z : J) (_ : (z : WithTop J) < _) ↦ b z) z hz le_rfl
  have hUb : ∀ z : J, U z ≤ b z := fun z ↦ iSup₂_le fun _ hz ↦ hb (WithTop.coe_lt_coe.1 hz).le
  have key : ∀ x, C (Subfunctor.homOfLe (inf_le_right : s ⊓ U x ≤ U x)) := by
    intro x
    induction x using WellFoundedLT.induction with
    | _ x ih =>
    let T : J → Subfunctor Q := fun z ↦ if (z : WithTop J) < x then b z else ⊥
    let F : WithTop J → Subfunctor Q :=
      fun y ↦ s ⊓ U x ⊔ ⨆ (z : J) (_ : (z : WithTop J) < y), T z
    have hF : IsUnionChain (s ⊓ U x) T F := fun _ ↦ rfl
    have hFz : ∀ z : J, (z : WithTop J) < x → F z = s ⊓ U x ⊔ U z := fun z hz ↦
      congrArg (s ⊓ U x ⊔ ·) (iSup_congr fun _ ↦ iSup_congr fun hz' ↦ if_pos (hz'.trans hz))
    have htop : F ⊤ = U x := by
      refine le_antisymm (sup_le inf_le_right (iSup₂_le fun z _ ↦ ?_))
        (le_sup_of_le_right (iSup₂_le fun z hz ↦ le_iSup₂_of_le z (WithTop.coe_lt_top z) ?_))
      · by_cases hz : (z : WithTop J) < x
        · simpa only [T, if_pos hz] using hbU hz
        · simp only [T, if_neg hz, bot_le]
      · simp only [T, if_pos hz, le_refl]
    have hcomp := transfiniteCompositionsOfShape_le C _ _
      (Subfunctor.transfiniteCompositionsOfShape_homOfLe C F hF.mono
        (fun _ hm ↦ hF.eq_iSup_of_isSuccLimit hm) fun y hy ↦ ?_)
    · exact (Subfunctor.homOfLe_mem_iff_of_eq C _ _ hF.bot htop).1 hcomp
    induction y using WithTop.recTopCoe with
    | top => exact absurd isMax_top hy
    | coe z =>
    by_cases hz : (z : WithTop J) < x
    · refine (Subfunctor.homOfLe_mem_iff_of_eq C _ le_sup_left (hFz z hz) ?_).2
        (mem_homOfLe_sup_sup hP (hUb z) (hbU hz) (ih z hz) (h z))
      rw [hF.succ, hFz z hz]
      simp only [T, if_pos hz]
    · refine (Subfunctor.homOfLe_mem_iff_of_eq C _ le_rfl rfl ?_).2 (C.id_mem _)
      rw [hF.succ]
      simp only [T, if_neg hz, sup_bot_eq]
  have hU : U ⊤ = ⨆ j, b j := iSup_congr fun z ↦ iSup_pos (WithTop.coe_lt_top z)
  exact (Subfunctor.homOfLe_mem_iff_of_eq C _ _ (by rw [hU]) hU).1 (key ⊤)

end Chain

theorem isMonoSaturatedClass_app_of_isPullback {B : Type v} [SmallCategory B]
    (Φ Ψ : (Bᵒᵖ ⥤ Type (max w v)) ⥤ (Aᵒᵖ ⥤ Type (max w v)))
    [PreservesColimitsOfSize.{max w v, max w v} Φ] [PreservesColimitsOfSize.{max w v, max w v} Ψ]
    (hΨ : ∀ {X Y : Bᵒᵖ ⥤ Type (max w v)} (f : X ⟶ Y), Mono f → Mono (Ψ.map f))
    (α : Φ ⟶ Ψ) (hα : ∀ X, Mono (α.app X))
    (hcart : ∀ {X Y : Bᵒᵖ ⥤ Type (max w v)} (i : X ⟶ Y), Mono i →
      IsPullback (Φ.map i) (α.app X) (α.app Y) (Ψ.map i))
    (C : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))) [C.IsStableUnderCobaseChange]
    [C.IsStableUnderTransfiniteComposition.{max w v}]
    (hP : ∀ ⦃X Y Z : Aᵒᵖ ⥤ Type (max w v)⦄ (f : X ⟶ Y) (g : Y ⟶ Z),
      Mono g → C f → C (f ≫ g) → C g) :
    IsMonoSaturatedClass (fun X ↦ C (α.app X)) where
  of_isPushout h _ h₀ h₁ h₂ := by
    have := preservesSmallestColimits_of_preservesColimits Φ
    have := preservesSmallestColimits_of_preservesColimits Ψ
    exact mem_app_of_isPushout α hα hΨ hcart hP h h₀ h₁ h₂
  of_isColimit J _ _ F hF c hc h := by
    have hm : ∀ j, Mono (c.ι.app j) := fun j ↦ (NatTrans.mono_iff_mono_app _).2 fun a ↦
      (mono_iff_injective _).2
        (CategoryTheory.FunctorToTypes.injective_colimit_ι_app_app F hF hc a.unop j)
    have hc' := isColimitOfPreserves Ψ hc
    have hsup : ⨆ j, Subfunctor.range (Ψ.map (c.ι.app j)) = Subfunctor.range (Ψ.map (𝟙 c.pt)) := by
      have hd := Subfunctor.range_desc_of_isColimit hc' (Ψ.mapCocone c)
      rw [hc'.desc_self] at hd
      rw [Ψ.map_id]
      exact hd.symm
    refine (mem_app_iff_homOfLe α hα hΨ hcart (𝟙 c.pt)).2
      ((Subfunctor.homOfLe_mem_iff_of_eq C _ _ (by rw [hsup]) hsup).1
        (mem_homOfLe_iSup hP _ _ (fun i j hij ↦ ?_) fun j ↦
          (mem_app_iff_homOfLe α hα hΨ hcart (c.ι.app j)).1 (h j)))
    rw [← c.w (homOfLE hij), Ψ.map_comp]
    exact Subfunctor.range_comp_le _ _

end Atoms.Homotopical

namespace HomotopicalAlgebra.ExactCylinder

open Atoms.Homotopical

universe w v

variable {A : Type v} [SmallCategory A]

theorem anodyne_le_of_isStable (𝕀 : ExactCylinder.{max w v} (Aᵒᵖ ⥤ Type (max w v)))
    (S : MorphismProperty (Aᵒᵖ ⥤ Type (max w v)))
    (hS : S ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)))
    (M : MorphismProperty (Aᵒᵖ ⥤ Type (max w v)))
    (hM : saturation.{max w v} M = MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)))
    (C : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))) [C.IsStableUnderCobaseChange]
    [C.IsStableUnderTransfiniteComposition.{max w v}] [C.IsStableUnderRetracts]
    (hcancel : ∀ ⦃X Y Z : Aᵒᵖ ⥤ Type (max w v)⦄ (f : X ⟶ Y) (g : Y ⟶ Z),
      Mono f → Mono g → C f → C (f ≫ g) → C g)
    (hend : ∀ (ε : Bool) {K L : Aᵒᵖ ⥤ Type (max w v)} (t : K ⟶ L), M t →
      C ((𝕀.endpoint ε).app K) ∧ C ((𝕀.endpoint ε).app L))
    (hSC : S ≤ C) :
    𝕀.anodyne S ≤ C := by
  have : IsSaturated.{max w v} C :=
    { isStableUnderCobaseChange := inferInstance
      isStableUnderTransfiniteComposition := inferInstance
      isStableUnderRetracts := inferInstance }
  have hP : ∀ ⦃X Y Z : Aᵒᵖ ⥤ Type (max w v)⦄ (f : X ⟶ Y) (g : Y ⟶ Z), Mono g →
      (C ⊓ MorphismProperty.monomorphisms _) f → (C ⊓ MorphismProperty.monomorphisms _) (f ≫ g) →
      (C ⊓ MorphismProperty.monomorphisms _) g :=
    fun _ _ _ f g hg hf hfg ↦ ⟨hcancel f g hf.2 hg hf.1 hfg.1, hg⟩
  have hend' (ε : Bool) (X : Aᵒᵖ ⥤ Type (max w v)) :
      (C ⊓ MorphismProperty.monomorphisms _) ((𝕀.endpoint ε).app X) :=
    forall_of_saturation_eq (isMonoSaturatedClass_app_of_isPullback (𝟭 _) 𝕀.I
      (fun f _ ↦ 𝕀.I.map_mono f) (𝕀.endpoint ε) (𝕀.mono_endpoint ε)
      (fun i _ ↦ (𝕀.isPullback_endpoint ε i).flip) _ hP)
      (fun i r h hY ↦ (C ⊓ MorphismProperty.monomorphisms _).of_retract
        (NatTrans.retractArrowApp (𝕀.endpoint ε) ⟨i, r, h⟩) hY)
      M hM (fun t ht ↦ ⟨⟨(hend ε t ht).1, 𝕀.mono_endpoint ε _⟩,
        ⟨(hend ε t ht).2, 𝕀.mono_endpoint ε _⟩⟩) X
  rw [𝕀.anodyne_eq_saturation_anodyneGenerators S hS]
  exact (saturation_le _ _ (𝕀.anodyneGenerators_le_of_endpoint_mem S _ inf_le_right hP hend'
    fun _ _ f hf ↦ ⟨hSC f hf, hS f hf⟩)).trans inf_le_left

section Slice

variable {T : Aᵒᵖ ⥤ Type v}

private theorem map_homMk_comp_map_homMk {X₀ X₁ X₂ X₃ : Aᵒᵖ ⥤ Type v} {t₀ : X₀ ⟶ T}
    {t₁ : X₁ ⟶ T} {t₂ : X₂ ⟶ T} {t₃ : X₃ ⟶ T} {a : X₀ ⟶ X₁} {b : X₁ ⟶ X₃} {c : X₀ ⟶ X₂}
    {d : X₂ ⟶ X₃} {ha : a ≫ t₁ = t₀} {hb : b ≫ t₃ = t₁} {hc : c ≫ t₂ = t₀} {hd : d ≫ t₃ = t₂}
    (h : a ≫ b = c ≫ d) :
    (overEquivPresheafCostructuredArrow T).functor.map
        (Over.homMk a ha : Over.mk t₀ ⟶ Over.mk t₁) ≫
      (overEquivPresheafCostructuredArrow T).functor.map
        (Over.homMk b hb : Over.mk t₁ ⟶ Over.mk t₃) =
    (overEquivPresheafCostructuredArrow T).functor.map
        (Over.homMk c hc : Over.mk t₀ ⟶ Over.mk t₂) ≫
      (overEquivPresheafCostructuredArrow T).functor.map
        (Over.homMk d hd : Over.mk t₂ ⟶ Over.mk t₃) := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg _ (Over.OverMorphism.ext (by simpa using h))

private theorem isPushout_map_homMk {X₀ X₁ X₂ X₃ : Aᵒᵖ ⥤ Type v} {f₁ : X₀ ⟶ X₁} {f₂ : X₀ ⟶ X₂}
    {g₁ : X₁ ⟶ X₃} {g₂ : X₂ ⟶ X₃} (h : IsPushout f₁ f₂ g₁ g₂) (t₀ : X₀ ⟶ T) (t₁ : X₁ ⟶ T)
    (t₂ : X₂ ⟶ T) (t₃ : X₃ ⟶ T) (e₁ : f₁ ≫ t₁ = t₀) (e₂ : f₂ ≫ t₂ = t₀) (e₁' : g₁ ≫ t₃ = t₁)
    (e₂' : g₂ ≫ t₃ = t₂) :
    IsPushout
      ((overEquivPresheafCostructuredArrow T).functor.map
        (Over.homMk f₁ e₁ : Over.mk t₀ ⟶ Over.mk t₁))
      ((overEquivPresheafCostructuredArrow T).functor.map
        (Over.homMk f₂ e₂ : Over.mk t₀ ⟶ Over.mk t₂))
      ((overEquivPresheafCostructuredArrow T).functor.map
        (Over.homMk g₁ e₁' : Over.mk t₁ ⟶ Over.mk t₃))
      ((overEquivPresheafCostructuredArrow T).functor.map
        (Over.homMk g₂ e₂' : Over.mk t₂ ⟶ Over.mk t₃)) :=
  (overEquivPresheafCostructuredArrow T).functor.map_isPushout
    (IsPushout.of_map (Over.forget T) (Over.OverMorphism.ext (by simpa using h.w)) h)

private def retractArrowOver {X Y X' Y' : Aᵒᵖ ⥤ Type v} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (h : RetractArrow f g) (l : Y ⟶ T) :
    RetractArrow (Over.homMk f : Over.mk (f ≫ l) ⟶ Over.mk l)
      (Over.homMk g : Over.mk (g ≫ h.r.right ≫ l) ⟶ Over.mk (h.r.right ≫ l)) where
  i := Arrow.homMk (Over.homMk h.i.left (by simp [h.i_w_assoc]))
    (Over.homMk h.i.right (by simp)) (Over.OverMorphism.ext (by simp))
  r := Arrow.homMk (Over.homMk h.r.left (by simp [h.r_w_assoc])) (Over.homMk h.r.right)
    (Over.OverMorphism.ext (by simp))
  retract := by ext <;> simp

end Slice

instance isStableUnderRetracts_overWeakEquivalences (𝕀 : ExactCylinder.{v} (Aᵒᵖ ⥤ Type v))
    (S : MorphismProperty (Aᵒᵖ ⥤ Type v)) (X : Aᵒᵖ ⥤ Type v) :
    (𝕀.overWeakEquivalences S X).IsStableUnderRetracts :=
  inferInstanceAs (((𝕀.over X).weakEquivalences
    (sliceGenerators (𝕀.anodyneGenerators S) X)).IsStableUnderRetracts)

variable (𝕀 : ExactCylinder.{v} (Aᵒᵖ ⥤ Type v)) (S : MorphismProperty (Aᵒᵖ ⥤ Type v))

private theorem isALocalizer_overWeakEquivalences [S.IsSmall.{v}]
    (hS : S ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v)) (T : Aᵒᵖ ⥤ Type v) :
    IsALocalizer (𝕀.overWeakEquivalences S T) := by
  have := 𝕀.isSmall_anodyneGenerators S
  rw [← 𝕀.weakEquivalences_over_eq_of_eq_saturation S _ hS
    (𝕀.anodyne_eq_saturation_anodyneGenerators S hS) T]
  exact (𝕀.over T).isALocalizer_weakEquivalences _
    (sliceGenerators_le_monomorphisms _ (𝕀.anodyneGenerators_le_monomorphisms S hS) T)

theorem absoluteWeakEquivalences_of_isPushout_of_mono [S.IsSmall.{v}]
    (hS : S ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v))
    {F₀ F₁ F₂ F' G₀ G₁ G₂ G' : Aᵒᵖ ⥤ Type v}
    {φ₁ : F₀ ⟶ F₁} {φ₂ : F₀ ⟶ F₂} {ε₁ : F₁ ⟶ F'} {ε₂ : F₂ ⟶ F'}
    {ψ₁ : G₀ ⟶ G₁} {ψ₂ : G₀ ⟶ G₂} {η₁ : G₁ ⟶ G'} {η₂ : G₂ ⟶ G'}
    (hF : IsPushout φ₁ φ₂ ε₁ ε₂) (hG : IsPushout ψ₁ ψ₂ η₁ η₂) [Mono φ₁] [Mono ψ₁]
    (χ₀ : F₀ ⟶ G₀) (χ₁ : F₁ ⟶ G₁) (χ₂ : F₂ ⟶ G₂) (χ' : F' ⟶ G')
    (h₁ : φ₁ ≫ χ₁ = χ₀ ≫ ψ₁) (h₂ : φ₂ ≫ χ₂ = χ₀ ≫ ψ₂)
    (h₁' : ε₁ ≫ χ' = χ₁ ≫ η₁) (h₂' : ε₂ ≫ χ' = χ₂ ≫ η₂)
    (hχ₀ : 𝕀.absoluteWeakEquivalences S χ₀) (hχ₁ : 𝕀.absoluteWeakEquivalences S χ₁)
    (hχ₂ : 𝕀.absoluteWeakEquivalences S χ₂) :
    𝕀.absoluteWeakEquivalences S χ' := by
  intro T l
  have := 𝕀.isALocalizer_overWeakEquivalences S hS T
  have e : ψ₂ ≫ η₂ ≫ l = ψ₁ ≫ η₁ ≫ l := by rw [hG.w_assoc]
  have e₁ : φ₁ ≫ χ₁ ≫ η₁ ≫ l = χ₀ ≫ ψ₁ ≫ η₁ ≫ l := by rw [reassoc_of% h₁]
  have e₂ : φ₂ ≫ χ₂ ≫ η₂ ≫ l = χ₀ ≫ ψ₁ ≫ η₁ ≫ l := by rw [reassoc_of% h₂, e]
  have : Mono (Over.homMk φ₁ e₁ : Over.mk _ ⟶ Over.mk _) :=
    Over.mono_of_mono_left _ (hk := ‹Mono φ₁›)
  have : Mono (Over.homMk ψ₁ rfl : Over.mk (ψ₁ ≫ η₁ ≫ l) ⟶ Over.mk (η₁ ≫ l)) :=
    Over.mono_of_mono_left _ (hk := ‹Mono ψ₁›)
  exact IsALocalizer.of_isPushout_of_mono
    (isPushout_map_homMk hF _ _ _ (χ' ≫ l) e₁ e₂ (by rw [reassoc_of% h₁'])
      (by rw [reassoc_of% h₂']))
    (isPushout_map_homMk hG _ _ _ l rfl e rfl rfl) (sliceHom χ₀ (ψ₁ ≫ η₁ ≫ l))
    (sliceHom χ₁ (η₁ ≫ l)) (sliceHom χ₂ (η₂ ≫ l)) (sliceHom χ' l)
    (map_homMk_comp_map_homMk h₁) (map_homMk_comp_map_homMk h₂)
    (map_homMk_comp_map_homMk h₁') (map_homMk_comp_map_homMk h₂') (hχ₀ T _) (hχ₁ T _) (hχ₂ T _)

theorem absoluteWeakEquivalences_of_isColimit [S.IsSmall.{v}]
    (hS : S ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v))
    {J : Type v} [LinearOrder J] [WellFoundedLT J] {X Y : J ⥤ Aᵒᵖ ⥤ Type v}
    (hX : ∀ (i j : J) (h : i ≤ j), Mono (X.map (homOfLE h)))
    (hY : ∀ (i j : J) (h : i ≤ j), Mono (Y.map (homOfLE h)))
    (φ : X ⟶ Y) (hφ : ∀ j, 𝕀.absoluteWeakEquivalences S (φ.app j))
    {cX : Cocone X} {cY : Cocone Y} (hcX : IsColimit cX) (hcY : IsColimit cY)
    (f : cX.pt ⟶ cY.pt) (hf : ∀ j, cX.ι.app j ≫ f = φ.app j ≫ cY.ι.app j) :
    𝕀.absoluteWeakEquivalences S f := by
  intro T l
  have := 𝕀.isALocalizer_overWeakEquivalences S hS T
  let E := (overEquivPresheafCostructuredArrow T).functor
  let Y' := Y.toOver T (fun j ↦ cY.ι.app j ≫ l) fun g ↦ cY.w_assoc g l
  let X' := X.toOver T (fun j ↦ φ.app j ≫ cY.ι.app j ≫ l) fun g ↦ by
    rw [φ.naturality_assoc, cY.w_assoc]
  let φ' : X' ⟶ Y' :=
    { app j := Over.homMk (φ.app j)
      naturality _ _ g := Over.OverMorphism.ext (φ.naturality g) }
  have hfl (j : J) : cX.ι.app j ≫ f ≫ l = φ.app j ≫ cY.ι.app j ≫ l := by
    rw [reassoc_of% (hf j)]
  let cX' : Cocone X' :=
    { pt := Over.mk (f ≫ l)
      ι :=
        { app j := Over.homMk (cX.ι.app j) (hfl j)
          naturality _ _ g := Over.OverMorphism.ext ((cX.w g).trans (Category.comp_id _).symm) } }
  let cY' : Cocone Y' :=
    { pt := Over.mk l
      ι :=
        { app j := Over.homMk (cY.ι.app j)
          naturality _ _ g := Over.OverMorphism.ext ((cY.w g).trans (Category.comp_id _).symm) } }
  have hmono {Z : J ⥤ Aᵒᵖ ⥤ Type v} (t : ∀ j, Z.obj j ⟶ T) (ht) (hZ : ∀ (i j : J) (h : i ≤ j),
      Mono (Z.map (homOfLE h))) (i j : J) (h : i ≤ j) :
      Mono ((Z.toOver T t ht ⋙ E).map (homOfLE h)) :=
    have : Mono ((Z.toOver T t ht).map (homOfLE h)) := Over.mono_of_mono_left _ (hk := hZ i j h)
    E.map_mono _
  exact IsALocalizer.of_isColimit (hmono _ _ hX) (hmono _ _ hY) (Functor.whiskerRight φ' E)
    (fun j ↦ hφ j T _) (isColimitOfPreserves E (isColimitOfReflects (Over.forget T) (c := cX') hcX))
    (isColimitOfPreserves E (isColimitOfReflects (Over.forget T) (c := cY') hcY)) (sliceHom f l)
    fun j ↦ map_homMk_comp_map_homMk (ha := hfl j) (hb := rfl) (hc := rfl) (hd := rfl) (hf j)

instance absoluteWeakEquivalences_isStableUnderRetracts :
    (𝕀.absoluteWeakEquivalences S).IsStableUnderRetracts where
  of_retract h hg := fun T l ↦ (𝕀.overWeakEquivalences S T).of_retract
    ((retractArrowOver h l).map (overEquivPresheafCostructuredArrow T).functor) (hg T _)

end HomotopicalAlgebra.ExactCylinder
