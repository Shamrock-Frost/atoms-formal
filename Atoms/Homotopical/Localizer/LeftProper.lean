import Atoms.Homotopical.HomotopyColimit.ColimitInvariance
import Atoms.Homotopical.Cellular.MonoSaturated

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra

namespace Atoms.Homotopical

universe w v

variable {A : Type v} [SmallCategory A]

private theorem mem_of_isPushout_of_rlp_aux {A : Type v} [SmallCategory A]
    {V : MorphismProperty (Aᵒᵖ ⥤ Type v)} [hV : IsALocalizer.{v, v} V] {E D B P : Aᵒᵖ ⥤ Type v}
    {j : E ⟶ D} {p : E ⟶ B} {q : D ⟶ P}
    {j' : B ⟶ P} (h : IsPushout j p q j') [Mono j]
    (hp : (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v)).rlp p) : V q := by
  let I := lawvereCylinder A
  obtain ⟨s, hs⟩ := exists_section_of_rlp_monomorphisms p hp
  obtain ⟨k₀, h₀, h₁, hk₀⟩ := I.exists_homotopy_of_rlp_monomorphisms p hp s hs
  let a : I.I.obj E ⟶ I.endpointBoxSource false j := pushout.inl _ _
  let b : D ⟶ I.endpointBoxSource false j := pushout.inr _ _
  have hb : IsPushout ((I.endpoint false).app E) j a b := IsPushout.of_hasPushout _ _
  have := I.mono_endpoint false E
  have hinr : (MorphismProperty.monomorphisms _ ⊓ V) b :=
    MorphismProperty.of_isPushout hb.flip
      ⟨MorphismProperty.monomorphisms.infer_property _, hV.lawvereCylinder_endpoint_mem false E⟩
  have hbinr : b ≫ I.endpointBox false j = (I.endpoint false).app D := pushout.inr_desc _ _ _
  have hbinl : a ≫ I.endpointBox false j = I.I.map j := pushout.inl_desc _ _ _
  have hbox : (MorphismProperty.monomorphisms _ ⊓ V) (I.endpointBox false j) :=
    ⟨I.mono_endpointBox false j inferInstance, V.of_precomp _ _ hinr.2
      (by rw [hbinr]; exact hV.lawvereCylinder_endpoint_mem false D)⟩
  let c : I.endpointBoxSource false j ⟶ D :=
    hb.desc (k₀ ≫ j) (𝟙 D) (by rw [reassoc_of% h₀, Category.comp_id])
  have hcinl : a ≫ c = k₀ ≫ j := hb.inl_desc _ _ _
  have hcinr : b ≫ c = 𝟙 D := hb.inr_desc _ _ _
  have hD := IsPushout.of_hasPushout (I.endpointBox false j) c
  let H := pushout.inl (I.endpointBox false j) c
  let ι := pushout.inr (I.endpointBox false j) c
  have hHι : I.endpointBox false j ≫ H = c ≫ ι := pushout.condition
  have hι : V ι := (MorphismProperty.of_isPushout hD.flip hbox).2
  have hH₀ : (I.endpoint false).app D ≫ H = ι := by
    rw [← hbinr, Category.assoc, hHι, reassoc_of% hcinr]
  have hH : V H := V.of_precomp _ _
    (hV.lawvereCylinder_endpoint_mem false D) (by rw [hH₀]; exact hι)
  let δ := (I.endpoint true).app D ≫ H
  have hδ : V δ := V.comp_mem _ _ (hV.lawvereCylinder_endpoint_mem true D) hH
  have hjδ : j ≫ δ = p ≫ s ≫ j ≫ ι := by
    change j ≫ (I.endpoint true).app D ≫ H = _
    rw [← I.endpoint_naturality_assoc, ← hbinl, Category.assoc, hHι, reassoc_of% hcinl,
      reassoc_of% h₁]
  let g : P ⟶ pushout (I.endpointBox false j) c := h.desc δ (s ≫ j ≫ ι) hjδ
  let k : pushout (I.endpointBox false j) c ⟶ P :=
    pushout.desc (I.contraction.app D ≫ q) q (by
      refine hb.hom_ext ?_ ?_
      · rw [reassoc_of% hbinl, I.map_contraction_app_assoc j, h.w, reassoc_of% hcinl, h.w,
          reassoc_of% hk₀]
      · rw [reassoc_of% hbinr, I.endpoint_app_contraction_app_assoc false, reassoc_of% hcinr])
  have hδk : δ ≫ k = q := by
    change ((I.endpoint true).app D ≫ H) ≫ k = q
    rw [Category.assoc, pushout.inl_desc, I.endpoint_app_contraction_app_assoc true]
  have hιk : ι ≫ k = q := pushout.inr_desc _ _ _
  have hgk : g ≫ k = 𝟙 P := by
    refine h.hom_ext ?_ ?_
    · rw [h.inl_desc_assoc, hδk, Category.comp_id]
    · rw [h.inr_desc_assoc, Category.assoc, Category.assoc, hιk, h.w, reassoc_of% hs,
        Category.comp_id]
  let R : RetractArrow q δ :=
    { i := Arrow.homMk (𝟙 D) g (by simp [g])
      r := Arrow.homMk (𝟙 D) k (by simp [hδk])
      retract := by ext <;> simp [hgk] }
  exact MorphismProperty.of_retract R hδ

theorem IsALocalizer.mem_of_isPushout_of_rlp {V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))}
    [hV : IsALocalizer V] {E D B P : Aᵒᵖ ⥤ Type (max w v)} {j : E ⟶ D} {p : E ⟶ B} {q : D ⟶ P}
    {j' : B ⟶ P} (h : IsPushout j p q j') [Mono j]
    (hp : (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v))).rlp p) : V q := by
  have := IsALocalizer.inverseImage_asSmall (V := V)
  rw [MorphismProperty.monomorphisms_eq_inverseImage_of_isEquivalence
      (AsSmall.equiv : A ≌ AsSmall.{max w v} A).op.congrLeft.functor,
    MorphismProperty.rlp_inverseImage_of_isEquivalence] at hp
  exact (MorphismProperty.map_functor_map_inverse_iff
    (AsSmall.equiv : A ≌ AsSmall.{max w v} A).op.congrLeft.symm V q).1
      (mem_of_isPushout_of_rlp_aux
        (V := V.inverseImage (AsSmall.equiv : A ≌ AsSmall.{max w v} A).op.congrLeft.inverse)
        (h.map (AsSmall.equiv : A ≌ AsSmall.{max w v} A).op.congrLeft.functor) hp)

theorem IsALocalizer.mem_desc_of_isPushout_of_rlp {V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))}
    [hV : IsALocalizer V] {E D Z B P Q : Aᵒᵖ ⥤ Type (max w v)} {j : E ⟶ D} {i : E ⟶ Z} {r : Z ⟶ B}
    {q : D ⟶ P} {j' : B ⟶ P} {a : D ⟶ Q} {b : Z ⟶ Q} (h : IsPushout j (i ≫ r) q j')
    (h₁ : IsPushout j i a b) [Mono j]
    (hr : (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v))).rlp r) :
    V (h₁.desc q (r ≫ j') (by rw [h.w, Category.assoc])) := by
  have := Adhesive.mono_of_isPushout_of_mono_left h₁
  exact hV.mem_of_isPushout_of_rlp (IsPushout.of_top' h h₁) hr

theorem IsALocalizer.mem_of_isPushout {V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))}
    [hV : IsALocalizer V] {E D B P : Aᵒᵖ ⥤ Type (max w v)} {j : E ⟶ D} {w : E ⟶ B} {q : D ⟶ P}
    {j' : B ⟶ P} (h : IsPushout j w q j') [Mono j] (hw : V w) : V q := by
  let F := factorizationData (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)))
    (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v))).rlp w
  have hm : V F.i :=
    V.of_postcomp _ _ (hV.rlp_monomorphisms_le _ F.hp) (by rw [F.fac]; exact hw)
  have h' : IsPushout j (F.i ≫ F.p) q j' := by rwa [F.fac]
  have h₁ := IsPushout.of_hasPushout j F.i
  have ha : V (pushout.inl j F.i) :=
    (MorphismProperty.of_isPushout (P := MorphismProperty.monomorphisms _ ⊓ V) h₁ ⟨F.hi, hm⟩).2
  have hq := V.comp_mem _ _ ha (hV.mem_desc_of_isPushout_of_rlp h' h₁ F.hp)
  rwa [h₁.inl_desc] at hq

private theorem of_isPushout_asSmall {V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))}
    [IsALocalizer V] {F₀ F₁ F₂ F' G₀ G₁ G₂ G' : Aᵒᵖ ⥤ Type (max w v)}
    {φ₁ : F₀ ⟶ F₁} {φ₂ : F₀ ⟶ F₂} {ε₁ : F₁ ⟶ F'} {ε₂ : F₂ ⟶ F'}
    {ψ₁ : G₀ ⟶ G₁} {ψ₂ : G₀ ⟶ G₂} {η₁ : G₁ ⟶ G'} {η₂ : G₂ ⟶ G'}
    (hF : IsPushout φ₁ φ₂ ε₁ ε₂) (hG : IsPushout ψ₁ ψ₂ η₁ η₂) [Mono φ₁] [Mono φ₂] [Mono ψ₁]
    [Mono ψ₂] (χ₀ : F₀ ⟶ G₀) (χ₁ : F₁ ⟶ G₁) (χ₂ : F₂ ⟶ G₂) (χ' : F' ⟶ G')
    (h₁ : φ₁ ≫ χ₁ = χ₀ ≫ ψ₁) (h₂ : φ₂ ≫ χ₂ = χ₀ ≫ ψ₂)
    (h₁' : ε₁ ≫ χ' = χ₁ ≫ η₁) (h₂' : ε₂ ≫ χ' = χ₂ ≫ η₂)
    (hχ₀ : V χ₀) (hχ₁ : V χ₁) (hχ₂ : V χ₂) : V χ' := by
  have := IsALocalizer.inverseImage_asSmall (V := V)
  have hV : ∀ {X Y : Aᵒᵖ ⥤ Type (max w v)} (f : X ⟶ Y),
      V ((AsSmall.equiv : A ≌ AsSmall.{max w v} A).op.congrLeft.inverse.map
        ((AsSmall.equiv : A ≌ AsSmall.{max w v} A).op.congrLeft.functor.map f)) ↔ V f :=
    fun f ↦ MorphismProperty.map_functor_map_inverse_iff
      (AsSmall.equiv : A ≌ AsSmall.{max w v} A).op.congrLeft.symm V f
  let F : (Aᵒᵖ ⥤ Type (max w v)) ⥤ ((AsSmall.{max w v} A)ᵒᵖ ⥤ Type (max w v)) :=
    (AsSmall.equiv : A ≌ AsSmall.{max w v} A).op.congrLeft.functor
  refine (hV χ').1 (IsALocalizer.of_isPushout
    (V := V.inverseImage (AsSmall.equiv : A ≌ AsSmall.{max w v} A).op.congrLeft.inverse)
    (hF.map F) (hG.map F) (F.map χ₀) (F.map χ₁)
    (F.map χ₂) (F.map χ') ?_ ?_ ?_ ?_ ((hV χ₀).2 hχ₀) ((hV χ₁).2 hχ₁) ((hV χ₂).2 hχ₂))
  all_goals simp only [← F.map_comp, h₁, h₂, h₁', h₂']

theorem IsALocalizer.of_isColimit_asSmall {V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))}
    [IsALocalizer V] {J : Type (max w v)} [LinearOrder J] [WellFoundedLT J]
    {X Y : J ⥤ Aᵒᵖ ⥤ Type (max w v)}
    (hX : ∀ (i j : J) (h : i ≤ j), Mono (X.map (homOfLE h)))
    (hY : ∀ (i j : J) (h : i ≤ j), Mono (Y.map (homOfLE h)))
    (φ : X ⟶ Y) (hφ : ∀ j, V (φ.app j)) {cX : Cocone X} {cY : Cocone Y}
    (hcX : IsColimit cX) (hcY : IsColimit cY) (f : cX.pt ⟶ cY.pt)
    (hf : ∀ j, cX.ι.app j ≫ f = φ.app j ≫ cY.ι.app j) : V f := by
  have := IsALocalizer.inverseImage_asSmall (V := V)
  have hV : ∀ {X Y : Aᵒᵖ ⥤ Type (max w v)} (f : X ⟶ Y),
      V ((AsSmall.equiv : A ≌ AsSmall.{max w v} A).op.congrLeft.inverse.map
        ((AsSmall.equiv : A ≌ AsSmall.{max w v} A).op.congrLeft.functor.map f)) ↔ V f :=
    fun f ↦ MorphismProperty.map_functor_map_inverse_iff
      (AsSmall.equiv : A ≌ AsSmall.{max w v} A).op.congrLeft.symm V f
  let F : (Aᵒᵖ ⥤ Type (max w v)) ⥤ ((AsSmall.{max w v} A)ᵒᵖ ⥤ Type (max w v)) :=
    (AsSmall.equiv : A ≌ AsSmall.{max w v} A).op.congrLeft.functor
  refine (hV f).1 (IsALocalizer.of_isColimit
    (V := V.inverseImage (AsSmall.equiv : A ≌ AsSmall.{max w v} A).op.congrLeft.inverse)
    (X := X ⋙ F) (Y := Y ⋙ F)
    (fun i j h ↦ F.map_mono (X.map (homOfLE h))) (fun i j h ↦ F.map_mono (Y.map (homOfLE h)))
    (Functor.whiskerRight φ F) (fun j ↦ (hV (φ.app j)).2 (hφ j)) (isColimitOfPreserves F hcX)
    (isColimitOfPreserves F hcY) (F.map f) fun j ↦ ?_)
  simp only [Functor.mapCocone_ι_app, Functor.whiskerRight_app, ← F.map_comp, hf]

theorem IsALocalizer.of_isPushout_of_mono {V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))}
    [hV : IsALocalizer V] {F₀ F₁ F₂ F' G₀ G₁ G₂ G' : Aᵒᵖ ⥤ Type (max w v)}
    {φ₁ : F₀ ⟶ F₁} {φ₂ : F₀ ⟶ F₂} {ε₁ : F₁ ⟶ F'} {ε₂ : F₂ ⟶ F'}
    {ψ₁ : G₀ ⟶ G₁} {ψ₂ : G₀ ⟶ G₂} {η₁ : G₁ ⟶ G'} {η₂ : G₂ ⟶ G'}
    (hF : IsPushout φ₁ φ₂ ε₁ ε₂) (hG : IsPushout ψ₁ ψ₂ η₁ η₂) [Mono φ₁] [Mono ψ₁]
    (χ₀ : F₀ ⟶ G₀) (χ₁ : F₁ ⟶ G₁) (χ₂ : F₂ ⟶ G₂) (χ' : F' ⟶ G')
    (h₁ : φ₁ ≫ χ₁ = χ₀ ≫ ψ₁) (h₂ : φ₂ ≫ χ₂ = χ₀ ≫ ψ₂)
    (h₁' : ε₁ ≫ χ' = χ₁ ≫ η₁) (h₂' : ε₂ ≫ χ' = χ₂ ≫ η₂)
    (hχ₀ : V χ₀) (hχ₁ : V χ₁) (hχ₂ : V χ₂) : V χ' := by
  let Fφ := factorizationData (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)))
    (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v))).rlp φ₂
  let Fψ := factorizationData (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)))
    (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v))).rlp ψ₂
  have : Mono Fφ.i := Fφ.hi
  have : Mono Fψ.i := Fψ.hi
  have := Fψ.hp Fφ.i Fφ.hi
  have sq : CommSq (χ₀ ≫ Fψ.i) Fφ.i Fψ.p (Fφ.p ≫ χ₂) := ⟨by
    rw [Category.assoc, Fψ.fac, ← h₂, reassoc_of% Fφ.fac]⟩
  let l := sq.lift
  have hl : V l := V.of_postcomp _ _ (hV.rlp_monomorphisms_le _ Fψ.hp) (by
    rw [sq.fac_right]
    exact V.comp_mem _ _ (hV.rlp_monomorphisms_le _ Fφ.hp) hχ₂)
  have hF' := IsPushout.of_hasPushout φ₁ Fφ.i
  have hG' := IsPushout.of_hasPushout ψ₁ Fψ.i
  let χ'' := hF'.desc (χ₁ ≫ pushout.inl ψ₁ Fψ.i) (l ≫ pushout.inr ψ₁ Fψ.i) (by
    rw [reassoc_of% h₁, hG'.w, reassoc_of% sq.fac_left])
  have hχ'' : V χ'' := of_isPushout_asSmall hF' hG' χ₀ χ₁ l χ'' h₁ sq.fac_left
    (hF'.inl_desc _ _ _) (hF'.inr_desc _ _ _) hχ₀ hχ₁ hl
  have hFφ : IsPushout φ₁ (Fφ.i ≫ Fφ.p) ε₁ ε₂ := by rwa [Fφ.fac]
  have hGψ : IsPushout ψ₁ (Fψ.i ≫ Fψ.p) η₁ η₂ := by rwa [Fψ.fac]
  let cF := hF'.desc ε₁ (Fφ.p ≫ ε₂) (by rw [hFφ.w, Category.assoc])
  let cG := hG'.desc η₁ (Fψ.p ≫ η₂) (by rw [hGψ.w, Category.assoc])
  have hcF : V cF := hV.mem_desc_of_isPushout_of_rlp hFφ hF' Fφ.hp
  have hcG : V cG := hV.mem_desc_of_isPushout_of_rlp hGψ hG' Fψ.hp
  have hc : cF ≫ χ' = χ'' ≫ cG := by
    refine hF'.hom_ext ?_ ?_
    · rw [hF'.inl_desc_assoc, h₁', hF'.inl_desc_assoc, Category.assoc, hG'.inl_desc]
    · rw [hF'.inr_desc_assoc, Category.assoc, h₂', hF'.inr_desc_assoc, Category.assoc,
        hG'.inr_desc, reassoc_of% sq.fac_right]
  exact V.of_precomp _ _ hcF (by rw [hc]; exact V.comp_mem _ _ hχ'' hcG)

theorem IsALocalizer.isMonoSaturatedClass_app {V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))}
    [hV : IsALocalizer V] {B : Type v} [SmallCategory B]
    (Φ Ψ : (Bᵒᵖ ⥤ Type (max w v)) ⥤ (Aᵒᵖ ⥤ Type (max w v)))
    [PreservesColimitsOfSize.{max w v, max w v} Φ] [PreservesColimitsOfSize.{max w v, max w v} Ψ]
    (hΦ : ∀ {X Y : Bᵒᵖ ⥤ Type (max w v)} (f : X ⟶ Y), Mono f → Mono (Φ.map f))
    (hΨ : ∀ {X Y : Bᵒᵖ ⥤ Type (max w v)} (f : X ⟶ Y), Mono f → Mono (Ψ.map f)) (α : Φ ⟶ Ψ) :
    IsMonoSaturatedClass (fun X => V (α.app X)) where
  of_isPushout {X₀ X₁ X₂ X₃ f₁ f₂ g₁ g₂} h hf h₀ h₁ h₂ := by
    have := preservesSmallestColimits_of_preservesColimits Φ
    have := preservesSmallestColimits_of_preservesColimits Ψ
    have := hΦ f₁ hf
    have := hΨ f₁ hf
    exact hV.of_isPushout_of_mono (Φ.map_isPushout h) (Ψ.map_isPushout h)
      (α.app X₀) (α.app X₁) (α.app X₂) (α.app X₃) (α.naturality f₁) (α.naturality f₂)
      (α.naturality g₁) (α.naturality g₂) h₀ h₁ h₂
  of_isColimit J _ _ F hF {c} hc hP :=
    IsALocalizer.of_isColimit_asSmall (X := F ⋙ Φ) (Y := F ⋙ Ψ)
      (fun i j h => hΦ _ (hF i j h)) (fun i j h => hΨ _ (hF i j h))
      (Functor.whiskerLeft F α) hP (isColimitOfPreserves Φ hc) (isColimitOfPreserves Ψ hc)
      (α.app c.pt) (fun j => α.naturality (c.ι.app j))

end Atoms.Homotopical
