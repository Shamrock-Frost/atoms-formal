import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Cisinski.FibrantObject
import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Cisinski.ModelStructure

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra.ExactCylinder

universe v u

variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C] [HasPushouts C] [HasTerminal C]
  [HasInitial C] [HasStrictInitialObjects C] [HasPullbacks C] [FinitaryPreExtensive C]
  [HasEffectiveUnions C] (𝕀 : ExactCylinder.{v} C) {S : MorphismProperty C}

omit [HasTerminal C] [HasPullbacks C] [FinitaryPreExtensive C] [HasEffectiveUnions C] in
theorem anodyne_endpoint_app (ε : Bool) (X : C) : 𝕀.anodyne S ((𝕀.endpoint ε).app X) :=
  (𝕀.anodyne S).of_retract (𝕀.endpointRetractArrow ε X)
    ((𝕀.isAnodyneClass_anodyne S).endpointBox_mem ε _ (initial.mono_from X _))

theorem weakEquivalences_of_isPushout_of_rlp [IsSaturated.{v} (MorphismProperty.monomorphisms C)]
    (hS : S ≤ MorphismProperty.monomorphisms C)
    {E D B P : C} {j : E ⟶ D} {p : E ⟶ B} {q : D ⟶ P} {j' : B ⟶ P} (h : IsPushout j p q j')
    [Mono j] (hp : (MorphismProperty.monomorphisms C).rlp p) : 𝕀.weakEquivalences S q := by
  have hW := 𝕀.anodyne_le_weakEquivalences S hS
  obtain ⟨s, hs⟩ := exists_section_of_rlp_monomorphisms p hp
  obtain ⟨k₀, h₀, h₁, hk₀⟩ := 𝕀.exists_homotopy_of_rlp_monomorphisms p hp s hs
  let a : 𝕀.I.obj E ⟶ 𝕀.endpointBoxSource false j := pushout.inl _ _
  let b : D ⟶ 𝕀.endpointBoxSource false j := pushout.inr _ _
  have hb : IsPushout ((𝕀.endpoint false).app E) j a b := IsPushout.of_hasPushout _ _
  have hbinr : b ≫ 𝕀.endpointBox false j = (𝕀.endpoint false).app D := pushout.inr_desc _ _ _
  have hbinl : a ≫ 𝕀.endpointBox false j = 𝕀.I.map j := pushout.inl_desc _ _ _
  have hbox : 𝕀.anodyne S (𝕀.endpointBox false j) :=
    (𝕀.isAnodyneClass_anodyne S).endpointBox_mem false j inferInstance
  let c : 𝕀.endpointBoxSource false j ⟶ D :=
    hb.desc (k₀ ≫ j) (𝟙 D) (by rw [reassoc_of% h₀, Category.comp_id])
  have hcinl : a ≫ c = k₀ ≫ j := hb.inl_desc _ _ _
  have hcinr : b ≫ c = 𝟙 D := hb.inr_desc _ _ _
  have hD := IsPushout.of_hasPushout (𝕀.endpointBox false j) c
  let H := pushout.inl (𝕀.endpointBox false j) c
  let ι := pushout.inr (𝕀.endpointBox false j) c
  have hHι : 𝕀.endpointBox false j ≫ H = c ≫ ι := pushout.condition
  have hι : 𝕀.weakEquivalences S ι := hW _ (MorphismProperty.of_isPushout hD.flip hbox)
  have hH₀ : (𝕀.endpoint false).app D ≫ H = ι := by
    rw [← hbinr, Category.assoc, hHι, reassoc_of% hcinr]
  have hH : 𝕀.weakEquivalences S H := (𝕀.weakEquivalences S).of_precomp _ _
    (hW _ (𝕀.anodyne_endpoint_app false D)) (by rw [hH₀]; exact hι)
  let δ := (𝕀.endpoint true).app D ≫ H
  have hδ : 𝕀.weakEquivalences S δ :=
    (𝕀.weakEquivalences S).comp_mem _ _ (hW _ (𝕀.anodyne_endpoint_app true D)) hH
  have hjδ : j ≫ δ = p ≫ s ≫ j ≫ ι := by
    change j ≫ (𝕀.endpoint true).app D ≫ H = _
    rw [← 𝕀.endpoint_naturality_assoc, ← hbinl, Category.assoc, hHι, reassoc_of% hcinl,
      reassoc_of% h₁]
  let g : P ⟶ pushout (𝕀.endpointBox false j) c := h.desc δ (s ≫ j ≫ ι) hjδ
  let k : pushout (𝕀.endpointBox false j) c ⟶ P :=
    pushout.desc (𝕀.contraction.app D ≫ q) q (by
      refine hb.hom_ext ?_ ?_
      · rw [reassoc_of% hbinl, 𝕀.map_contraction_app_assoc j, h.w, reassoc_of% hcinl, h.w,
          reassoc_of% hk₀]
      · rw [reassoc_of% hbinr, 𝕀.endpoint_app_contraction_app_assoc false, reassoc_of% hcinr])
  have hδk : δ ≫ k = q := by
    change ((𝕀.endpoint true).app D ≫ H) ≫ k = q
    rw [Category.assoc, pushout.inl_desc, 𝕀.endpoint_app_contraction_app_assoc true]
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

theorem weakEquivalences_desc_of_isPushout_of_rlp
    [IsSaturated.{v} (MorphismProperty.monomorphisms C)] (hS : S ≤ MorphismProperty.monomorphisms C)
    {E D Z B P Q : C} {j : E ⟶ D} {i : E ⟶ Z} {r : Z ⟶ B} {q : D ⟶ P} {j' : B ⟶ P}
    {a : D ⟶ Q} {b : Z ⟶ Q} (h : IsPushout j (i ≫ r) q j') (h₁ : IsPushout j i a b) [Mono j]
    (hr : (MorphismProperty.monomorphisms C).rlp r) :
    𝕀.weakEquivalences S (h₁.desc q (r ≫ j') (by rw [h.w, Category.assoc])) := by
  have : Mono b := (MorphismProperty.monomorphisms C).of_isPushout h₁.flip
    (inferInstanceAs (Mono j))
  exact 𝕀.weakEquivalences_of_isPushout_of_rlp hS (IsPushout.of_top' h h₁) hr

variable [HasBinaryProducts C] [HasColimitsOfSize.{v, v} C] [IsLocallyPresentable.{v} C]
  [HasCellularModel C] [S.IsSmall.{v}]

theorem weakEquivalences_of_isPushout (hS : S ≤ MorphismProperty.monomorphisms C)
    {E D B P : C} {j : E ⟶ D} {w : E ⟶ B} {q : D ⟶ P} {j' : B ⟶ P} (h : IsPushout j w q j')
    [Mono j] (hw : 𝕀.weakEquivalences S w) : 𝕀.weakEquivalences S q := by
  have := 𝕀.isSaturated_trivialCofibrations S hS
  let F := factorizationData (MorphismProperty.monomorphisms C)
    (MorphismProperty.monomorphisms C).rlp w
  have hm : 𝕀.weakEquivalences S F.i := (𝕀.weakEquivalences S).of_postcomp _ _
    (𝕀.weakEquivalences_of_rlp_monomorphisms S _ F.hp) (by rw [F.fac]; exact hw)
  have h' : IsPushout j (F.i ≫ F.p) q j' := by rwa [F.fac]
  have h₁ := IsPushout.of_hasPushout j F.i
  have ha : 𝕀.weakEquivalences S (pushout.inl j F.i) :=
    (MorphismProperty.of_isPushout (P := 𝕀.trivialCofibrations S) h₁ ⟨F.hi, hm⟩).2
  have hq := (𝕀.weakEquivalences S).comp_mem _ _ ha
    (𝕀.weakEquivalences_desc_of_isPushout_of_rlp hS h' h₁ F.hp)
  rwa [h₁.inl_desc] at hq

private theorem weakEquivalences_of_isPushout_of_mono_of_mono
    (hS : S ≤ MorphismProperty.monomorphisms C) {F₀ F₁ F₂ F' G₀ G₁ G₂ G' : C}
    {φ₁ : F₀ ⟶ F₁} {φ₂ : F₀ ⟶ F₂} {ε₁ : F₁ ⟶ F'} {ε₂ : F₂ ⟶ F'}
    {ψ₁ : G₀ ⟶ G₁} {ψ₂ : G₀ ⟶ G₂} {η₁ : G₁ ⟶ G'} {η₂ : G₂ ⟶ G'}
    (hF : IsPushout φ₁ φ₂ ε₁ ε₂) (hG : IsPushout ψ₁ ψ₂ η₁ η₂) (hφ₁ : Mono φ₁) (hψ₂ : Mono ψ₂)
    (χ₀ : F₀ ⟶ G₀) (χ₁ : F₁ ⟶ G₁) (χ₂ : F₂ ⟶ G₂) (χ' : F' ⟶ G')
    (h₁ : φ₁ ≫ χ₁ = χ₀ ≫ ψ₁) (h₂ : φ₂ ≫ χ₂ = χ₀ ≫ ψ₂)
    (h₁' : ε₁ ≫ χ' = χ₁ ≫ η₁) (h₂' : ε₂ ≫ χ' = χ₂ ≫ η₂)
    (hχ₀ : 𝕀.weakEquivalences S χ₀) (hχ₁ : 𝕀.weakEquivalences S χ₁)
    (hχ₂ : 𝕀.weakEquivalences S χ₂) : 𝕀.weakEquivalences S χ' := by
  have hY := IsPushout.of_hasPushout φ₁ χ₀
  let m : pushout φ₁ χ₀ ⟶ G₁ := hY.desc χ₁ ψ₁ h₁
  have hinl : 𝕀.weakEquivalences S (pushout.inl φ₁ χ₀) :=
    𝕀.weakEquivalences_of_isPushout hS hY hχ₀
  have hm : 𝕀.weakEquivalences S m := (𝕀.weakEquivalences S).of_precomp _ _ hinl
    (by rw [hY.inl_desc]; exact hχ₁)
  have hinr : pushout.inr φ₁ χ₀ ≫ m = ψ₁ := hY.inr_desc _ _ _
  have hX := IsPushout.of_hasPushout (pushout.inr φ₁ χ₀) ψ₂
  have hbig : IsPushout φ₁ (φ₂ ≫ χ₂)
      (pushout.inl φ₁ χ₀ ≫ pushout.inl (pushout.inr φ₁ χ₀) ψ₂)
      (pushout.inr (pushout.inr φ₁ χ₀) ψ₂) := by
    rw [h₂]
    exact hY.paste_vert hX
  have hu := IsPushout.of_top' hbig hF
  have : Mono ε₂ := (MorphismProperty.monomorphisms C).of_isPushout hF.flip
    (inferInstanceAs (Mono φ₁))
  have hu' := 𝕀.weakEquivalences_of_isPushout hS hu hχ₂
  have hv := IsPushout.of_left' (by rwa [hinr]) hX
  have : Mono (pushout.inl (pushout.inr φ₁ χ₀) ψ₂) :=
    (MorphismProperty.monomorphisms C).of_isPushout hX (inferInstanceAs (Mono ψ₂))
  have hv' := 𝕀.weakEquivalences_of_isPushout hS hv.flip hm
  have hc := (𝕀.weakEquivalences S).comp_mem _ _ hu' hv'
  convert hc using 1
  refine hF.hom_ext ?_ ?_
  · rw [h₁', hF.inl_desc_assoc, Category.assoc, hX.inl_desc, hY.inl_desc_assoc]
  · rw [h₂', hF.inr_desc_assoc, Category.assoc, hX.inr_desc]

theorem weakEquivalences_of_isPushout_of_mono (hS : S ≤ MorphismProperty.monomorphisms C)
    {F₀ F₁ F₂ F' G₀ G₁ G₂ G' : C}
    {φ₁ : F₀ ⟶ F₁} {φ₂ : F₀ ⟶ F₂} {ε₁ : F₁ ⟶ F'} {ε₂ : F₂ ⟶ F'}
    {ψ₁ : G₀ ⟶ G₁} {ψ₂ : G₀ ⟶ G₂} {η₁ : G₁ ⟶ G'} {η₂ : G₂ ⟶ G'}
    (hF : IsPushout φ₁ φ₂ ε₁ ε₂) (hG : IsPushout ψ₁ ψ₂ η₁ η₂) [Mono φ₁] [Mono ψ₁]
    (χ₀ : F₀ ⟶ G₀) (χ₁ : F₁ ⟶ G₁) (χ₂ : F₂ ⟶ G₂) (χ' : F' ⟶ G')
    (h₁ : φ₁ ≫ χ₁ = χ₀ ≫ ψ₁) (h₂ : φ₂ ≫ χ₂ = χ₀ ≫ ψ₂)
    (h₁' : ε₁ ≫ χ' = χ₁ ≫ η₁) (h₂' : ε₂ ≫ χ' = χ₂ ≫ η₂)
    (hχ₀ : 𝕀.weakEquivalences S χ₀) (hχ₁ : 𝕀.weakEquivalences S χ₁)
    (hχ₂ : 𝕀.weakEquivalences S χ₂) : 𝕀.weakEquivalences S χ' := by
  let Fφ := factorizationData (MorphismProperty.monomorphisms C)
    (MorphismProperty.monomorphisms C).rlp φ₂
  let Fψ := factorizationData (MorphismProperty.monomorphisms C)
    (MorphismProperty.monomorphisms C).rlp ψ₂
  have : Mono Fφ.i := Fφ.hi
  have : Mono Fψ.i := Fψ.hi
  have hpφ := 𝕀.weakEquivalences_of_rlp_monomorphisms S _ Fφ.hp
  have hpψ := 𝕀.weakEquivalences_of_rlp_monomorphisms S _ Fψ.hp
  have := Fψ.hp Fφ.i Fφ.hi
  have sq : CommSq (χ₀ ≫ Fψ.i) Fφ.i Fψ.p (Fφ.p ≫ χ₂) := ⟨by
    rw [Category.assoc, Fψ.fac, ← h₂, reassoc_of% Fφ.fac]⟩
  have hl : 𝕀.weakEquivalences S sq.lift := (𝕀.weakEquivalences S).of_postcomp _ _ hpψ (by
    rw [sq.fac_right]
    exact (𝕀.weakEquivalences S).comp_mem _ _ hpφ hχ₂)
  have hF' := IsPushout.of_hasPushout φ₁ Fφ.i
  have hG' := IsPushout.of_hasPushout ψ₁ Fψ.i
  let χ'' := hF'.desc (χ₁ ≫ pushout.inl ψ₁ Fψ.i) (sq.lift ≫ pushout.inr ψ₁ Fψ.i) (by
    rw [reassoc_of% h₁, hG'.w, reassoc_of% sq.fac_left])
  have hχ'' : 𝕀.weakEquivalences S χ'' := 𝕀.weakEquivalences_of_isPushout_of_mono_of_mono hS
    hF' hG' inferInstance Fψ.hi χ₀ χ₁ sq.lift χ'' h₁ sq.fac_left (hF'.inl_desc _ _ _)
    (hF'.inr_desc _ _ _) hχ₀ hχ₁ hl
  have hFφ : IsPushout φ₁ (Fφ.i ≫ Fφ.p) ε₁ ε₂ := by rwa [Fφ.fac]
  have hGψ : IsPushout ψ₁ (Fψ.i ≫ Fψ.p) η₁ η₂ := by rwa [Fψ.fac]
  let cF := hF'.desc ε₁ (Fφ.p ≫ ε₂) (by rw [hFφ.w, Category.assoc])
  let cG := hG'.desc η₁ (Fψ.p ≫ η₂) (by rw [hGψ.w, Category.assoc])
  have hcF : 𝕀.weakEquivalences S cF :=
    𝕀.weakEquivalences_desc_of_isPushout_of_rlp hS hFφ hF' Fφ.hp
  have hcG : 𝕀.weakEquivalences S cG :=
    𝕀.weakEquivalences_desc_of_isPushout_of_rlp hS hGψ hG' Fψ.hp
  have hc : cF ≫ χ' = χ'' ≫ cG := by
    refine hF'.hom_ext ?_ ?_
    · rw [hF'.inl_desc_assoc, h₁', hF'.inl_desc_assoc, Category.assoc, hG'.inl_desc]
    · rw [hF'.inr_desc_assoc, Category.assoc, h₂', hF'.inr_desc_assoc, Category.assoc,
        hG'.inr_desc, reassoc_of% sq.fac_right]
  exact (𝕀.weakEquivalences S).of_precomp _ _ hcF
    (by rw [hc]; exact (𝕀.weakEquivalences S).comp_mem _ _ hχ'' hcG)

end HomotopicalAlgebra.ExactCylinder
