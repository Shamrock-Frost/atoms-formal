import Mathlib.CategoryTheory.MorphismProperty.Limits

namespace CategoryTheory.MorphismProperty

variable {C : Type*} [Category C]

theorem mem_iff_of_isPullback (V : MorphismProperty C) [V.RespectsIso]
    {P Q K L P' Q' : C} {φ : P ⟶ Q} {α : P ⟶ K} {β : Q ⟶ L} {f : K ⟶ L} {φ' : P' ⟶ Q'}
    {α' : P' ⟶ K} {β' : Q' ⟶ L} (h : IsPullback φ α β f) (h' : IsPullback φ' α' β' f)
    (e : Q' ≅ Q) (he : e.hom ≫ β = β') : V φ' ↔ V φ := by
  let i : P' ⟶ P := h.lift (φ' ≫ e.hom) α' (by rw [Category.assoc, he, h'.w])
  let j : P ⟶ P' := h'.lift (φ ≫ e.inv) α (by rw [Category.assoc, ← he, e.inv_hom_id_assoc, h.w])
  have hij : i ≫ j = 𝟙 _ := h'.hom_ext (by simp [i, j]) (by simp [i, j])
  have hji : j ≫ i = 𝟙 _ := h.hom_ext (by simp [i, j]) (by simp [i, j])
  exact V.arrow_mk_iso_iff (Arrow.isoMk ⟨i, j, hij, hji⟩ e (by simp [i]))

instance IsStableUnderCobaseChange.inverseImage {D : Type*} [Category D] (F : C ⥤ D)
    [Limits.PreservesColimitsOfShape Limits.WalkingSpan F] (P : MorphismProperty D)
    [P.IsStableUnderCobaseChange] : (P.inverseImage F).IsStableUnderCobaseChange :=
  ⟨fun sq hf ↦ P.of_isPushout (sq.map F) hf⟩

open Limits in
theorem coprod_map_mem_of_isStableUnderCobaseChange [HasBinaryCoproducts C]
    (P : MorphismProperty C) [P.IsStableUnderCobaseChange] [P.IsStableUnderComposition]
    [P.RespectsIso] {K X : C} {u : K ⟶ X} (hu : P u) : P (coprod.map u u) := by
  have h₁ : P (coprod.map u (𝟙 K)) := P.of_isPushout (IsPushout.of_coprod_inl_with_id u K) hu
  have h₂ : P (coprod.map (𝟙 X) u) := by
    have e : coprod.map (𝟙 X) u = (coprod.braiding X K).hom ≫ coprod.map u (𝟙 X) ≫
        (coprod.braiding X X).hom := by
      apply coprod.hom_ext
      · simp only [coprod.braiding_hom, coprod.inl_desc_assoc, coprod.inr_map_assoc,
          Category.id_comp, coprod.inr_desc, coprod.inl_map]
      · simp only [coprod.braiding_hom, coprod.inr_desc_assoc, coprod.inl_map_assoc,
          coprod.inl_desc, coprod.inr_map]
    rw [e, cancel_left_of_respectsIso P, cancel_right_of_respectsIso P]
    exact P.of_isPushout (IsPushout.of_coprod_inl_with_id u X) hu
  have e : coprod.map u u = coprod.map u (𝟙 K) ≫ coprod.map (𝟙 X) u := by
    rw [coprod.map_map]
    simp
  rw [e]
  exact P.comp_mem _ _ h₁ h₂

end CategoryTheory.MorphismProperty
