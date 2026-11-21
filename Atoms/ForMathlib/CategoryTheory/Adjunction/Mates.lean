import Mathlib.CategoryTheory.Adjunction.Mates

namespace CategoryTheory

theorem homEquiv_conjugateEquiv_app {C D : Type*} [Category C] [Category D] {L₁ L₂ : C ⥤ D}
    {R₁ R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁) {c : C} {d : D}
    (g : L₁.obj c ⟶ d) :
    adj₂.homEquiv c d (α.app c ≫ g) =
      adj₁.homEquiv c d g ≫ (conjugateEquiv adj₁ adj₂ α).app d := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc,
    (conjugateEquiv adj₁ adj₂ α).naturality, ← Category.assoc, ← unit_conjugateEquiv,
    Category.assoc]

theorem isIso_conjugateEquiv_app_of_bijective {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁) (d : D)
    (h : ∀ c, Function.Bijective fun g : L₁.obj c ⟶ d => α.app c ≫ g) :
    IsIso ((conjugateEquiv adj₁ adj₂ α).app d) := by
  refine isIso_of_yoneda_map_bijective _ fun c => ?_
  have e : (fun x : c ⟶ R₁.obj d => x ≫ (conjugateEquiv adj₁ adj₂ α).app d) =
      adj₂.homEquiv c d ∘ (fun g => α.app c ≫ g) ∘ (adj₁.homEquiv c d).symm := by
    funext x
    rw [Function.comp_apply, Function.comp_apply, homEquiv_conjugateEquiv_app,
      Equiv.apply_symm_apply]
  rw [e]
  exact (adj₂.homEquiv c d).bijective.comp ((h c).comp (adj₁.homEquiv c d).symm.bijective)

theorem conjugateEquiv_eq_of_homEquiv {C D : Type*} [Category C] [Category D] {L₁ L₂ : C ⥤ D}
    {R₁ R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁) (γ : R₁ ⟶ R₂)
    (h : ∀ (c : C) (d : D) (g : L₁.obj c ⟶ d),
      adj₂.homEquiv c d (α.app c ≫ g) = adj₁.homEquiv c d g ≫ γ.app d) :
    conjugateEquiv adj₁ adj₂ α = γ := by
  ext d
  have e : adj₁.homEquiv _ d (adj₁.counit.app d) = 𝟙 _ := by
    rw [Adjunction.homEquiv_unit, Adjunction.right_triangle_components]
  have h₁ := h (R₁.obj d) d (adj₁.counit.app d)
  rw [homEquiv_conjugateEquiv_app, e, Category.id_comp, Category.id_comp] at h₁
  exact h₁

end CategoryTheory
