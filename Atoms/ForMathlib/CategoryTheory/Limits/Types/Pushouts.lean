import Mathlib.CategoryTheory.Limits.Types.Pushouts

namespace CategoryTheory.Limits.Types

universe v

variable {X₁ X₂ X₃ X₄ : Type v} {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}

theorem eq_of_isPushout_of_notMem_range (h : IsPushout t l r b) {y : X₃}
    (hy : y ∉ Set.range l) : (∀ x, r x ≠ b y) ∧ ∀ y', b y' = b y → y' = y := by
  classical
  let g : X₄ ⟶ Option X₃ := h.desc (↾fun _ ↦ none)
    (↾fun z ↦ if z ∈ Set.range l then none else some z) (by ext s; simp)
  have hr (x : X₂) : g (r x) = none := ConcreteCategory.congr_hom (h.inl_desc _ _ _) x
  have hb (z : X₃) : g (b z) = if z ∈ Set.range l then none else some z :=
    ConcreteCategory.congr_hom (h.inr_desc _ _ _) z
  refine ⟨fun x hx ↦ ?_, fun y' hy' ↦ ?_⟩
  · have := hb y
    rw [← hx, hr, if_neg hy] at this
    simp at this
  · have := hb y'
    rw [hy', hb, if_neg hy] at this
    split_ifs at this
    exact (Option.some.inj this).symm

end CategoryTheory.Limits.Types

namespace CategoryTheory

open Limits Opposite

universe v' u'

variable {C : Type u'} [Category.{v'} C]

theorem eq_of_isPushout_of_not_exists {X₀ X₁ X₂ X : Cᵒᵖ ⥤ Type v'} {f₁ : X₀ ⟶ X₁}
    {f₂ : X₀ ⟶ X₂} {g₁ : X₁ ⟶ X} {g₂ : X₂ ⟶ X} (h : IsPushout f₁ f₂ g₁ g₂) {a : C}
    {y y' : yoneda.obj a ⟶ X₁} (hy : y ≫ g₁ = y' ≫ g₁)
    (hn : ¬∃ y₂ : yoneda.obj a ⟶ X₂, y₂ ≫ g₂ = y ≫ g₁) : y = y' := by
  have hx : g₁.app (op a) (yonedaEquiv y) = g₁.app (op a) (yonedaEquiv y') := by
    rw [← yonedaEquiv_comp, ← yonedaEquiv_comp, hy]
  by_cases hr : yonedaEquiv y ∈ Set.range (f₁.app (op a))
  · obtain ⟨s, hs⟩ := hr
    refine (hn ⟨yonedaEquiv.symm s ≫ f₂, ?_⟩).elim
    have hs' : yonedaEquiv.symm s ≫ f₁ = y := yonedaEquiv.injective (by
      rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
      exact hs)
    rw [Category.assoc, ← h.w, ← Category.assoc, hs']
  · exact yonedaEquiv.injective ((Types.eq_of_isPushout_of_notMem_range
      (h.map ((evaluation Cᵒᵖ (Type v')).obj (op a))).flip hr).2 _ hx.symm).symm

end CategoryTheory
