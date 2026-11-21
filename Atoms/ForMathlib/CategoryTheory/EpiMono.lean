import Mathlib.CategoryTheory.EpiMono

universe v u

namespace CategoryTheory

variable {A : Type u} [Category.{v} A]

theorem isSplitEpi_of_comp {x y z : A} (g : x ⟶ y) (f : y ⟶ z) [IsSplitEpi (g ≫ f)] :
    IsSplitEpi f :=
  IsSplitEpi.mk' ⟨section_ (g ≫ f) ≫ g, by rw [Category.assoc]; exact IsSplitEpi.id (g ≫ f)⟩

theorem deg_lt_of_isSplitEpi_of_not_isIso {deg : A → ℕ}
    (hle : ∀ ⦃a b : A⦄ (i : a ⟶ b), Mono i → deg a ≤ deg b)
    (hiso : ∀ ⦃a b : A⦄ (i : a ⟶ b), Mono i → deg a = deg b → IsIso i)
    {a b : A} (p : a ⟶ b) [IsSplitEpi p] (hp : ¬ IsIso p) : deg b < deg a := by
  refine lt_of_le_of_ne (hle (section_ p) inferInstance) fun h ↦ hp ?_
  have := hiso (section_ p) inferInstance h
  exact IsIso.of_epi_section p

end CategoryTheory
