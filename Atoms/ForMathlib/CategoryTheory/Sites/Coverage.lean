import Mathlib.CategoryTheory.Sites.Coverage

universe w v u

namespace CategoryTheory.Presieve

open Opposite

variable {C : Type u} [Category.{v} C]

theorem isSeparated_coverage (K : Coverage C) (P : Cᵒᵖ ⥤ Type w) :
    IsSeparated K.toGrothendieck P ↔ ∀ {X : C} (R : Presieve X), R ∈ K X → IsSeparatedFor P R := by
  refine ⟨fun H X R hR => isSeparatedFor_iff_generate.2 (H _ (Coverage.Saturate.of _ _ hR)),
    fun H X S hS => ?_⟩
  suffices h : ∀ (X : C) (S : Sieve X), K.Saturate X S → ∀ x y : P.obj (op X),
      (∀ ⦃Y⦄ (f : Y ⟶ X), S f → P.map f.op x = P.map f.op y) → x = y from
    fun x t₁ t₂ h₁ h₂ => h X S hS t₁ t₂ fun Y f hf => (h₁ f hf).trans (h₂ f hf).symm
  intro X S hS
  induction hS with
  | of X R hR =>
    exact fun x y h => (H R hR).ext fun _ f hf => h f (Sieve.le_generate R _ f hf)
  | top X =>
    exact fun x y h => by simpa using h (𝟙 X) trivial
  | transitive X R S _ _ ihR ihS =>
    refine fun x y h => ihR x y fun Y f hf => ihS hf (P.map f.op x) (P.map f.op y) fun Z g hg => ?_
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp]
    exact h _ hg

end CategoryTheory.Presieve
