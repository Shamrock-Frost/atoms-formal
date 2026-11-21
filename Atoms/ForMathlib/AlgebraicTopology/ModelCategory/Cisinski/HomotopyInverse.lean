import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Cisinski.TrivialFibration

open CategoryTheory Limits

namespace HomotopicalAlgebra.ExactCylinder

universe w v u

variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C] (𝕀 : ExactCylinder.{w} C)

theorem homotopic_of_left_inverse_of_right_inverse {X Y : C} {f : X ⟶ Y} {g h : Y ⟶ X}
    (hg : 𝕀.Homotopic (f ≫ g) (𝟙 X)) (hh : 𝕀.Homotopic (h ≫ f) (𝟙 Y)) : 𝕀.Homotopic g h := by
  have h₁ : 𝕀.Homotopic g ((h ≫ f) ≫ g) := by
    simpa using 𝕀.homotopic_comp (Relation.EqvGen.symm _ _ hh) g
  have h₂ : 𝕀.Homotopic (h ≫ f ≫ g) h := by
    simpa using 𝕀.homotopic_precomp h hg
  exact Relation.EqvGen.trans _ _ _ h₁ ((Category.assoc h f g).symm ▸ h₂)

theorem homotopyInverse_of_left_inverse_of_right_inverse {X Y : C} {f : X ⟶ Y} {g h : Y ⟶ X}
    (hg : 𝕀.Homotopic (f ≫ g) (𝟙 X)) (hh : 𝕀.Homotopic (h ≫ f) (𝟙 Y)) :
    𝕀.Homotopic (g ≫ f) (𝟙 Y) ∧ 𝕀.Homotopic (f ≫ h) (𝟙 X) := by
  have e := 𝕀.homotopic_of_left_inverse_of_right_inverse hg hh
  exact ⟨Relation.EqvGen.trans _ _ _ (𝕀.homotopic_comp e f) hh,
    Relation.EqvGen.trans _ _ _ (𝕀.homotopic_precomp f (Relation.EqvGen.symm _ _ e)) hg⟩

end HomotopicalAlgebra.ExactCylinder
