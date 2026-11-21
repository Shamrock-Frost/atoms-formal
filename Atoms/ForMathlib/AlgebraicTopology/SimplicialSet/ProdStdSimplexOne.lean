import Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplexOne

open CategoryTheory Simplicial MonoidalCategory CartesianMonoidalCategory

universe u

namespace SSet

theorem stdSimplex.edge_one_cases (x : (Δ[1] : SSet.{u}) _⦋1⦌) :
    x = yonedaEquiv (stdSimplex.map (SimplexCategory.const ⦋1⦌ ⦋1⦌ 0)) ∨
      x = yonedaEquiv (𝟙 Δ[1]) ∨
        x = yonedaEquiv (stdSimplex.map (SimplexCategory.const ⦋1⦌ ⦋1⦌ 1)) := by
  obtain ⟨i, rfl⟩ := stdSimplex.objMk₁_surjective x
  fin_cases i
  · exact Or.inr (Or.inr (stdSimplex.ext _ _ fun t => by fin_cases t <;> rfl))
  · exact Or.inr (Or.inl (stdSimplex.ext _ _ fun t => by fin_cases t <;> rfl))
  · exact Or.inl (stdSimplex.ext _ _ fun t => by fin_cases t <;> rfl)

namespace prodStdSimplex

noncomputable def lowerTriangle : Δ[2] ⟶ (Δ[1] ⊗ Δ[1] : SSet.{u}) :=
  lift (stdSimplex.σ 1) (stdSimplex.σ 0)

noncomputable def upperTriangle : Δ[2] ⟶ (Δ[1] ⊗ Δ[1] : SSet.{u}) :=
  lift (stdSimplex.σ 0) (stdSimplex.σ 1)

theorem δ_zero_lowerTriangle : stdSimplex.δ 0 ≫ lowerTriangle.{u} =
    lift (stdSimplex.map (SimplexCategory.const ⦋1⦌ ⦋1⦌ 1)) (𝟙 Δ[1]) :=
  yonedaEquiv.injective (Prod.ext (stdSimplex.ext _ _ fun t => by fin_cases t <;> rfl)
    (stdSimplex.ext _ _ fun t => by fin_cases t <;> rfl))

theorem δ_one_lowerTriangle : stdSimplex.δ 1 ≫ lowerTriangle.{u} = lift (𝟙 Δ[1]) (𝟙 Δ[1]) :=
  yonedaEquiv.injective (Prod.ext (stdSimplex.ext _ _ fun t => by fin_cases t <;> rfl)
    (stdSimplex.ext _ _ fun t => by fin_cases t <;> rfl))

theorem δ_two_lowerTriangle : stdSimplex.δ 2 ≫ lowerTriangle.{u} =
    lift (𝟙 Δ[1]) (stdSimplex.map (SimplexCategory.const ⦋1⦌ ⦋1⦌ 0)) :=
  yonedaEquiv.injective (Prod.ext (stdSimplex.ext _ _ fun t => by fin_cases t <;> rfl)
    (stdSimplex.ext _ _ fun t => by fin_cases t <;> rfl))

theorem δ_zero_upperTriangle : stdSimplex.δ 0 ≫ upperTriangle.{u} =
    lift (𝟙 Δ[1]) (stdSimplex.map (SimplexCategory.const ⦋1⦌ ⦋1⦌ 1)) :=
  yonedaEquiv.injective (Prod.ext (stdSimplex.ext _ _ fun t => by fin_cases t <;> rfl)
    (stdSimplex.ext _ _ fun t => by fin_cases t <;> rfl))

theorem δ_one_upperTriangle : stdSimplex.δ 1 ≫ upperTriangle.{u} = lift (𝟙 Δ[1]) (𝟙 Δ[1]) :=
  yonedaEquiv.injective (Prod.ext (stdSimplex.ext _ _ fun t => by fin_cases t <;> rfl)
    (stdSimplex.ext _ _ fun t => by fin_cases t <;> rfl))

theorem δ_two_upperTriangle : stdSimplex.δ 2 ≫ upperTriangle.{u} =
    lift (stdSimplex.map (SimplexCategory.const ⦋1⦌ ⦋1⦌ 0)) (𝟙 Δ[1]) :=
  yonedaEquiv.injective (Prod.ext (stdSimplex.ext _ _ fun t => by fin_cases t <;> rfl)
    (stdSimplex.ext _ _ fun t => by fin_cases t <;> rfl))

end prodStdSimplex

end SSet
