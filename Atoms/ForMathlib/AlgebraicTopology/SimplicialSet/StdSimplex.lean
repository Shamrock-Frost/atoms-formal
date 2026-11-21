import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

universe u

open CategoryTheory Simplicial

namespace SSet

lemma hom_ext_yonedaEquiv_symm {X Y : SSet.{u}} {f g : X ⟶ Y}
    (h : ∀ (n : ℕ) (σ : X _⦋n⦌), yonedaEquiv.symm σ ≫ f = yonedaEquiv.symm σ ≫ g) : f = g := by
  ext n σ
  have := congrArg yonedaEquiv (h n.unop.len σ)
  rwa [yonedaEquiv_comp, yonedaEquiv_comp, Equiv.apply_symm_apply] at this

end SSet
