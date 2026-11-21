import Mathlib.AlgebraicTopology.SimplicialObject.Basic

namespace CategoryTheory

instance SimplicialObject.isSplitMono_σ {C : Type*} [Category* C] (X : SimplicialObject C) {n : ℕ}
    (i : Fin (n + 1)) : IsSplitMono (X.σ i) :=
  IsSplitMono.mk' ⟨X.δ i.castSucc, X.δ_comp_σ_self⟩

end CategoryTheory
