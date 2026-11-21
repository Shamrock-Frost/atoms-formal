import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.CartesianFibration
import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.Isofibration

open CategoryTheory Limits Simplicial

universe u

namespace SSet

theorem isofibration_of_isCartesianFibration {X S : SSet.{u}} [X.Quasicategory] [S.Quasicategory]
    (p : X ⟶ S) [IsCartesianFibration p] : Isofibration p where
  exists_lift x₀ y₁ g hg := by
    obtain ⟨I⟩ := hg
    obtain ⟨h, hhp, hh₀, hh⟩ := IsCartesianFibration.exists_isCartesianEdge (p := p) x₀
      (yonedaEquiv.symm I.inv.edge) (by rw [stdSimplex.δ_comp_yonedaEquiv_symm, I.inv.tgt_eq])
    have hhp' : p.app _ (yonedaEquiv h) = I.inv.edge := by
      rw [← yonedaEquiv_comp, hhp, Equiv.apply_symm_apply]
    have hh₀' : X.δ 0 (yonedaEquiv h) = x₀ := by
      rw [← stdSimplex.yonedaEquiv_δ_comp, hh₀, Equiv.apply_symm_apply]
    obtain ⟨σ, hσ₀, hσ₁, hσ⟩ := exists_simplex_two_of_isCartesianEdge hh (X.σ 0 x₀)
      ((δ_comp_σ_self_apply (S := X) (n := 0) 0 x₀).trans hh₀'.symm) I.homInvId.simplex
      (I.homInvId.d₀.trans hhp'.symm)
      (I.homInvId.d₁.trans (σ_naturality_apply p 0 x₀).symm)
    have hsrc : X.δ 1 (X.δ 2 σ) = x₀ := (δ_comp_δ_self_apply (i := 1) σ).symm.trans
      ((congrArg _ hσ₁).trans (δ_comp_σ_succ_apply (S := X) 0 x₀))
    have hinv : Nonempty (Edge.mk' (X.δ 0 σ)).InvStruct := by
      rw [hσ₀]
      refine ((invStruct_iff_isCartesianEdge p h).2 ⟨hh, ⟨I.invStructInv.ofEq ?_⟩⟩)
      rw [Edge.mk'_edge, yonedaEquiv_comp, hhp']
    obtain ⟨J⟩ := nonempty_invStruct_δ_two σ hinv (by rw [hσ₁]; exact nonempty_invStruct_σ x₀)
    exact ⟨X.δ 0 (X.δ 2 σ), Edge.mk (X.δ 2 σ) hsrc rfl, ⟨J.ofEq rfl⟩,
      (δ_naturality_apply p 2 σ).trans ((congrArg _ hσ).trans I.homInvId.d₂)⟩

end SSet
