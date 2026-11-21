import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.RelativeFibre
import Atoms.Homotopical.Simplicial.CartesianMonoidal
import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Product
import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Over

open CategoryTheory Limits Simplicial MonoidalCategory MonoidalClosed HomotopicalAlgebra

universe u

namespace SSet

open Atoms.Homotopical SSet.modelCategoryJoyal

theorem fibration_ihomEvalVertices {S : SSet.{u}} {p : ℕ}
    (v : Fin (p + 1) → S _⦋0⦌) [Mono (simplicialShapeVerticesι v)]
    (Q : SSet.{u}) [Q.Quasicategory] : Fibration (SSet.ihomEvalVertices v Q) := by
  have : Fibration ((pre (simplicialShapeVerticesι v)).app Q) :=
    (SSet.modelCategoryJoyal.fibration_iff_isofibration _).2
      (SSet.isofibration_pullbackObjObjπ (terminal.from Q) (simplicialShapeVerticesι v)
        (Functor.PullbackObjObj.ofIsTerminal _ _ _ terminalIsTerminal))
  rw [← pre_simplicialShapeVerticesι_comp_ihomVerticesIso]
  infer_instance

theorem weakEquivalence_simplicialVertexFibreTargetMap {S Q Q' : SSet.{u}} {p : ℕ}
    (v : Fin (p + 1) → S _⦋0⦌) [Mono (simplicialShapeVerticesι v)]
    [Q.Quasicategory] [Q'.Quasicategory] (f : Q ⟶ Q') [WeakEquivalence f]
    (c : Fin (p + 1) → Q _⦋0⦌) :
    WeakEquivalence (simplicialVertexFibreTargetMap v f c) := by
  have : IsFibrant Q := (isFibrant_iff_quasicategory Q).2 inferInstance
  have : IsFibrant Q' := (isFibrant_iff_quasicategory Q').2 inferInstance
  have : IsFibrant ((ihom (∐ fun _ : Fin (p + 1) => (Δ[0] : SSet.{u}))).obj Q) :=
    (isQuillen_ihomAdjunction _).isFibrant_obj Q
  have : IsFibrant (∏ᶜ fun _ : Fin (p + 1) => Q) :=
    isFibrant_of_fibration (ihomVerticesIso p Q).inv
  have : IsFibrant ((ihom (∐ fun _ : Fin (p + 1) => (Δ[0] : SSet.{u}))).obj Q') :=
    (isQuillen_ihomAdjunction _).isFibrant_obj Q'
  have : IsFibrant (∏ᶜ fun _ : Fin (p + 1) => Q') :=
    isFibrant_of_fibration (ihomVerticesIso p Q').inv
  have := fibration_ihomEvalVertices v Q
  have := fibration_ihomEvalVertices v Q'
  have := (isQuillen_ihomAdjunction S).weakEquivalence_map_of_isFibrant f
  have := weakEquivalence_piMap (fun _ : Fin (p + 1) => f)
  have : IsFibrant (Δ[0] : SSet.{u}) :=
    (isFibrant_iff_of_isTerminal (𝟙 _) SSet.stdSimplex.isTerminalObj₀).2 inferInstance
  exact (IsPullback.of_hasPullback (SSet.ihomEvalVertices v Q) _).weakEquivalence_map_of_fibration
      (IsPullback.of_hasPullback (SSet.ihomEvalVertices v Q') _)
      ((ihom S).map f) (Limits.Pi.map fun _ => f) (𝟙 _)
      (simplicialVertexFibreTargetMap v f c) (ihomEvalVertices_target v f).symm
      (by
        rw [Category.id_comp]
        apply Pi.hom_ext
        intro k
        rw [Category.assoc, Limits.Pi.map_π, Pi.lift_π_assoc, Pi.lift_π,
          SSet.yonedaEquiv_symm_comp])
      (simplicialVertexFibreTargetMap_ι v f c)
      (SSet.stdSimplex.isTerminalObj₀.hom_ext _ _)

theorem weakEquivalence_simplicialVertexFibreTargetMapOfEq {S Q Q' : SSet.{u}} {p : ℕ}
    (v : Fin (p + 1) → S _⦋0⦌) [Mono (simplicialShapeVerticesι v)]
    [Q.Quasicategory] [Q'.Quasicategory] (f : Q ⟶ Q') [WeakEquivalence f]
    (c : Fin (p + 1) → Q _⦋0⦌) (d : Fin (p + 1) → Q' _⦋0⦌)
    (h : ∀ k, f.app _ (c k) = d k) :
    WeakEquivalence (simplicialVertexFibreTargetMapOfEq v f c d h) := by
  obtain rfl : (fun k => f.app _ (c k)) = d := funext h
  exact weakEquivalence_simplicialVertexFibreTargetMap v f c

end SSet
