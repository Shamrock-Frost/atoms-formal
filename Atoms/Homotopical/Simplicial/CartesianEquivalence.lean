import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.CartesianIsofibration
import Atoms.Homotopical.Simplicial.FibrewiseEquivalence

open CategoryTheory Limits HomotopicalAlgebra

universe u

namespace SSet.modelCategoryJoyal

theorem fibration_of_isCartesianFibration {X S : SSet.{u}} [X.Quasicategory] [S.Quasicategory]
    (p : X ⟶ S) [IsCartesianFibration p] : Fibration p :=
  (fibration_iff_isofibration p).2 (isofibration_of_isCartesianFibration p)

theorem weakEquivalence_iff_trivialFibration_of_isCartesianFibration {X S : SSet.{u}}
    [X.Quasicategory] [S.Quasicategory] (p : X ⟶ S) [IsCartesianFibration p] :
    WeakEquivalence p ↔ modelCategoryQuillen.I.rlp p := by
  refine ⟨fun _ ↦ ?_, weakEquivalence_of_rlp_I⟩
  have := fibration_of_isCartesianFibration p
  have h : (cofibrations SSet.{u}).rlp p := by
    rw [cofibrations_rlp]
    exact mem_trivialFibrations p
  rw [← rlp_monomorphisms]
  exact h

theorem weakEquivalence_pullback_fst_of_isCartesianFibration {C D D' : SSet.{u}}
    [C.Quasicategory] [D.Quasicategory] [D'.Quasicategory] (p : C ⟶ D) [IsCartesianFibration p]
    (q : D' ⟶ D) [WeakEquivalence q] : WeakEquivalence (pullback.fst p q) := by
  have := (isFibrant_iff_quasicategory D).2 inferInstance
  have := (isFibrant_iff_quasicategory D').2 inferInstance
  have := fibration_of_isCartesianFibration p
  exact weakEquivalence_pullback_fst_of_fibration p q

end SSet.modelCategoryJoyal
