import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.CartesianFiberSequence
import Atoms.Homotopical.Simplicial.CommaLimit
import Atoms.Homotopical.Simplicial.FibrewiseEquivalence

open CategoryTheory Limits Simplicial HomotopicalAlgebra

universe u

namespace SSet.modelCategoryJoyal

theorem exists_weakEquivalence_fiber_sliceAtFiberMap {X S : SSet.{u}} (p : X ⟶ S)
    [InnerFibration p] {x x' y : X _⦋0⦌} (e : Edge x' y)
    (he : IsLocallyCartesianEdge p (yonedaEquiv.symm e.edge)) (hx : p.app _ x = p.app _ x') :
    ∃ (F : SSet.{u})
      (a : F ⟶ pullback (sliceAtFiberMap p hx rfl)
        (yonedaEquiv.symm ((sliceAtFiberVerticesEquiv S _ _).symm (e.map p))))
      (b : F ⟶ mappingSpace (pullback p (yonedaEquiv.symm (p.app _ x')))
        (fiberVertex p x hx) (fiberVertex p x' rfl)),
      WeakEquivalence a ∧ WeakEquivalence b := by
  obtain ⟨F, a, b, ha, hb⟩ := exists_trivialFibrations_fiber_sliceAtFiberMap p e he hx
  have : (pullback p (yonedaEquiv.symm (p.app _ x'))).Quasicategory :=
    quasicategory_of_innerFibration (pullback.snd _ _)
  have := weakEquivalence_of_rlp_I hb
  have := weakEquivalence_sliceAtFibreToMappingSpace (fiberVertex p x hx) (fiberVertex p x' rfl)
  exact ⟨F, a, b ≫ sliceAtFibreToMappingSpace _ _ _, weakEquivalence_of_rlp_I ha, inferInstance⟩

end SSet.modelCategoryJoyal
