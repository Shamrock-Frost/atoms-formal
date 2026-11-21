import Atoms.Diagrammatic.Joyal.GrayHomComparison

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra Atoms.Homotopical
open MorphismProperty

universe u

namespace Atoms.Diagrammatic

open SSet.modelCategoryJoyal MarkedSSet.modelCategoryCartesian

theorem DiagSet.exists_relative_faceNerveReplacement {E S : DiagSet.{u}} (p : E ⟶ S) :
    ∃ (CE CS : MarkedSSet.{u}) (_ : IsFibrant CE) (_ : IsFibrant CS)
      (c : CE ⟶ CS) (_ : Fibration c)
      (ηE : E ⟶ faceNerveRight.obj CE) (ηS : S ⟶ faceNerveRight.obj CS),
      WeakEquivalence ((DiagSet.toInfty 1).map ηE) ∧
        WeakEquivalence ((DiagSet.toInfty 1).map ηS) ∧
        ηE ≫ faceNerveRight.map c = p ≫ ηS := by
  obtain ⟨CS, hCS, ηS, hηS, -⟩ := exists_weakEquivalence_faceNerveRight S
  let φ := factorizationData (trivialCofibrations MarkedSSet.{u}) (fibrations _)
    ((faceNerveAdjunction.homEquiv ((DiagSet.toInfty 1).obj E) CS).symm (p ≫ ηS))
  have : Fibration φ.p := (fibration_iff _).2 φ.hp
  have : IsFibrant φ.Z := isFibrant_of_fibration φ.p
  have hi : WeakEquivalence φ.i := (weakEquivalence_iff _).2 φ.hi.2
  refine ⟨φ.Z, CS, inferInstance, hCS, φ.p, inferInstance,
    faceNerveAdjunction.homEquiv ((DiagSet.toInfty 1).obj E) φ.Z φ.i, ηS,
    (isQuillenEquivalence_faceNerveAdjunction.weakEquivalence_iff
      (A := (DiagSet.toInfty 1).obj E) φ.i).1 hi, hηS, ?_⟩
  exact (faceNerveAdjunction.homEquiv_naturality_right φ.i φ.p).symm.trans
    ((congrArg (faceNerveAdjunction.homEquiv ((DiagSet.toInfty 1).obj E) CS) φ.fac).trans
      (Equiv.apply_symm_apply _ _))

end Atoms.Diagrammatic
