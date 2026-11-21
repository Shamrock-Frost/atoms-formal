import Atoms.Diagrammatic.Fibration.CartesianArrowComparison
import Atoms.Diagrammatic.Fibration.CartesianCylinder
import Atoms.Diagrammatic.Fibration.SliceContraction

open CategoryTheory Limits Opposite HomotopicalAlgebra Atoms.Homotopical Atoms.Shape

universe u

namespace Atoms.Diagrammatic

theorem DiagSet.rlp_rightCylinderMaps_cartesianMarkedHom {E S : DiagSet.{u}} (p : E ⟶ S)
    [DiagSet.IsCartesianFibration p] [IsFibrant ((DiagSet.toInfty 1).obj S)] :
    MarkedDiagSet.rightCylinderMaps.rlp (DiagSet.cartesianMarkedHom p) :=
  DiagSet.rlp_rightCylinderMaps_cartesianMarkedHom_of_sphere p
    fun U _ ↦ DiagSet.hasLiftingProperty_pushoutProduct_flat_map_cartesianMarkedHom p
      (sphereInclusion U)

theorem DiagSet.trivialFibration_cartesianYoneda {E S : DiagSet.{u}} (p : E ⟶ S)
    [DiagSet.IsCartesianFibration p] [IsFibrant ((DiagSet.toInfty 1).obj S)] (b : S.Vertex) :
    (MorphismProperty.monomorphisms DiagSet.{u}).rlp (DiagSet.cartesianYonedaEval p b) :=
  DiagSet.trivialFibration_cartesianYoneda_of_rlp_rightCylinderMaps p b
    (DiagSet.rlp_rightCylinderMaps_cartesianMarkedHom p)

open SSet.modelCategoryJoyal in
theorem DiagSet.cartesianFunOver_comparison {E S : DiagSet.{u}} (p : E ⟶ S)
    [DiagSet.IsCartesianFibration p] [IsFibrant ((DiagSet.toInfty 1).obj S)] (b : S.Vertex) :
    letI := (DiagSet.isCartesianFibration_iff_toSSet p).1 inferInstance
    ∃ f : DiagSet.toSSet.obj (DiagSet.cartesianFunOver p b) ⟶
        SSet.cartesianFunOver (DiagSet.toSSet.map p) (S.vertexEquivSSet b),
      WeakEquivalence f ∧
        f ≫ SSet.cartesianYonedaEval (DiagSet.toSSet.map p) (S.vertexEquivSSet b) =
          DiagSet.toSSet.map (DiagSet.cartesianYonedaEval p b) ≫
            (DiagSet.toSSetFiberIso p b).hom :=
  letI := (DiagSet.isCartesianFibration_iff_toSSet p).1 inferInstance
  DiagSet.cartesianFunOver_comparison_of_rlp p b (DiagSet.trivialFibration_cartesianYoneda p b)

end Atoms.Diagrammatic
