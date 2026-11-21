import Atoms.Diagrammatic.Fibration.MarkedRightAnodyne
import Atoms.Diagrammatic.Fibration.CartesianMarkingBox

open CategoryTheory Limits Opposite HomotopicalAlgebra Atoms.Homotopical Atoms.Shape

universe u

namespace Atoms.Diagrammatic

theorem DiagSet.rlp_rightCylinderMaps_cartesianMarkedHom_of_sphere
    {E S : DiagSet.{u}} (p : E ⟶ S) [DiagSet.IsCartesianFibration p]
    [IsFibrant ((DiagSet.toInfty 1).obj S)]
    (hs : ∀ (U : Atom), 0 < U.dimension → HasLiftingProperty
      (Functor.PushoutObjObj.ofHasPushout
        (Functor.curry.obj (markedTensorBifunctor.{u} false))
        ((MarkedPresheaf.flat atomMarking).map (sphereInclusion U))
        (markedIntervalVertex true)).ι (DiagSet.cartesianMarkedHom p)) :
    MarkedDiagSet.rightCylinderMaps.rlp (DiagSet.cartesianMarkedHom p) := by
  apply MarkedDiagSet.rlp_rightCylinderMaps_of_generators
  · intro U
    by_cases hU : 0 < U.dimension
    · exact hs U hU
    · have hzero : U.dimension = 0 := by omega
      have := isIso_toAtomPoint_of_dimension_eq_zero hzero
      let i := asIso (toAtomPoint U)
      let e : Arrow.mk (sphereInclusion.{u} U) ≅ Arrow.mk (sphereInclusion atomPoint) :=
        Arrow.isoMk ((DiagSet.isInitialSphereOfDimensionEqZero U hzero).uniqueUpToIso
          (DiagSet.isInitialSphereOfDimensionEqZero atomPoint dimension_atomPoint))
          (uliftYoneda.mapIso i)
          ((DiagSet.isInitialSphereOfDimensionEqZero U hzero).hom_ext _ _)
      let b := Functor.PushoutObjObj.ι_iso_of_iso_left
        (f₂ := Arrow.mk (markedIntervalVertex.{u} true))
        (Functor.PushoutObjObj.ofHasPushout
          (Functor.curry.obj (markedTensorBifunctor false)) _ _)
        (Functor.PushoutObjObj.ofHasPushout _ _ _)
        ((MarkedPresheaf.flat atomMarking).mapArrow.mapIso e)
      have := DiagSet.hasLiftingProperty_markedIntervalVertex_cartesianMarkedHom p
      have := MarkedDiagSet.hasLiftingProperty_pushoutProduct_flat_sphere_atomPoint
        (DiagSet.cartesianMarkedHom p)
      exact (HasLiftingProperty.iff_of_arrow_iso_left b.symm
        (DiagSet.cartesianMarkedHom p)).1 this
  · intro U hU
    by_cases h : 1 < U.dimension
    · exact DiagSet.hasLiftingProperty_pushoutProduct_markingInclusion_above_one p U h
    · exact DiagSet.hasLiftingProperty_pushoutProduct_markingInclusion_dimension_one p U
        (by omega)

end Atoms.Diagrammatic
