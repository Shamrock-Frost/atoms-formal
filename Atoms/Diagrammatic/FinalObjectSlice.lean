import Atoms.Diagrammatic.CosliceProjection
import Atoms.Diagrammatic.Fibration.SliceContraction
import Atoms.Diagrammatic.FinalObjectComparison
import Atoms.Homotopical.Simplicial.CosliceInitial

open CategoryTheory Limits Simplicial MorphismProperty HomotopicalAlgebra
open Atoms.Homotopical Atoms.Shape SSet.modelCategoryQuillen

universe u

namespace Atoms.Diagrammatic

variable {X : DiagSet.{u}}

theorem DiagSet.rlp_monomorphisms_sliceAtProj_iff (hX : IsInftyCategory 1 X) (t : X.Vertex) :
    (monomorphisms DiagSet.{u}).rlp (X.sliceAtProj t) ↔
      I.rlp (SSet.sliceAtπ (DiagSet.toSSet.obj X) (X.vertexEquivSSet t)) := by
  have hX' : IsFibrant ((DiagSet.toInfty 1).obj X) := (isFibrant_infty_iff 1 X).2 hX
  have hp : Fibration ((DiagSet.toInfty 1).map (X.sliceAtProj t)) :=
    (DiagSet.isRightFibration_sliceProj (vertexHom t)).fibration
  have e : I.rlp (DiagSet.toSSet.map (X.sliceAtProj t)) ↔
      I.rlp (SSet.sliceAtπ (DiagSet.toSSet.obj X) (X.vertexEquivSSet t)) := by
    rw [← X.toSSetSliceAtIso_hom_comp_sliceAtπ t]
    exact (I.rlp).cancel_left_of_respectsIso _ _
  exact ⟨fun h ↦ e.1 (rlp_I_toSSet_map_of_rlp_monomorphisms h),
    fun h ↦ rlp_monomorphisms_of_rlp_I_toSSet_map (hB := hX') _ (e.2 h)⟩

theorem DiagSet.isFinalObject_iff_rlp_sliceProj (hX : IsInftyCategory 1 X) (t : X.Vertex) :
    X.IsFinalObject t ↔
      (monomorphisms DiagSet.{u}).rlp
        ((sliceProj (ball.{u} atomPoint)).app (Under.mk (vertexHom t))) := by
  have : (DiagSet.toSSet.obj X).Quasicategory :=
    quasicategory_toSSet_obj X ((isFibrant_infty_iff 1 X).2 hX)
  exact (DiagSet.isFinalObject_iff_isFinal hX t).trans
    ((SSet.isFinal_iff_trivialFibration_sliceAtπ _).trans
      (DiagSet.rlp_monomorphisms_sliceAtProj_iff hX t).symm)

theorem DiagSet.rlp_monomorphisms_sliceProj_of_isFinalObject (hX : IsInftyCategory 1 X)
    {t : X.Vertex} (ht : X.IsFinalObject t) :
    (monomorphisms DiagSet.{u}).rlp
      ((sliceProj (ball.{u} atomPoint)).app (Under.mk (vertexHom t))) :=
  (DiagSet.isFinalObject_iff_rlp_sliceProj hX t).1 ht

theorem DiagSet.IsFinalObject.hasLift_sliceAtProj (hX : IsInftyCategory 1 X) {t : X.Vertex}
    (ht : X.IsFinalObject t) {A B : DiagSet.{u}} {i : A ⟶ B} [Mono i] {a : A ⟶ X.sliceAt t}
    {b : B ⟶ X} (sq : CommSq a i (X.sliceAtProj t) b) : sq.HasLift :=
  (DiagSet.rlp_monomorphisms_sliceProj_of_isFinalObject hX ht i
    (monomorphisms.infer_property _)).sq_hasLift sq

theorem DiagSet.rlp_monomorphisms_cosliceProj_iff (hX : IsInftyCategory 1 X) (t : X.Vertex) :
    (monomorphisms DiagSet.{u}).rlp (cosliceProj (Under.mk (vertexHom t))) ↔
      I.rlp (SSet.cosliceπ (Under.mk (SSet.yonedaEquiv.symm (X.vertexEquivSSet t)))) := by
  have hX' : IsFibrant ((DiagSet.toInfty 1).obj X) := (isFibrant_infty_iff 1 X).2 hX
  have hp : Fibration ((DiagSet.toInfty 1).map (cosliceProj (Under.mk (vertexHom t)))) :=
    fibration_cosliceProj (vertexHom t)
  have e := rlp_I_toSSet_map_cosliceProj_vertexHom_iff t
  exact ⟨fun h ↦ e.1 (rlp_I_toSSet_map_of_rlp_monomorphisms h),
    fun h ↦ rlp_monomorphisms_of_rlp_I_toSSet_map (hB := hX') _ (e.2 h)⟩

theorem DiagSet.isInitialObject_iff_rlp_cosliceProj (hX : IsInftyCategory 1 X) (t : X.Vertex) :
    X.IsInitialObject t ↔
      (monomorphisms DiagSet.{u}).rlp (cosliceProj (Under.mk (vertexHom t))) := by
  have : (DiagSet.toSSet.obj X).Quasicategory :=
    quasicategory_toSSet_obj X ((isFibrant_infty_iff 1 X).2 hX)
  exact (DiagSet.isInitialObject_iff_isInitialObject hX t).trans
    ((SSet.isInitialObject_iff_trivialFibration_cosliceπ _).trans
      (DiagSet.rlp_monomorphisms_cosliceProj_iff hX t).symm)

theorem DiagSet.rlp_monomorphisms_cosliceProj_of_isInitialObject (hX : IsInftyCategory 1 X)
    {t : X.Vertex} (ht : X.IsInitialObject t) :
    (monomorphisms DiagSet.{u}).rlp (cosliceProj (Under.mk (vertexHom t))) :=
  (DiagSet.isInitialObject_iff_rlp_cosliceProj hX t).1 ht

theorem DiagSet.IsInitialObject.hasLift_cosliceProj (hX : IsInftyCategory 1 X) {t : X.Vertex}
    (ht : X.IsInitialObject t) {A B : DiagSet.{u}} {i : A ⟶ B} [Mono i]
    {a : A ⟶ (WithInitial.coslice (ball.{u} atomPoint)).obj (Under.mk (vertexHom t))} {b : B ⟶ X}
    (sq : CommSq a i (cosliceProj (Under.mk (vertexHom t))) b) : sq.HasLift :=
  (DiagSet.rlp_monomorphisms_cosliceProj_of_isInitialObject hX ht i
    (monomorphisms.infer_property _)).sq_hasLift sq

end Atoms.Diagrammatic
