import Atoms.Diagrammatic.Fibration.CartesianFibration
import Atoms.Diagrammatic.Fibration.RightFibration
import Atoms.Diagrammatic.KanComparison

open CategoryTheory Limits Opposite MorphismProperty HomotopicalAlgebra Simplicial Atoms.Shape

universe u

namespace Atoms.Diagrammatic

variable {E S : DiagSet.{u}}

theorem DiagSet.isPullback_toSSet_fiber (p : E ⟶ S) (b : S.Vertex) :
    IsPullback (DiagSet.toSSet.map (pullback.fst p (uliftYonedaEquiv.symm b)))
      (DiagSet.toSSet.map (pullback.snd p (uliftYonedaEquiv.symm b)) ≫ toSSetObjBallPointIso.hom)
      (DiagSet.toSSet.map p) (SSet.yonedaEquiv.symm (S.vertexEquivSSet b)) :=
  ((IsPullback.of_hasPullback p (uliftYonedaEquiv.symm b)).map DiagSet.toSSet).of_iso
    (Iso.refl _) (Iso.refl _) toSSetObjBallPointIso (Iso.refl _) (by simp) (by simp) (by simp)
    (by
      rw [← toSSetPoint_comp_toSSet_map_vertexHom b]
      exact (Iso.hom_inv_id_assoc toSSetObjBallPointIso _).symm)

noncomputable def DiagSet.toSSetFiberIso (p : E ⟶ S) (b : S.Vertex) :
    DiagSet.toSSet.obj (pullback p (uliftYonedaEquiv.symm b)) ≅
      pullback (DiagSet.toSSet.map p) (SSet.yonedaEquiv.symm (S.vertexEquivSSet b)) :=
  (DiagSet.isPullback_toSSet_fiber p b).isoPullback

@[reassoc (attr := simp)]
theorem DiagSet.toSSetFiberIso_hom_fst (p : E ⟶ S) (b : S.Vertex) :
    (DiagSet.toSSetFiberIso p b).hom ≫ pullback.fst _ _ =
      DiagSet.toSSet.map (pullback.fst p (uliftYonedaEquiv.symm b)) :=
  (DiagSet.isPullback_toSSet_fiber p b).isoPullback_hom_fst

instance DiagSet.isFibrant_fiber (p : E ⟶ S) [Fibration ((DiagSet.toInfty 1).map p)]
    (b : S.Vertex) :
    IsFibrant ((DiagSet.toInfty 1).obj (pullback p (uliftYonedaEquiv.symm b))) := by
  have h : Fibration ((DiagSet.toInfty 1).map (pullback.snd p (uliftYonedaEquiv.symm b))) :=
    (fibration_toInfty_one_map_iff _).2 (MorphismProperty.of_isPullback
      (IsPullback.of_hasPullback p (uliftYonedaEquiv.symm b))
      ((fibration_toInfty_one_map_iff p).1 inferInstance))
  exact (isFibrant_iff_of_isTerminal
    ((DiagSet.toInfty 1).map (pullback.snd p (uliftYonedaEquiv.symm b)))
    isTerminalBallAtomPoint).2 h

theorem DiagSet.isRightFibration_iff_isCartesianFibration_and_forall (p : E ⟶ S)
    [Fibration ((DiagSet.toInfty 1).map p)] [IsFibrant ((DiagSet.toInfty 1).obj S)] :
    DiagSet.IsRightFibration p ↔ DiagSet.IsCartesianFibration p ∧
      ∀ ⦃x y : E.Vertex⦄ (e : E.Edge x y), DiagSet.IsCartesianEdge p e := by
  rw [DiagSet.isRightFibration_iff_rightFibrations_toSSet,
    SSet.rightFibrations_iff_isCartesianFibration_and_forall,
    DiagSet.isCartesianFibration_iff_toSSet]
  refine and_congr_right fun _ ↦ ⟨fun h x y e ↦ ?_, fun h f ↦ ?_⟩
  · exact (DiagSet.isCartesianEdge_iff_isCartesianEdge_toSSet_of_fibration p e).2 (h _)
  · obtain ⟨x, y, e, he⟩ := DiagSet.exists_edgeEquivSSet_edge_eq (SSet.yonedaEquiv f)
    obtain rfl : SSet.yonedaEquiv.symm (E.edgeEquivSSet e).edge = f := by
      rw [he, Equiv.symm_apply_apply]
    exact (h e).isCartesianEdge_toSSet

open SSet.modelCategoryQuillen in
theorem DiagSet.isRightFibration_iff_isCartesianFibration_and_fiber (p : E ⟶ S)
    [Fibration ((DiagSet.toInfty 1).map p)] [IsFibrant ((DiagSet.toInfty 1).obj S)] :
    DiagSet.IsRightFibration p ↔ DiagSet.IsCartesianFibration p ∧
      ∀ b : S.Vertex, IsInftyCategory 0 (pullback p (uliftYonedaEquiv.symm b)) := by
  have hfib (b : S.Vertex) : IsInftyCategory 0 (pullback p (uliftYonedaEquiv.symm b)) ↔
      (pullback (DiagSet.toSSet.map p)
        (SSet.yonedaEquiv.symm (S.vertexEquivSSet b))).KanComplex :=
    (kanComplex_toSSet_obj_iff (X := pullback p (uliftYonedaEquiv.symm b))
      (isInftyCategory_of_isFibrant 1 _ (DiagSet.isFibrant_fiber p b))).symm.trans
      ⟨fun _ ↦ isFibrant_of_fibration (DiagSet.toSSetFiberIso p b).inv,
        fun _ ↦ isFibrant_of_fibration (DiagSet.toSSetFiberIso p b).hom⟩
  refine ⟨fun hp ↦ ⟨((DiagSet.isRightFibration_iff_isCartesianFibration_and_forall p).1 hp).1,
    fun b ↦ (hfib b).2 (SSet.kanComplex_fiber_of_rightFibrations
      ((DiagSet.isRightFibration_iff_rightFibrations_toSSet p).1 hp) _)⟩, fun ⟨hp, h⟩ ↦ ?_⟩
  have := (DiagSet.isCartesianFibration_iff_toSSet p).1 hp
  exact (DiagSet.isRightFibration_iff_rightFibrations_toSSet p).2
    (SSet.rightFibrations_of_isCartesianFibration_of_kanComplex _ fun s ↦ (hfib s).1 (h s))

end Atoms.Diagrammatic
