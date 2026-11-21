import Atoms.Diagrammatic.MappingSpaceComparison
import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.CommaConePoint

open CategoryTheory Limits Simplicial MonoidalClosed HomotopicalAlgebra Opposite
open Atoms.Shape Atoms.Homotopical

universe u

namespace Atoms.Diagrammatic

open SSet

@[reassoc]
theorem grayHomSimplicialComparison_app_comp_evalVertex (C : MarkedSSet.{u})
    {K : SSet.{u}} (a : K _⦋0⦌) :
    (grayHomSimplicialComparison K).app C ≫
        DiagSet.toSSet.map (grayHomEvalVertex a (faceNerveRight.obj C)) =
      SSet.evalVertex a ((MarkedPresheaf.forget (D := edgeMarking)).obj C) ≫
        faceNerveRightComparison.app C := by
  let Q := (MarkedPresheaf.forget (D := edgeMarking)).obj C
  have he : (pre (SSet.yonedaEquiv.symm a)).app Q =
      SSet.evalVertex a Q ≫ SSet.constDiagram Δ[0] Q := by
    apply (cancel_mono (SSet.evalVertex (SSet.yonedaEquiv (𝟙 Δ[0])) Q)).1
    simp only [Category.assoc, SSet.constDiagram_comp_evalVertex, Category.comp_id,
        SSet.pre_app_comp_evalVertex]
    rw [← SSet.yonedaEquiv_comp, Category.id_comp, Equiv.apply_symm_apply]
  have hc : constDiagram (SSet.toDiagSet.obj Δ[0]) (faceNerveRight.obj C) ≫
      (grayHomRestrict pointIsoToDiagSetStdSimplex.hom).app _ ≫
        grayHomRightPointIso.hom.app _ = 𝟙 _ := by
    rw [← Category.assoc, constDiagram_comp_grayHomRestrict,
      constDiagram_comp_grayHomRightPointIso_hom_app]
  rw [grayHomEvalVertex, grayHomRestrict_comp, NatTrans.comp_app, Category.assoc,
    Functor.map_comp, ← pre_app_comp_grayHomSimplicialComparison_app_assoc, he,
    Category.assoc, constDiagram_comp_grayHomSimplicialComparison_app_assoc,
    ← Functor.map_comp, hc, DiagSet.toSSet.map_id, Category.comp_id]

theorem boundaryComparison_comp_end (C : MarkedSSet.{u}) (α : Bool) :
    boundaryComparison C ≫ DiagSet.toSSet.map
        (cond α (grayHomBoundaryFan (faceNerveRight.obj C)).snd
          (grayHomBoundaryFan (faceNerveRight.obj C)).fst) =
      SSet.evalVertex
        (SSet.yonedaEquiv (SSet.boundary.ι (cond α 0 1) :
          Δ[0] ⟶ (∂Δ[1] : SSet.{u})))
        ((MarkedPresheaf.forget (D := edgeMarking)).obj C) ≫
          faceNerveRightComparison.app C := by
  have hi : cond α (coprod.inr : ball.{u} atomPoint ⟶ intervalBoundary)
      coprod.inl ≫ intervalBoundaryToDiagSet =
      pointIsoToDiagSetStdSimplex.hom ≫
        SSet.toDiagSet.map (SSet.boundary.ι (cond α 0 1)) := by
    cases α <;> simp only [cond_false, cond_true, intervalBoundaryToDiagSet,
      coprod.inl_desc, coprod.inr_desc]
  have he : (grayHomRestrict intervalBoundaryToDiagSet).app (faceNerveRight.obj C) ≫
        cond α (grayHomBoundaryFan (faceNerveRight.obj C)).snd
          (grayHomBoundaryFan (faceNerveRight.obj C)).fst =
      grayHomEvalVertex (SSet.yonedaEquiv
        (SSet.boundary.ι (cond α 0 1) : Δ[0] ⟶ (∂Δ[1] : SSet.{u})))
          (faceNerveRight.obj C) := by
    have e : cond α (grayHomBoundaryFan (faceNerveRight.obj C)).snd
        (grayHomBoundaryFan (faceNerveRight.obj C)).fst =
        (grayHomRestrict (cond α (coprod.inr : ball.{u} atomPoint ⟶ intervalBoundary)
          coprod.inl)).app _ ≫ grayHomRightPointIso.hom.app _ := by
      cases α <;> rfl
    exact (congrArg ((grayHomRestrict intervalBoundaryToDiagSet).app _ ≫ ·) e).trans (by
      rw [grayHomEvalVertex, Equiv.symm_apply_apply]
      exact (Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ grayHomRightPointIso.hom.app _)
          ((NatTrans.congr_app (grayHomRestrict_comp _ _) _).symm.trans
            (congrArg (fun f => (grayHomRestrict f).app _) hi))))
  rw [boundaryComparison, Category.assoc, ← Functor.map_comp, he]
  exact grayHomSimplicialComparison_app_comp_evalVertex C _

private theorem terminal_vertex_comparison (C : MarkedSSet.{u})
    {c₀ : ((MarkedPresheaf.forget (D := edgeMarking)).obj C) _⦋0⦌}
    {y : (faceNerveRight.obj C).Vertex}
    (h : (faceNerveRightComparison.app C).app _ c₀ =
      (faceNerveRight.obj C).vertexEquivSSet y) :
    SSet.stdSimplex.isTerminalObj₀.from _ ≫ SSet.yonedaEquiv.symm c₀ ≫
        faceNerveRightComparison.app C =
      faceNerveRightComparison.app C ≫
        DiagSet.toSSet.map (isTerminalBallAtomPoint.from _ ≫ vertexHom y) := by
  rw [SSet.yonedaEquiv_symm_comp, h, ← toSSetPoint_comp_toSSet_map_vertexHom,
    DiagSet.toSSet.map_comp, ← Category.assoc, ← Category.assoc]
  apply congrArg (fun f : ((MarkedPresheaf.forget (D := edgeMarking)).obj C) ⟶
    DiagSet.toSSet.obj (ball atomPoint) => f ≫ DiagSet.toSSet.map (vertexHom y))
  exact isTerminalToSSetBallAtomPoint.hom_ext _ _

private theorem commaConeBase_comp_boundaryComparison (C : MarkedSSet.{u})
    {c₀ : ((MarkedPresheaf.forget (D := edgeMarking)).obj C) _⦋0⦌}
    {y : (faceNerveRight.obj C).Vertex}
    (h : (faceNerveRightComparison.app C).app _ c₀ =
      (faceNerveRight.obj C).vertexEquivSSet y) :
    SSet.commaConeBase (SSet.yonedaEquiv.symm c₀) ≫
        (ihom (∂Δ[1] : SSet.{u})).map
          (SSet.evalVertex (SSet.yonedaEquiv (𝟙 Δ[0])) _) ≫ boundaryComparison C =
      faceNerveRightComparison.app C ≫
        DiagSet.toSSet.map (boundaryHom (𝟙 _) (isTerminalBallAtomPoint.from _ ≫ vertexHom y)) := by
  let Y := faceNerveRight.obj C
  have ends (α : Bool) :
      (SSet.commaConeBase (SSet.yonedaEquiv.symm c₀) ≫
        (ihom (∂Δ[1] : SSet.{u})).map
          (SSet.evalVertex (SSet.yonedaEquiv (𝟙 Δ[0])) _) ≫ boundaryComparison C) ≫
          DiagSet.toSSet.map (cond α (grayHomBoundaryFan Y).snd
            (grayHomBoundaryFan Y).fst) =
      (faceNerveRightComparison.app C ≫ DiagSet.toSSet.map
        (boundaryHom (𝟙 _) (isTerminalBallAtomPoint.from _ ≫ vertexHom y))) ≫
          DiagSet.toSSet.map (cond α (grayHomBoundaryFan Y).snd
            (grayHomBoundaryFan Y).fst) := by
    have he := boundaryComparison_comp_end C α
    have hb := commaConeBase_comp_eval_end (SSet.yonedaEquiv.symm c₀) α
    refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) he).trans (Category.assoc _ _ _).symm))).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hb).trans ?_)))
    refine Eq.trans ?_ ((congrArg (_ ≫ ·) (DiagSet.toSSet.map_comp _ _)).trans
      (Category.assoc _ _ _).symm)
    cases α
    · exact (Category.id_comp _).trans ((Category.comp_id _).symm.trans
        (congrArg (_ ≫ ·) ((DiagSet.toSSet.map_id _).symm.trans (congrArg DiagSet.toSSet.map
          (boundaryHom_comp_grayHomBoundaryFan_fst _ _).symm))))
    · exact (terminal_vertex_comparison C h).trans (congrArg (_ ≫ ·)
        (congrArg DiagSet.toSSet.map (boundaryHom_comp_grayHomBoundaryFan_snd _ _).symm))
  exact BinaryFan.IsLimit.hom_ext ((isLimitMapConeBinaryFanEquiv DiagSet.toSSet _ _)
    (isLimitOfPreserves DiagSet.toSSet (isLimitGrayHomBoundaryFan Y)))
    (ends false) (ends true)

noncomputable def commaConeToConeObject (C : MarkedSSet.{u})
    {c₀ : ((MarkedPresheaf.forget (D := edgeMarking)).obj C) _⦋0⦌}
    {y : (faceNerveRight.obj C).Vertex}
    (h : (faceNerveRightComparison.app C).app _ c₀ =
      (faceNerveRight.obj C).vertexEquivSSet y) :
    SSet.commaCone (SSet.yonedaEquiv.symm c₀) ⟶
      DiagSet.toSSet.obj (coneObject true (vertexHom y)) :=
  (DiagSet.toSSet.map_isPullback (isPullback_coneObject_vertexHom true y)).lift
    (SSet.commaConeArrow _ ≫ (ihom (Δ[1] : SSet.{u})).map
      (SSet.evalVertex (SSet.yonedaEquiv (𝟙 Δ[0])) _) ≫ intervalComparison C)
    (SSet.commaConeπ _ ≫ faceNerveRightComparison.app C) (by
      rw [Category.assoc, Category.assoc, ← pre_app_comp_boundaryComparison,
        ← Category.assoc, ← Category.assoc,
        (isPullback_commaCone_point (SSet.yonedaEquiv.symm c₀)).w,
        Category.assoc, Category.assoc, commaConeBase_comp_boundaryComparison C h]
      rfl)

@[reassoc]
theorem commaConeToConeObject_π (C : MarkedSSet.{u})
    {c₀ : ((MarkedPresheaf.forget (D := edgeMarking)).obj C) _⦋0⦌}
    {y : (faceNerveRight.obj C).Vertex}
    (h : (faceNerveRightComparison.app C).app _ c₀ =
      (faceNerveRight.obj C).vertexEquivSSet y) :
    commaConeToConeObject C h ≫ DiagSet.toSSet.map (coneObjectπ true (vertexHom y)) =
      SSet.commaConeπ _ ≫ faceNerveRightComparison.app C :=
  IsPullback.lift_snd _ _ _ _

private theorem vertex_boundaryHom {Y : DiagSet.{u}} (x y : Y.Vertex) :
    vertexHom x ≫ boundaryHom (𝟙 Y) (isTerminalBallAtomPoint.from Y ≫ vertexHom y) =
      Y.endpointsPoint x y := by
  have ht : isTerminalBallAtomPoint.from (ball.{u} atomPoint) = 𝟙 _ :=
    isTerminalBallAtomPoint.hom_ext _ _
  apply BinaryFan.IsLimit.hom_ext (isLimitGrayHomBoundaryFan Y)
  · exact (Category.assoc _ _ _).trans
      ((congrArg (vertexHom x ≫ ·) (boundaryHom_comp_grayHomBoundaryFan_fst _ _)).trans
        ((Category.comp_id _).trans
          ((DiagSet.endpointsPoint_comp_grayHomBoundaryFan_fst x y).trans
            ((congrArg (· ≫ vertexHom x) ht).trans (Category.id_comp _))).symm))
  · exact (Category.assoc _ _ _).trans
      ((congrArg (vertexHom x ≫ ·) (boundaryHom_comp_grayHomBoundaryFan_snd _ _)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ vertexHom y) (isTerminalBallAtomPoint.hom_ext _ _)).trans
            (DiagSet.endpointsPoint_comp_grayHomBoundaryFan_snd x y).symm)))

noncomputable def mappingSpaceToConeObject {Y : DiagSet.{u}} (x y : Y.Vertex) :
    (Y.mappingSpace x y).toFunctor ⟶ coneObject true (vertexHom y) :=
  (isPullback_coneObject_vertexHom true y).lift (Y.mappingSpace x y).ι
    (isTerminalBallAtomPoint.from _ ≫ vertexHom x) (by
      simp only [cond_true]
      rw [Category.assoc, vertex_boundaryHom, (Y.isPullback_mappingSpace x y).w])

theorem isPullback_mappingSpaceToConeObject {Y : DiagSet.{u}} (x y : Y.Vertex) :
    IsPullback (mappingSpaceToConeObject x y) (isTerminalBallAtomPoint.from _)
      (coneObjectπ true (vertexHom y)) (vertexHom x) := by
  refine IsPullback.of_right ?_ (IsPullback.lift_snd _ _ _ _)
    (isPullback_coneObject_vertexHom true y)
  have hf : mappingSpaceToConeObject x y ≫ coneObjectι true (vertexHom y) ≫
      (grayHomRight (ball (atomSimplex 1))).map (grayHomRightPointIso.hom.app Y) =
      (Y.mappingSpace x y).ι := IsPullback.lift_fst _ _ _ _
  change IsPullback (mappingSpaceToConeObject x y ≫ coneObjectι true (vertexHom y) ≫
      (grayHomRight (ball (atomSimplex 1))).map (grayHomRightPointIso.hom.app Y))
    (isTerminalBallAtomPoint.from _) ((grayHomRestrict intervalBoundaryι).app Y)
    (vertexHom x ≫ boundaryHom (𝟙 Y) (isTerminalBallAtomPoint.from Y ≫ vertexHom y))
  rw [hf, vertex_boundaryHom]
  exact Y.isPullback_mappingSpace x y

@[reassoc]
private theorem mappingSpaceToConeObject_arrow {Y : DiagSet.{u}} (x y : Y.Vertex) :
    mappingSpaceToConeObject x y ≫ coneObjectι true (vertexHom y) ≫
        (grayHomRight (ball (atomSimplex 1))).map (grayHomRightPointIso.hom.app Y) =
      (Y.mappingSpace x y).ι := IsPullback.lift_fst _ _ _ _

@[reassoc]
private theorem mappingSpaceToConeObject_π {Y : DiagSet.{u}} (x y : Y.Vertex) :
    mappingSpaceToConeObject x y ≫ coneObjectπ true (vertexHom y) =
      isTerminalBallAtomPoint.from _ ≫ vertexHom x := IsPullback.lift_snd _ _ _ _

@[reassoc]
private theorem commaConeToConeObject_arrow (C : MarkedSSet.{u})
    {c₀ : ((MarkedPresheaf.forget (D := edgeMarking)).obj C) _⦋0⦌}
    {y : (faceNerveRight.obj C).Vertex}
    (h₀ : (faceNerveRightComparison.app C).app _ c₀ =
      (faceNerveRight.obj C).vertexEquivSSet y) :
    commaConeToConeObject C h₀ ≫ DiagSet.toSSet.map
      (coneObjectι true (vertexHom y) ≫
        (grayHomRight (ball (atomSimplex 1))).map (grayHomRightPointIso.hom.app _)) =
      SSet.commaConeArrow _ ≫ (ihom (Δ[1] : SSet.{u})).map
        (SSet.evalVertex (SSet.yonedaEquiv (𝟙 Δ[0])) _) ≫ intervalComparison C :=
  IsPullback.lift_fst _ _ _ _

theorem mappingSpaceToCommaCone_comp_commaConeToConeObject (C : MarkedSSet.{u})
    {c c₀ : ((MarkedPresheaf.forget (D := edgeMarking)).obj C) _⦋0⦌}
    {x y : (faceNerveRight.obj C).Vertex}
    (hc : (faceNerveRightComparison.app C).app _ c =
      (faceNerveRight.obj C).vertexEquivSSet x)
    (h₀ : (faceNerveRightComparison.app C).app _ c₀ =
      (faceNerveRight.obj C).vertexEquivSSet y) :
    mappingSpaceToCommaCone c c₀ ≫ commaConeToConeObject C h₀ =
      mappingSpaceToGray C hc h₀ ≫ DiagSet.toSSet.map (mappingSpaceToConeObject x y) := by
  apply (DiagSet.toSSet.map_isPullback
    (isPullback_coneObject_vertexHom true y)).hom_ext
  · simp only [Category.assoc, commaConeToConeObject_arrow,
      mappingSpaceToCommaCone_arrow_assoc]
    rw [← Functor.map_comp, mappingSpaceToConeObject_arrow, mappingSpaceToGray_ι]
    rfl
  · simp only [Category.assoc, commaConeToConeObject_π, mappingSpaceToCommaCone_π_assoc]
    rw [← Functor.map_comp, mappingSpaceToConeObject_π, Functor.map_comp]
    have hv : SSet.yonedaEquiv.symm c ≫ faceNerveRightComparison.app C =
        toSSetPoint ≫ DiagSet.toSSet.map (vertexHom x) := by
      rw [SSet.yonedaEquiv_symm_comp, hc, toSSetPoint_comp_toSSet_map_vertexHom]
    calc
      _ = pullback.snd _ _ ≫ toSSetPoint ≫ DiagSet.toSSet.map (vertexHom x) :=
        congrArg (pullback.snd _ _ ≫ ·) hv
      _ = _ := by
        simp only [← Category.assoc]
        congr 1
        exact isTerminalToSSetBallAtomPoint.hom_ext _ _

section WeakEquivalence

open SSet.modelCategoryJoyal MarkedSSet.modelCategoryCartesian

theorem weakEquivalence_commaConeToConeObject (C : MarkedSSet.{u}) [IsFibrant C]
    {c₀ : ((MarkedPresheaf.forget (D := edgeMarking)).obj C) _⦋0⦌}
    {y : (faceNerveRight.obj C).Vertex}
    (h : (faceNerveRightComparison.app C).app _ c₀ =
      (faceNerveRight.obj C).vertexEquivSSet y) :
    WeakEquivalence (commaConeToConeObject C h) := by
  have hG : IsInftyCategory 1 (faceNerveRight.obj C) :=
    (isFibrant_infty_iff 1 _).1 (isQuillen_faceNerveAdjunction.isFibrant_obj C)
  have : SSet.Quasicategory ((MarkedPresheaf.forget (D := edgeMarking)).obj C) :=
    (isFibrant_iff_quasicategory _).1
      (Atoms.Homotopical.isQuillenEquivalence_flatForgetAdjunction.toIsQuillen.isFibrant_obj C)
  have : Fibration ((pre (∂Δ[1]).ι).app
      ((MarkedPresheaf.forget (D := edgeMarking)).obj C)) :=
    (SSet.modelCategoryJoyal.fibration_iff_isofibration _).2
      (SSet.isofibration_pre_boundaryOne _)
  have : IsFibrant ((ihom (∂Δ[1] : SSet.{u})).obj
      ((MarkedPresheaf.forget (D := edgeMarking)).obj C)) :=
    (isFibrant_iff_quasicategory _).2 inferInstance
  obtain ⟨_, _⟩ := fibration_toSSet_map_grayHomRestrict_and_isFibrant hG
  have := weakEquivalence_grayHomSimplicialComparison_app Δ[1] C
  have := weakEquivalence_grayHomSimplicialComparison_app (∂Δ[1] : SSet.{u}) C
  have : WeakEquivalence (intervalComparison C) := by
    dsimp only [intervalComparison]
    infer_instance
  have : WeakEquivalence (boundaryComparison C) := by
    dsimp only [boundaryComparison]
    infer_instance
  have := (isFibrant_iff_quasicategory _).2
    (inferInstance : SSet.Quasicategory ((MarkedPresheaf.forget (D := edgeMarking)).obj C))
  have := isFibrant_toSSet_obj hG
  have := weakEquivalence_faceNerveRightComparison_app C
  exact (isPullback_commaCone_point (SSet.yonedaEquiv.symm c₀)).weakEquivalence_map_of_fibration
    (DiagSet.toSSet.map_isPullback (isPullback_coneObject_vertexHom true y))
    (intervalComparison C) (boundaryComparison C) (faceNerveRightComparison.app C)
    (commaConeToConeObject C h) (pre_app_comp_boundaryComparison C)
    (commaConeBase_comp_boundaryComparison C h)
    (IsPullback.lift_fst _ _ _ _) (IsPullback.lift_snd _ _ _ _)

end WeakEquivalence

end Atoms.Diagrammatic
