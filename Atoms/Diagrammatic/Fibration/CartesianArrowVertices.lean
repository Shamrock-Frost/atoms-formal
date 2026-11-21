import Atoms.Diagrammatic.Fibration.CartesianArrowObject
import Atoms.Diagrammatic.Joyal.GrayTensorModel
import Atoms.Diagrammatic.Joyal.GrayLeibnizComparison

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra Atoms.Shape Atoms.Homotopical

universe u

namespace Atoms.Diagrammatic

variable {E S : DiagSet.{u}}

noncomputable def DiagSet.toSSetGrayHomPointEquiv (K : SSet.{u}) (X : DiagSet.{u}) :
    (Δ[0] ⟶ DiagSet.toSSet.obj ((grayHomRight (SSet.toDiagSet.obj K)).obj X)) ≃
      (K ⟶ DiagSet.toSSet.obj X) :=
  (DiagSet.Infty.sSetDiagSetAdj.homEquiv _ _).symm.trans
    (((grayTensorRightAdjunction (SSet.toDiagSet.obj K)).homEquiv _ _).symm.trans
      ((Iso.homCongr
        ((grayTensorRight (SSet.toDiagSet.obj K)).mapIso
          pointIsoToDiagSetStdSimplex.symm ≪≫ GrayDiagSet.leftUnitor _) (Iso.refl X)).trans
            (DiagSet.Infty.sSetDiagSetAdj.homEquiv _ _)))

theorem DiagSet.toSSetGrayHomPointEquiv_comparison (K : SSet.{u}) (C : MarkedSSet.{u})
    (b : Δ[0] ⟶ (ihom K).obj ((MarkedPresheaf.forget (D := edgeMarking)).obj C)) :
    DiagSet.toSSetGrayHomPointEquiv K (faceNerveRight.obj C)
        (b ≫ (grayHomSimplicialComparison K).app C) =
      SSet.ihomPointEquiv K _ b ≫ faceNerveRightComparison.app C := by
  apply (DiagSet.toSSetGrayHomPointEquiv K (faceNerveRight.obj C)).symm.injective
  rw [Equiv.symm_apply_apply]
  have hp : grayTensorSnd (SSet.toDiagSet.obj Δ[0]) (SSet.toDiagSet.obj K) =
      ((grayTensorRight (SSet.toDiagSet.obj K)).mapIso
        pointIsoToDiagSetStdSimplex.symm ≪≫ GrayDiagSet.leftUnitor _).hom := by
    dsimp only [grayTensorSnd, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
    have h : isTerminalBallAtomPoint.from (SSet.toDiagSet.obj Δ[0]) =
        pointIsoToDiagSetStdSimplex.{u}.inv := isTerminalBallAtomPoint.hom_ext _ _
    rw [h]
    rfl
  have hc := grayHomSimplicialComparison_app_point K C b
  rw [hp] at hc
  exact hc.symm

theorem DiagSet.grayArrowVertexEquiv_comparison (C : MarkedSSet.{u})
    (b : Δ[0] ⟶ (ihom Δ[1]).obj ((MarkedPresheaf.forget (D := edgeMarking)).obj C)) :
    SSet.yonedaEquiv.symm ((faceNerveRight.obj C).edgeEquivSSet (DiagSet.Edge.ofCell
        (DiagSet.grayArrowVertexEquiv (faceNerveRight.obj C) (SSet.yonedaEquiv
          (b ≫ (grayHomSimplicialComparison Δ[1]).app C ≫ DiagSet.toSSet.map
            ((grayHomRestrict markedIntervalVertexArrowIso.inv.right).app
              (faceNerveRight.obj C))))))).edge =
      SSet.ihomPointEquiv Δ[1] _ b ≫ faceNerveRightComparison.app C := by
  let X : DiagSet.{u} := faceNerveRight.obj C
  let i : markedInterval.{u}.underlying ⟶ SSet.toDiagSet.obj (Δ[1] : SSet.{u}) :=
    markedIntervalVertexArrowIso.{u}.inv.right
  let q := SSet.ihomPointEquiv Δ[1] _ b ≫ faceNerveRightComparison.app C
  have hc := grayHomSimplicialComparison_app_vertex Δ[1] C (SSet.yonedaEquiv b)
  rw [Equiv.symm_apply_apply] at hc
  have hp := grayTensorSnd_unit markedInterval.{u}.underlying
  let z := ((grayHomSimplicialComparison Δ[1]).app C).app _ (SSet.yonedaEquiv b)
  have hv : SSet.yonedaEquiv
      (b ≫ (grayHomSimplicialComparison Δ[1]).app C ≫ DiagSet.toSSet.map
        ((grayHomRestrict i).app X)) = ((grayHomRestrict i).app X).app _ z := by
    rw [SSet.yonedaEquiv_comp]
    rfl
  refine (congrArg SSet.yonedaEquiv.symm ((DiagSet.edgeEquivSSet_edge _).trans
    (congrArg (fun c => X.map atomSimplexOneIsoGlobe.hom.op c)
      ((DiagSet.grayArrowVertexEquiv_apply X _).trans
        (congrArg DiagSet.intervalHomVertexCell hv))))).trans ?_
  apply (sSetDiagSetAdj.homEquiv _ _).symm.injective
  refine (homEquiv_symm_yonedaEquiv_symm (X := X) (n := 1) _).trans ?_
  dsimp only [DiagSet.intervalHomVertexCell]
  rw [uliftYonedaEquiv_symm_map,
    Equiv.symm_apply_apply]
  have hr := grayHomRightCellEquiv_grayHomRestrict i X (atomSimplex 0) z
  change (toDiagSetObjStdSimplexIso 1).hom ≫ uliftYoneda.map atomSimplexOneIsoGlobe.hom ≫
    intervalBallIso.hom ≫ (GrayDiagSet.leftUnitor markedInterval.underlying).inv ≫
      grayHomRightCellEquiv markedInterval.underlying X atomPoint
          (((grayHomRestrict i).app X).app (op atomPoint) z) =
    (sSetDiagSetAdj.homEquiv _ _).symm q
  refine (congrArg (fun F => (toDiagSetObjStdSimplexIso 1).hom ≫
    uliftYoneda.map atomSimplexOneIsoGlobe.hom ≫ intervalBallIso.hom ≫
      (GrayDiagSet.leftUnitor markedInterval.underlying).inv ≫ F) hr).trans ?_
  refine (congrArg (fun F => (toDiagSetObjStdSimplexIso 1).hom ≫
    uliftYoneda.map atomSimplexOneIsoGlobe.hom ≫ intervalBallIso.hom ≫
      (GrayDiagSet.leftUnitor markedInterval.underlying).inv ≫
        (grayTensorLeft (ball (atomSimplex 0))).map i ≫ F) hc).trans ?_
  have ht : (grayTensorLeft (ball.{u} atomPoint)).map i ≫
      grayTensorSnd (ball.{u} atomPoint) (SSet.toDiagSet.obj Δ[1]) =
      grayTensorSnd (ball.{u} atomPoint) markedInterval.underlying ≫ i :=
    grayTensorBifunctor_map_grayTensorSnd (𝟙 _) i
  change (toDiagSetObjStdSimplexIso 1).hom ≫ uliftYoneda.map atomSimplexOneIsoGlobe.hom ≫
    intervalBallIso.hom ≫ (GrayDiagSet.leftUnitor markedInterval.underlying).inv ≫
      (grayTensorLeft (ball atomPoint)).map i ≫
        grayTensorSnd (ball atomPoint) (SSet.toDiagSet.obj (Δ[1] : SSet.{u})) ≫
          (sSetDiagSetAdj.homEquiv _ X).symm q = (sSetDiagSetAdj.homEquiv _ X).symm q
  rw [← Category.assoc _ _ ((sSetDiagSetAdj.homEquiv _ X).symm q), ht, hp,
    Category.assoc, Iso.inv_hom_id_assoc]
  have hi : uliftYoneda.map atomSimplexOneIsoGlobe.hom ≫ intervalBallIso.hom ≫ i =
      (toDiagSetObjStdSimplexIso 1).inv := by
    let B := ballIsoForgetYoneda.{u}
      (MarkedSite.marked (atomGlobe 1) markable_atomGlobe_one)
    refine (congrArg (fun F => uliftYoneda.map atomSimplexOneIsoGlobe.hom ≫
      intervalBallIso.hom ≫ F) markedIntervalVertexArrowIso_inv_right).trans ?_
    exact (congrArg (uliftYoneda.map atomSimplexOneIsoGlobe.hom ≫ ·)
      (B.hom_inv_id_assoc (uliftYoneda.map atomSimplexOneIsoGlobe.inv ≫
        (toDiagSetObjStdSimplexIso 1).inv))).trans
          ((uliftYoneda.mapIso atomSimplexOneIsoGlobe).hom_inv_id_assoc _)
  exact (congrArg (fun F => (toDiagSetObjStdSimplexIso 1).hom ≫ F ≫
    (sSetDiagSetAdj.homEquiv _ X).symm q) hi).trans
      ((toDiagSetObjStdSimplexIso 1).hom_inv_id_assoc _)

private theorem isCartesianEdge_intervalHomVertexCell_of_isEquivalence (p : E ⟶ S)
    [Fibration ((DiagSet.toInfty 1).map p)] [IsFibrant ((DiagSet.toInfty 1).obj S)]
    {x y : ((grayHomRight markedInterval.{u}.underlying).obj E).Vertex}
    (e : ((grayHomRight markedInterval.underlying).obj E).Edge x y)
    (he : IsEquivalence _ e.cell)
    (hy : DiagSet.IsCartesianEdge p (DiagSet.Edge.ofCell (DiagSet.intervalHomVertexCell y))) :
    DiagSet.IsCartesianEdge p (DiagSet.Edge.ofCell (DiagSet.intervalHomVertexCell x)) := by
  have hr (ε : Bool) : DiagSet.IsCartesianEdge p
      (DiagSet.graySquareRightEdge (DiagSet.graySquareOfIntervalHom e.cell) ε) := by
    have hc : (DiagSet.graySquareRightEdge (DiagSet.graySquareOfIntervalHom e.cell) ε).cell =
        (e.map (DiagSet.intervalHomEval E ε)).cell := by
      cases ε
      · exact DiagSet.graySquareOfIntervalHom_right_src e
      · exact DiagSet.graySquareOfIntervalHom_right_tgt e
    exact (DiagSet.isCartesianEdge_congr p
      (e := DiagSet.graySquareRightEdge (DiagSet.graySquareOfIntervalHom e.cell) ε)
      (e' := e.map (DiagSet.intervalHomEval E ε)) hc).2
      (DiagSet.isCartesianEdge_of_isEquivalence _ (he.map _))
  have ht := (DiagSet.isCartesianEdge_congr p
    (e := DiagSet.graySquareLeftEdge (DiagSet.graySquareOfIntervalHom e.cell) true)
    (e' := DiagSet.Edge.ofCell (DiagSet.intervalHomVertexCell y))
    (DiagSet.graySquareOfIntervalHom_left_tgt e)).2 hy
  exact (DiagSet.isCartesianEdge_congr p
    (e := DiagSet.graySquareLeftEdge (DiagSet.graySquareOfIntervalHom e.cell) false)
    (e' := DiagSet.Edge.ofCell (DiagSet.intervalHomVertexCell x))
    (DiagSet.graySquareOfIntervalHom_left_src e)).1
    (DiagSet.IsCartesianEdge.of_graySquare_left _ (hr false) (hr true) ht)

theorem DiagSet.isCartesianEdge_grayArrowVertex_iff_of_isEquivalence (p : E ⟶ S)
    [Fibration ((DiagSet.toInfty 1).map p)] [IsFibrant ((DiagSet.toInfty 1).obj S)]
    {x y : ((grayHomRight markedInterval.{u}.underlying).obj E).Vertex}
    (e : ((grayHomRight markedInterval.underlying).obj E).Edge x y)
    (he : IsEquivalence _ e.cell) :
    DiagSet.IsCartesianEdge p (DiagSet.Edge.ofCell (DiagSet.grayArrowVertexEquiv E x)) ↔
      DiagSet.IsCartesianEdge p (DiagSet.Edge.ofCell (DiagSet.grayArrowVertexEquiv E y)) := by
  simp only [DiagSet.grayArrowVertexEquiv_apply]
  refine ⟨?_, isCartesianEdge_intervalHomVertexCell_of_isEquivalence p e he⟩
  have hE := isInftyCategory_of_isFibrant 1 ((DiagSet.toInfty 1).obj E)
    (isFibrant_of_fibration ((DiagSet.toInfty 1).map p))
  have hA := isInftyCategory_grayHomRight markedInterval.underlying hE
  have : IsIso (HomotopyCategory.homMk hA.1 e) :=
    (HomotopyCategory.isIso_homMk_iff hA.1 e).2 he
  obtain ⟨d, hd⟩ := HomotopyCategory.homMk_surjective hA.1
    (inv (HomotopyCategory.homMk hA.1 e))
  have hdIso : IsIso (HomotopyCategory.homMk hA.1 d) := by rw [hd]; infer_instance
  exact isCartesianEdge_intervalHomVertexCell_of_isEquivalence p d
    ((HomotopyCategory.isIso_homMk_iff hA.1 d).1 hdIso)

end Atoms.Diagrammatic
