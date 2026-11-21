import Atoms.Diagrammatic.MappingSpaceComparison
import Atoms.Diagrammatic.MappingSpacePiZeroComparison
import Atoms.Homotopical.Simplicial.PiZero
import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.MappingSpacePiZero

open CategoryTheory Limits Simplicial MonoidalClosed HomotopicalAlgebra Opposite
open Atoms.Shape Atoms.Homotopical

universe u

namespace Atoms.Diagrammatic

private theorem intervalComparison_app_vertex_edge (C : MarkedSSet.{u})
    (w : ((ihom Δ[1]).obj ((MarkedPresheaf.forget (D := edgeMarking)).obj C)) _⦋0⦌) :
    uliftYonedaEquiv (inv (grayTensorSnd (ball.{u} atomPoint) (ball (atomSimplex 1))) ≫
      grayHomRightCellEquiv (ball.{u} (atomSimplex 1)) (faceNerveRight.obj C) (atomSimplex 0)
        ((intervalComparison C).app (op ⦋0⦌) w)) =
      SSet.yonedaEquiv (SSet.ihomPointEquiv Δ[1] _ (SSet.yonedaEquiv.symm w) ≫
        faceNerveRightComparison.app C) := by
  let Z := faceNerveRight.obj C
  let I := ball.{u} (atomSimplex 1)
  let P := ball.{u} (atomSimplex 0)
  let q := SSet.ihomPointEquiv Δ[1] _ (SSet.yonedaEquiv.symm w)
  let g : SSet.toDiagSet.obj Δ[1] ⟶ Z :=
    (DiagSet.Infty.sSetDiagSetAdj.homEquiv _ _).symm (q ≫ faceNerveRightComparison.app C)
  have hr := grayHomRightCellEquiv_grayHomRestrict (toDiagSetObjStdSimplexIso 1).inv
    Z (atomSimplex 0) (((grayHomSimplicialComparison Δ[1]).app C).app (op ⦋0⦌) w)
  have hv := grayHomSimplicialComparison_app_vertex Δ[1] C w
  have hc := hr.trans
    (congrArg ((grayTensorLeft P).map (toDiagSetObjStdSimplexIso 1).inv ≫ ·) hv)
  refine (congrArg (fun t => uliftYonedaEquiv (inv (grayTensorSnd P I) ≫ t)) hc).trans ?_
  change uliftYonedaEquiv (inv (grayTensorSnd P I) ≫
    (grayTensorLeft P).map (toDiagSetObjStdSimplexIso 1).inv ≫
      grayTensorSnd P (SSet.toDiagSet.obj Δ[1]) ≫ g) = _
  have hg : inv (grayTensorSnd P I) ≫
      (grayTensorLeft P).map (toDiagSetObjStdSimplexIso 1).inv ≫
        grayTensorSnd P (SSet.toDiagSet.obj Δ[1]) = (toDiagSetObjStdSimplexIso 1).inv := by
    rw [grayTensorLeft_map_grayTensorSnd, IsIso.inv_hom_id_assoc]
  refine (congrArg uliftYonedaEquiv
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ g) hg))).trans ?_
  have ht := homEquiv_symm_yonedaEquiv_symm
    (SSet.yonedaEquiv (q ≫ faceNerveRightComparison.app C))
  have hg' := congrArg (DiagSet.Infty.sSetDiagSetAdj.homEquiv _ _).symm
    (SSet.yonedaEquiv.symm_apply_apply (q ≫ faceNerveRightComparison.app C)).symm
  exact (congrArg (fun t => uliftYonedaEquiv ((toDiagSetObjStdSimplexIso 1).inv ≫ t))
    (hg'.trans ht)).trans
      ((congrArg uliftYonedaEquiv (Iso.inv_hom_id_assoc _ _)).trans
        (uliftYonedaEquiv.apply_symm_apply _))

private theorem mappingSpaceToGray_app_vertex_edge (C : MarkedSSet.{u})
    {c₀ c₁ : ((MarkedPresheaf.forget (D := edgeMarking)).obj C) _⦋0⦌}
    {y₀ y₁ : (faceNerveRight.obj C).Vertex}
    (h₀ : (faceNerveRightComparison.app C).app _ c₀ = (faceNerveRight.obj C).vertexEquivSSet y₀)
    (h₁ : (faceNerveRightComparison.app C).app _ c₁ = (faceNerveRight.obj C).vertexEquivSSet y₁)
    (v : (SSet.mappingSpace ((MarkedPresheaf.forget (D := edgeMarking)).obj C) c₀ c₁) _⦋0⦌) :
    (DiagSet.edgeEquivSSet ((faceNerveRight.obj C).mappingSpaceVerticesEquiv y₀ y₁
        ((DiagSet.vertexEquivSSet _).symm ((mappingSpaceToGray C h₀ h₁).app _ v)))).edge =
      (faceNerveRightComparison.app C).app _
        (SSet.mappingSpaceVerticesEquiv _ c₀ c₁ v).edge := by
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (mappingSpaceToGray_ι C h₀ h₁) (op ⦋0⦌)) v
  have h' : (DiagSet.toSSet.map ((faceNerveRight.obj C).mappingSpace y₀ y₁).ι).app _
      ((mappingSpaceToGray C h₀ h₁).app _ v) =
    (intervalComparison C).app _ ((pullback.fst (SSet.ihomStdSimplexOneEval
      ((MarkedPresheaf.forget (D := edgeMarking)).obj C))
        (CartesianMonoidalCategory.lift (SSet.yonedaEquiv.symm c₀)
          (SSet.yonedaEquiv.symm c₁))).app _ v) := h
  refine (DiagSet.mappingSpaceVerticesEquiv_edge y₀ y₁ _).trans
    ((congrArg (fun t => uliftYonedaEquiv
      (inv (grayTensorSnd (ball.{u} atomPoint) (ball (atomSimplex 1))) ≫
        grayHomRightCellEquiv (ball.{u} (atomSimplex 1)) (faceNerveRight.obj C)
          (atomSimplex 0) t)) h').trans ?_)
  refine (intervalComparison_app_vertex_edge C _).trans ?_
  have he := SSet.mappingSpaceVerticesEquiv_edge_yoneda c₀ c₁ v
  exact (congrArg (fun q => SSet.yonedaEquiv (q ≫ faceNerveRightComparison.app C)) he.symm).trans
    ((SSet.yonedaEquiv_symm_comp _ _).symm ▸ SSet.yonedaEquiv.apply_symm_apply _)

theorem mappingSpaceToGray_app_vertex (C : MarkedSSet.{u})
    {c₀ c₁ : ((MarkedPresheaf.forget (D := edgeMarking)).obj C) _⦋0⦌}
    {y₀ y₁ : (faceNerveRight.obj C).Vertex}
    (h₀ : (faceNerveRightComparison.app C).app _ c₀ = (faceNerveRight.obj C).vertexEquivSSet y₀)
    (h₁ : (faceNerveRightComparison.app C).app _ c₁ = (faceNerveRight.obj C).vertexEquivSSet y₁)
    (v : (SSet.mappingSpace ((MarkedPresheaf.forget (D := edgeMarking)).obj C) c₀ c₁) _⦋0⦌)
    (e' : (faceNerveRight.obj C).Edge y₀ y₁)
    (he : (faceNerveRightComparison.app C).app _
        (SSet.mappingSpaceVerticesEquiv _ c₀ c₁ v).edge = (DiagSet.edgeEquivSSet e').edge) :
    (mappingSpaceToGray C h₀ h₁).app _ v =
      DiagSet.vertexEquivSSet _
        (((faceNerveRight.obj C).mappingSpaceVerticesEquiv y₀ y₁).symm e') := by
  apply ((DiagSet.vertexEquivSSet _).symm.trans
    ((faceNerveRight.obj C).mappingSpaceVerticesEquiv y₀ y₁)).injective
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  apply DiagSet.edgeEquivSSet.injective
  exact SSet.Edge.ext ((mappingSpaceToGray_app_vertex_edge C h₀ h₁ v).trans he)

theorem mappingSpaceπ₀Comparison_mappingSpaceToGray (C : MarkedSSet.{u})
    (hC : IsInftyCategory 1 (faceNerveRight.obj C))
    {c₀ c₁ : ((MarkedPresheaf.forget (D := edgeMarking)).obj C) _⦋0⦌}
    {y₀ y₁ : (faceNerveRight.obj C).Vertex}
    (h₀ : (faceNerveRightComparison.app C).app _ c₀ = (faceNerveRight.obj C).vertexEquivSSet y₀)
    (h₁ : (faceNerveRightComparison.app C).app _ c₁ = (faceNerveRight.obj C).vertexEquivSSet y₁)
    (a : SSet.π₀ (SSet.mappingSpace
      ((MarkedPresheaf.forget (D := edgeMarking)).obj C) c₀ c₁)) :
    mappingSpaceπ₀Comparison hC y₀ y₁ (SSet.mapπ₀ (mappingSpaceToGray C h₀ h₁) a) =
      SSet.mapπ₀ (SSet.mappingSpaceMapOfEq (faceNerveRightComparison.app C) h₀ h₁) a := by
  induction a with | mk v => ?_
  let e := (faceNerveRight.obj C).mappingSpaceVerticesEquiv y₀ y₁
    ((DiagSet.vertexEquivSSet _).symm ((mappingSpaceToGray C h₀ h₁).app _ v))
  have hv : (mappingSpaceToGray C h₀ h₁).app _ v =
      DiagSet.vertexEquivSSet _
        (((faceNerveRight.obj C).mappingSpaceVerticesEquiv y₀ y₁).symm e) := by
    exact ((congrArg (DiagSet.vertexEquivSSet _)
      (((faceNerveRight.obj C).mappingSpaceVerticesEquiv y₀ y₁).symm_apply_apply _)).trans
        ((DiagSet.vertexEquivSSet _).apply_symm_apply _)).symm
  rw [SSet.mapπ₀_mk, hv, mappingSpaceπ₀Comparison_mk, SSet.mapπ₀_mk]
  congr 1
  apply (SSet.mappingSpaceVerticesEquiv _ _ _).injective
  rw [Equiv.apply_symm_apply]
  apply SSet.Edge.ext
  exact (mappingSpaceToGray_app_vertex_edge C h₀ h₁ v).trans
    (SSet.mappingSpaceVerticesEquiv_mapOfEq (faceNerveRightComparison.app C) h₀ h₁ v).symm

theorem mappingSpaceπ₀Comparison_zigzag {X : DiagSet.{u}} (hX : IsInftyCategory 1 X)
    {C : MarkedSSet.{u}} (hC : IsInftyCategory 1 (faceNerveRight.obj C))
    (η : X ⟶ faceNerveRight.obj C) (x y : X.Vertex)
    {c₀ c₁ : ((MarkedPresheaf.forget (D := edgeMarking)).obj C) _⦋0⦌}
    (h₀ : (faceNerveRightComparison.app C).app _ c₀ =
      (faceNerveRight.obj C).vertexEquivSSet (x.map η))
    (h₁ : (faceNerveRightComparison.app C).app _ c₁ =
      (faceNerveRight.obj C).vertexEquivSSet (y.map η))
    (a : SSet.π₀ (DiagSet.toSSet.obj (X.mappingSpace x y).toFunctor))
    (b : SSet.π₀ (SSet.mappingSpace
      ((MarkedPresheaf.forget (D := edgeMarking)).obj C) c₀ c₁))
    (h : SSet.mapπ₀ (DiagSet.toSSet.map (X.mappingSpaceMap η x y)) a =
      SSet.mapπ₀ (mappingSpaceToGray C h₀ h₁) b) :
    SSet.mapπ₀ (SSet.mappingSpaceMap (DiagSet.toSSet.map η)
      (X.vertexEquivSSet x) (X.vertexEquivSSet y)) (mappingSpaceπ₀Comparison hX x y a) =
        SSet.mapπ₀ (SSet.mappingSpaceMapOfEq (faceNerveRightComparison.app C) h₀ h₁) b :=
  ((mappingSpaceπ₀Comparison_mapπ₀ hX hC η x y a).symm.trans
    (congrArg (mappingSpaceπ₀Comparison hC (x.map η) (y.map η)) h)).trans
      (mappingSpaceπ₀Comparison_mappingSpaceToGray C hC h₀ h₁ b)

open SSet.modelCategoryJoyal MarkedSSet.modelCategoryCartesian in
theorem mappingSpaceπ₀Comparison_eq_zigzag {X : DiagSet.{u}} (hX : IsInftyCategory 1 X)
    {C : MarkedSSet.{u}} [IsFibrant C] (hC : IsInftyCategory 1 (faceNerveRight.obj C))
    (η : X ⟶ faceNerveRight.obj C) [WeakEquivalence ((DiagSet.toInfty 1).map η)]
    (x y : X.Vertex)
    {c₀ c₁ : ((MarkedPresheaf.forget (D := edgeMarking)).obj C) _⦋0⦌}
    (h₀ : (faceNerveRightComparison.app C).app _ c₀ =
      (faceNerveRight.obj C).vertexEquivSSet (x.map η))
    (h₁ : (faceNerveRightComparison.app C).app _ c₁ =
      (faceNerveRight.obj C).vertexEquivSSet (y.map η))
    (a : SSet.π₀ (DiagSet.toSSet.obj (X.mappingSpace x y).toFunctor)) :
    let e := Equiv.ofBijective (SSet.mapπ₀ (mappingSpaceToGray C h₀ h₁))
      (SSet.bijective_mapπ₀_of_kanWeak (joyal_weakEquivalences_le_kanWeak _
        (weakEquivalence_mappingSpaceToGray C h₀ h₁).mem))
    let e' := Equiv.ofBijective (SSet.mapπ₀ (SSet.mappingSpaceMap (DiagSet.toSSet.map η)
      (X.vertexEquivSSet x) (X.vertexEquivSSet y)))
      (SSet.bijective_mapπ₀_of_kanWeak (joyal_weakEquivalences_le_kanWeak _
        (weakEquivalence_mappingSpaceMap_toSSet_map hX hC η _ _).mem))
    mappingSpaceπ₀Comparison hX x y a = e'.symm
      (SSet.mapπ₀ (SSet.mappingSpaceMapOfEq (faceNerveRightComparison.app C) h₀ h₁)
        (e.symm (SSet.mapπ₀ (DiagSet.toSSet.map (X.mappingSpaceMap η x y)) a))) := by
  let e := Equiv.ofBijective (SSet.mapπ₀ (mappingSpaceToGray C h₀ h₁))
    (SSet.bijective_mapπ₀_of_kanWeak (joyal_weakEquivalences_le_kanWeak _
      (weakEquivalence_mappingSpaceToGray C h₀ h₁).mem))
  let e' := Equiv.ofBijective (SSet.mapπ₀ (SSet.mappingSpaceMap (DiagSet.toSSet.map η)
    (X.vertexEquivSSet x) (X.vertexEquivSSet y)))
    (SSet.bijective_mapπ₀_of_kanWeak (joyal_weakEquivalences_le_kanWeak _
      (weakEquivalence_mappingSpaceMap_toSSet_map hX hC η _ _).mem))
  change mappingSpaceπ₀Comparison hX x y a = e'.symm _
  apply e'.injective
  exact (mappingSpaceπ₀Comparison_zigzag hX hC η x y h₀ h₁ a
    (e.symm (SSet.mapπ₀ (DiagSet.toSSet.map (X.mappingSpaceMap η x y)) a))
    (e.apply_symm_apply _).symm).trans (e'.apply_symm_apply _).symm

end Atoms.Diagrammatic
