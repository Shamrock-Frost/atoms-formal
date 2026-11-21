import Atoms.Diagrammatic.Fibration.SliceContraction
import Atoms.Diagrammatic.Joyal.GrayHomMarkedExponential
import Atoms.Homotopical.Simplicial.CommaObject

open CategoryTheory Limits Simplicial MonoidalCategory MonoidalClosed HomotopicalAlgebra
open CartesianMonoidalCategory
open Atoms.Shape Atoms.Homotopical

universe u

namespace Atoms.Diagrammatic

open SSet.modelCategoryJoyal MarkedSSet.modelCategoryCartesian

private theorem quasicategory_forget_obj (C : MarkedSSet.{u}) [IsFibrant C] :
    SSet.Quasicategory ((MarkedPresheaf.forget (D := edgeMarking)).obj C) :=
  (isFibrant_iff_quasicategory _).1
    (Atoms.Homotopical.isQuillenEquivalence_flatForgetAdjunction.toIsQuillen.isFibrant_obj C)

private theorem grayHomRight_map_comp_grayHomBoundaryFan {Z Z' : DiagSet.{u}} (f : Z ⟶ Z')
    (β : Bool) :
    (grayHomRight intervalBoundary.{u}).map f ≫
        cond β (grayHomBoundaryFan Z').snd (grayHomBoundaryFan Z').fst =
      cond β (grayHomBoundaryFan Z).snd (grayHomBoundaryFan Z).fst ≫ f := by
  have h (i : ball.{u} atomPoint ⟶ intervalBoundary) :
      (grayHomRight intervalBoundary.{u}).map f ≫ (grayHomRestrict i).app Z' ≫
          grayHomRightPointIso.hom.app Z' =
        ((grayHomRestrict i).app Z ≫ grayHomRightPointIso.hom.app Z) ≫ f := by
    rw [← Category.assoc, (grayHomRestrict i).naturality, Category.assoc, Category.assoc]
    exact congrArg (_ ≫ ·) (grayHomRightPointIso.hom.naturality f)
  cases β
  · exact h coprod.inl
  · exact h coprod.inr

variable (α : Bool) (S : SSet.{u}) {C : MarkedSSet.{u}}
  (d : SSet.toDiagSet.obj S ⟶ faceNerveRight.obj C)

noncomputable abbrev markedCommaObject : SSet.{u} :=
  SSet.commaObject α ((MarkedPresheaf.forget (D := edgeMarking)).map (markedConstDiagram S C))
    (markedDiagramPoint S d)

theorem quasicategory_markedCommaObject [IsFibrant C] :
    (markedCommaObject α S d).Quasicategory :=
  have : IsFibrant ((ihom (faceNerve.obj (SSet.toDiagSet.obj S))).obj C) :=
    (MarkedSSet.isQuillen_ihomAdjunction (faceNerve.obj (SSet.toDiagSet.obj S))).isFibrant_obj C
  have := quasicategory_forget_obj C
  have := quasicategory_forget_obj ((ihom (faceNerve.obj (SSet.toDiagSet.obj S))).obj C)
  inferInstance

private theorem toUnit_comp_markedDiagramPoint_comp :
    (toUnit ((MarkedPresheaf.forget (D := edgeMarking)).obj C) ≫ markedDiagramPoint S d) ≫
        faceNerveRightComparison.app _ ≫ DiagSet.toSSet.map
          ((grayHomRightFaceNerveIso (SSet.toDiagSet.obj S)).hom.app C) =
      faceNerveRightComparison.app C ≫ DiagSet.toSSet.map
        (isTerminalBallAtomPoint.from (faceNerveRight.obj C) ≫ diagramPoint d) := by
  rw [Category.assoc, markedDiagramPoint_comp_faceNerveRightComparison_app, Functor.map_comp,
    ← Category.assoc, ← Category.assoc]
  exact congrArg (· ≫ _) (isTerminalToSSetBallAtomPoint.hom_ext _ _)

private theorem commaObjectBase_comp_boundaryComparison :
    SSet.commaObjectBase α
        ((MarkedPresheaf.forget (D := edgeMarking)).map (markedConstDiagram S C))
        (markedDiagramPoint S d) ≫
      boundaryComparison ((ihom (faceNerve.obj (SSet.toDiagSet.obj S))).obj C) ≫
        DiagSet.toSSet.map ((grayHomRight intervalBoundary.{u}).map
          ((grayHomRightFaceNerveIso (SSet.toDiagSet.obj S)).hom.app C)) =
      faceNerveRightComparison.app C ≫ DiagSet.toSSet.map (coneObjectBase α d) := by
  let E := (ihom (faceNerve.obj (SSet.toDiagSet.obj S))).obj C
  let Y := (grayHomRight (SSet.toDiagSet.obj S)).obj (faceNerveRight.obj C)
  let φ : faceNerveRight.obj E ⟶ Y := (grayHomRightFaceNerveIso (SSet.toDiagSet.obj S)).hom.app C
  have hc := markedConstDiagram_comp_faceNerveRightComparison_app S C
  have hp := toUnit_comp_markedDiagramPoint_comp S d
  have ends (β : Bool) :
      (SSet.commaObjectBase α
          ((MarkedPresheaf.forget (D := edgeMarking)).map (markedConstDiagram S C))
          (markedDiagramPoint S d) ≫ boundaryComparison E ≫
            DiagSet.toSSet.map ((grayHomRight intervalBoundary.{u}).map φ)) ≫
          DiagSet.toSSet.map (cond β (grayHomBoundaryFan Y).snd (grayHomBoundaryFan Y).fst) =
        (faceNerveRightComparison.app C ≫ DiagSet.toSSet.map (coneObjectBase α d)) ≫
          DiagSet.toSSet.map (cond β (grayHomBoundaryFan Y).snd (grayHomBoundaryFan Y).fst) := by
    have h₁ : boundaryComparison E ≫
          DiagSet.toSSet.map ((grayHomRight intervalBoundary.{u}).map φ) ≫
            DiagSet.toSSet.map (cond β (grayHomBoundaryFan Y).snd (grayHomBoundaryFan Y).fst) =
        SSet.evalVertex (SSet.yonedaEquiv (SSet.boundary.ι (cond β 0 1) :
            Δ[0] ⟶ (∂Δ[1] : SSet.{u}))) _ ≫
          faceNerveRightComparison.app E ≫ DiagSet.toSSet.map φ :=
      (congrArg (boundaryComparison E ≫ ·) ((DiagSet.toSSet.map_comp _ _).symm.trans
        ((congrArg DiagSet.toSSet.map (grayHomRight_map_comp_grayHomBoundaryFan φ β)).trans
          (DiagSet.toSSet.map_comp _ _)))).trans ((Category.assoc _ _ _).symm.trans
            ((congrArg (· ≫ DiagSet.toSSet.map φ) (boundaryComparison_comp_end E β)).trans
              (Category.assoc _ _ _)))
    refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
      ((Category.assoc _ _ _).trans h₁)).trans ((Category.assoc _ _ _).symm.trans ?_))
    cases β
    · refine (congrArg (· ≫ _) (SSet.commaObjectBase_comp_evalVertex_one α _ _)).trans
        (Eq.trans ?_ ((congrArg (_ ≫ ·) ((congrArg DiagSet.toSSet.map
          (coneObjectBase_comp_grayHomBoundaryFan_fst α d)).symm.trans
            (DiagSet.toSSet.map_comp _ _))).trans (Category.assoc _ _ _).symm))
      cases α
      · exact hp
      · exact hc
    · refine (congrArg (· ≫ _) (SSet.commaObjectBase_comp_evalVertex_zero α _ _)).trans
        (Eq.trans ?_ ((congrArg (_ ≫ ·) ((congrArg DiagSet.toSSet.map
          (coneObjectBase_comp_grayHomBoundaryFan_snd α d)).symm.trans
            (DiagSet.toSSet.map_comp _ _))).trans (Category.assoc _ _ _).symm))
      cases α
      · exact hc
      · exact hp
  exact BinaryFan.IsLimit.hom_ext ((isLimitMapConeBinaryFanEquiv DiagSet.toSSet _ _)
    (isLimitOfPreserves DiagSet.toSSet (isLimitGrayHomBoundaryFan Y))) (ends false) (ends true)

private theorem pre_app_comp_boundaryComparison_comp :
    (pre (∂Δ[1] : (Δ[1] : SSet.{u}).Subcomplex).ι).app _ ≫
        boundaryComparison ((ihom (faceNerve.obj (SSet.toDiagSet.obj S))).obj C) ≫
          DiagSet.toSSet.map ((grayHomRight intervalBoundary.{u}).map
            ((grayHomRightFaceNerveIso (SSet.toDiagSet.obj S)).hom.app C)) =
      (intervalComparison ((ihom (faceNerve.obj (SSet.toDiagSet.obj S))).obj C) ≫
        DiagSet.toSSet.map ((grayHomRight (ball.{u} (atomSimplex 1))).map
          ((grayHomRightFaceNerveIso (SSet.toDiagSet.obj S)).hom.app C))) ≫
        DiagSet.toSSet.map ((grayHomRestrict intervalBoundaryι).app
          ((grayHomRight (SSet.toDiagSet.obj S)).obj (faceNerveRight.obj C))) :=
  (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (pre_app_comp_boundaryComparison _)).trans
    ((Category.assoc _ _ _).trans ((congrArg (intervalComparison _ ≫ ·)
      ((DiagSet.toSSet.map_comp _ _).symm.trans ((congrArg DiagSet.toSSet.map
        ((grayHomRestrict intervalBoundaryι).naturality _).symm).trans
          (DiagSet.toSSet.map_comp _ _)))).trans (Category.assoc _ _ _).symm)))

noncomputable def markedCommaToConeObject :
    markedCommaObject α S d ⟶ DiagSet.toSSet.obj (coneObject α d) :=
  (DiagSet.toSSet.map_isPullback (isPullback_coneObject α d)).lift
    (SSet.commaObjectArrow α _ _ ≫ intervalComparison _ ≫ DiagSet.toSSet.map
      ((grayHomRight (ball.{u} (atomSimplex 1))).map
        ((grayHomRightFaceNerveIso (SSet.toDiagSet.obj S)).hom.app C)))
    (SSet.commaObjectπ α _ _ ≫ faceNerveRightComparison.app C)
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
      (pre_app_comp_boundaryComparison_comp S).symm).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _) (SSet.isPullback_commaObject α _ _).w).trans
          ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
            (commaObjectBase_comp_boundaryComparison α S d)).trans
              (Category.assoc _ _ _).symm))))))

theorem markedCommaToConeObject_π :
    markedCommaToConeObject α S d ≫ DiagSet.toSSet.map (coneObjectπ α d) =
      SSet.commaObjectπ α _ _ ≫ faceNerveRightComparison.app C :=
  IsPullback.lift_snd _ _ _ _

theorem weakEquivalence_markedCommaToConeObject [IsFibrant C] :
    WeakEquivalence (markedCommaToConeObject α S d) := by
  let E := (ihom (faceNerve.obj (SSet.toDiagSet.obj S))).obj C
  have hG := isInftyCategory_faceNerveRight_obj C
  have hY := isInftyCategory_grayHomRight (SSet.toDiagSet.obj S) hG
  have : IsFibrant E :=
    (MarkedSSet.isQuillen_ihomAdjunction (faceNerve.obj (SSet.toDiagSet.obj S))).isFibrant_obj C
  have := quasicategory_forget_obj C
  have := quasicategory_forget_obj E
  have : Fibration ((pre (∂Δ[1] : (Δ[1] : SSet.{u}).Subcomplex).ι).app
      ((MarkedPresheaf.forget (D := edgeMarking)).obj E)) :=
    (SSet.modelCategoryJoyal.fibration_iff_isofibration _).2 (SSet.isofibration_pre_boundaryOne _)
  have : IsFibrant ((ihom (∂Δ[1] : SSet.{u})).obj
      ((MarkedPresheaf.forget (D := edgeMarking)).obj E)) :=
    (isFibrant_iff_quasicategory _).2 inferInstance
  obtain ⟨_, _⟩ := fibration_toSSet_map_grayHomRestrict_and_isFibrant hY
  have := weakEquivalence_grayHomSimplicialComparison_app Δ[1] E
  have := weakEquivalence_grayHomSimplicialComparison_app (∂Δ[1] : SSet.{u}) E
  have : WeakEquivalence (intervalComparison E) := by
    dsimp only [intervalComparison]
    infer_instance
  have : WeakEquivalence (boundaryComparison E) := by
    dsimp only [boundaryComparison]
    infer_instance
  have := (isFibrant_iff_quasicategory _).2
    (inferInstance : SSet.Quasicategory ((MarkedPresheaf.forget (D := edgeMarking)).obj C))
  have := isFibrant_toSSet_obj hG
  have := weakEquivalence_faceNerveRightComparison_app C
  exact (SSet.isPullback_commaObject α _ _).weakEquivalence_map_of_fibration
    (DiagSet.toSSet.map_isPullback (isPullback_coneObject α d))
    (intervalComparison E ≫ DiagSet.toSSet.map ((grayHomRight (ball.{u} (atomSimplex 1))).map
      ((grayHomRightFaceNerveIso (SSet.toDiagSet.obj S)).hom.app C)))
    (boundaryComparison E ≫ DiagSet.toSSet.map ((grayHomRight intervalBoundary.{u}).map
      ((grayHomRightFaceNerveIso (SSet.toDiagSet.obj S)).hom.app C)))
    (faceNerveRightComparison.app C) (markedCommaToConeObject α S d)
    (pre_app_comp_boundaryComparison_comp S) (commaObjectBase_comp_boundaryComparison α S d)
    (IsPullback.lift_fst _ _ _ _) (IsPullback.lift_snd _ _ _ _)

noncomputable def markedCommaToCommaObject :
    markedCommaObject α S d ⟶
      SSet.commaObject α (SSet.constDiagram S (DiagSet.toSSet.obj (faceNerveRight.obj C)))
        (SSet.diagramPoint (sSetDiagSetAdj.unit.app S ≫ DiagSet.toSSet.map d)) :=
  SSet.commaObjectMap α (faceNerveRightComparison.app C) ((markedExponentialComparison S).app C)
    (markedConstDiagram_comp_markedExponentialComparison_app S C)
    (markedDiagramPoint_comp_markedExponentialComparison_app S d)

theorem markedCommaToCommaObject_π :
    markedCommaToCommaObject α S d ≫ SSet.commaObjectπ α _ _ =
      SSet.commaObjectπ α _ _ ≫ faceNerveRightComparison.app C :=
  SSet.commaObjectMap_π _ _ _ _ _

theorem weakEquivalence_markedCommaToCommaObject [IsFibrant C] :
    WeakEquivalence (markedCommaToCommaObject α S d) := by
  let E := (ihom (faceNerve.obj (SSet.toDiagSet.obj S))).obj C
  have hG := isInftyCategory_faceNerveRight_obj C
  have : IsFibrant E :=
    (MarkedSSet.isQuillen_ihomAdjunction (faceNerve.obj (SSet.toDiagSet.obj S))).isFibrant_obj C
  have := quasicategory_forget_obj C
  have := quasicategory_forget_obj E
  have : SSet.Quasicategory (DiagSet.toSSet.obj (faceNerveRight.obj C)) :=
    (isFibrant_iff_quasicategory _).1 (isFibrant_toSSet_obj hG)
  have := weakEquivalence_faceNerveRightComparison_app C
  have := weakEquivalence_markedExponentialComparison_app S C
  exact SSet.modelCategoryJoyal.weakEquivalence_commaObjectMap α _ _ _ _

section Legs

variable {α S d}

noncomputable def grayHomPointOfMap {K : SSet.{u}} {Y : DiagSet.{u}}
    (e : K ⟶ DiagSet.toSSet.obj Y) :
    Δ[0] ⟶ DiagSet.toSSet.obj ((grayHomRight (SSet.toDiagSet.obj K)).obj Y) :=
  sSetDiagSetAdj.homEquiv _ _ ((grayTensorRightAdjunction (SSet.toDiagSet.obj K)).homEquiv _ _
    (grayTensorSnd (SSet.toDiagSet.obj Δ[0]) (SSet.toDiagSet.obj K) ≫
      (sSetDiagSetAdj.homEquiv _ _).symm e))

theorem grayHomPointOfMap_comp {K : SSet.{u}} {Y Y' : DiagSet.{u}}
    (e : K ⟶ DiagSet.toSSet.obj Y) (f : Y ⟶ Y') :
    grayHomPointOfMap e ≫ DiagSet.toSSet.map ((grayHomRight (SSet.toDiagSet.obj K)).map f) =
      grayHomPointOfMap (e ≫ DiagSet.toSSet.map f) := by
  rw [grayHomPointOfMap, grayHomPointOfMap, ← Adjunction.homEquiv_naturality_right,
    ← Adjunction.homEquiv_naturality_right, Category.assoc,
    Adjunction.homEquiv_naturality_right_symm]

noncomputable def coneObjectLeg (α : Bool) {X : DiagSet.{u}} (d : SSet.toDiagSet.obj S ⟶ X)
    (s : S _⦋0⦌) :
    coneObject α d ⟶ (grayHomRight (ball.{u} (atomSimplex 1))).obj X :=
  coneObjectι α d ≫ (grayHomRight (ball.{u} (atomSimplex 1))).map (grayHomEvalVertex s X)

theorem coneObjectMap_coneObjectLeg {X Y : DiagSet.{u}} (d : SSet.toDiagSet.obj S ⟶ X)
    (F : X ⟶ Y) (s : S _⦋0⦌) :
    coneObjectMap α d F ≫ coneObjectLeg α (d ≫ F) s =
      coneObjectLeg α d s ≫ (grayHomRight (ball.{u} (atomSimplex 1))).map F := by
  have h : (grayHomRight (SSet.toDiagSet.obj S)).map F ≫ grayHomEvalVertex s Y =
      grayHomEvalVertex s X ≫ F := by
    rw [grayHomEvalVertex, grayHomEvalVertex, (grayHomRestrict _).naturality_assoc,
      Category.assoc]
    exact congrArg (_ ≫ ·) (grayHomRightPointIso.hom.naturality F)
  rw [coneObjectLeg, coneObjectMap_ι_assoc, coneObjectLeg, Category.assoc, ← Functor.map_comp,
    ← Functor.map_comp, h, Functor.map_comp]

theorem markedCommaToConeObject_coneObjectLeg (v : Δ[0] ⟶ markedCommaObject α S d)
    (s : S _⦋0⦌) :
    v ≫ markedCommaToConeObject α S d ≫ DiagSet.toSSet.map (coneObjectLeg α d s) =
      grayHomPointOfMap (SSet.ihomPointEquiv Δ[1] _ (v ≫ markedCommaToCommaObject α S d ≫
          SSet.commaObjectArrow α _ _) ≫ SSet.evalVertex s _) ≫
        DiagSet.toSSet.map ((grayHomRestrict (toDiagSetObjStdSimplexIso 1).inv).app _) := by
  let E := (ihom (faceNerve.obj (SSet.toDiagSet.obj S))).obj C
  let f := (grayHomRightFaceNerveIso (SSet.toDiagSet.obj S)).hom.app C ≫
    grayHomEvalVertex s (faceNerveRight.obj C)
  have h₁ : markedCommaToConeObject α S d ≫ DiagSet.toSSet.map (coneObjectLeg α d s) =
      SSet.commaObjectArrow α _ _ ≫ (grayHomSimplicialComparison Δ[1]).app E ≫
        DiagSet.toSSet.map ((grayHomRight (SSet.toDiagSet.obj Δ[1])).map f) ≫
          DiagSet.toSSet.map ((grayHomRestrict (toDiagSetObjStdSimplexIso 1).inv).app _) := by
    rw [coneObjectLeg, Functor.map_comp, ← Category.assoc, markedCommaToConeObject,
      IsPullback.lift_fst, Category.assoc, intervalComparison, Category.assoc, Category.assoc,
      ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
      ← (grayHomRestrict _).naturality]
  have h₂ : v ≫ SSet.commaObjectArrow α _ _ ≫ (grayHomSimplicialComparison Δ[1]).app E =
      grayHomPointOfMap (SSet.ihomPointEquiv Δ[1] _ (v ≫ SSet.commaObjectArrow α _ _) ≫
        faceNerveRightComparison.app E) :=
    (Category.assoc _ _ _).symm.trans
      (grayHomSimplicialComparison_app_point Δ[1] E (v ≫ SSet.commaObjectArrow α _ _)).symm
  rw [h₁, reassoc_of% h₂, ← Category.assoc, grayHomPointOfMap_comp, Category.assoc,
    faceNerveRightComparison_app_comp_grayHomEvalVertex, markedCommaToCommaObject,
    SSet.commaObjectMap_arrow, ← Category.assoc v, SSet.ihomPointEquiv_comp_ihom_map,
    Category.assoc]

end Legs

end Atoms.Diagrammatic
