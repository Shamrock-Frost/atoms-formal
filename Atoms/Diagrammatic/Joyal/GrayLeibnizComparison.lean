import Atoms.Diagrammatic.Joyal.GrayHomComparison
import Atoms.Homotopical.Simplicial.ConeExtension
import Atoms.Diagrammatic.Marked.CylinderTensor

universe u

open CategoryTheory Limits Simplicial MonoidalClosed HomotopicalAlgebra
open Atoms.Shape Atoms.Homotopical

namespace Atoms.Diagrammatic

variable {A B : SSet.{u}} (j : A ⟶ B) {C D : MarkedSSet.{u}} (c : C ⟶ D)

noncomputable def leibnizTargetComparison :
    (Functor.PullbackObjObj.ofHasPullback internalHom j
      ((MarkedPresheaf.forget (D := edgeMarking)).map c)).pt ⟶
    DiagSet.toSSet.obj (Functor.PullbackObjObj.ofHasPullback grayHomRightBifunctor
      (SSet.toDiagSet.map j) (faceNerveRight.map c)).pt :=
  (DiagSet.toSSet.map_isPullback (Functor.PullbackObjObj.ofHasPullback
    grayHomRightBifunctor (SSet.toDiagSet.map j) (faceNerveRight.map c)).isPullback).lift
    ((Functor.PullbackObjObj.ofHasPullback internalHom j
      ((MarkedPresheaf.forget (D := edgeMarking)).map c)).fst ≫
      (grayHomSimplicialComparison A).app C)
    ((Functor.PullbackObjObj.ofHasPullback internalHom j
      ((MarkedPresheaf.forget (D := edgeMarking)).map c)).snd ≫
      (grayHomSimplicialComparison B).app D)
    (by
      let q := Functor.PullbackObjObj.ofHasPullback internalHom j
        ((MarkedPresheaf.forget (D := edgeMarking)).map c)
      have hn := (grayHomSimplicialComparison A).naturality c
      have hs := pre_app_comp_grayHomSimplicialComparison_app j D
      calc
        _ = q.fst ≫ ((internalHom.obj (Opposite.op A)).map
            ((MarkedPresheaf.forget (D := edgeMarking)).map c) ≫
            (grayHomSimplicialComparison A).app D) := by
          exact (Category.assoc _ _ _).trans (congrArg (q.fst ≫ ·) hn.symm)
        _ = (q.snd ≫ (internalHom.map j.op).app
            ((MarkedPresheaf.forget (D := edgeMarking)).obj D)) ≫
            (grayHomSimplicialComparison A).app D := by
          exact (Category.assoc _ _ _).symm.trans
            (congrArg (· ≫ (grayHomSimplicialComparison A).app D) q.isPullback.w)
        _ = _ := (Category.assoc _ _ _).trans
          ((congrArg (q.snd ≫ ·) hs).trans (Category.assoc _ _ _).symm))

@[reassoc (attr := simp↓)]
theorem leibnizTargetComparison_fst :
    leibnizTargetComparison j c ≫ DiagSet.toSSet.map
      (Functor.PullbackObjObj.ofHasPullback grayHomRightBifunctor
        (SSet.toDiagSet.map j) (faceNerveRight.map c)).fst =
      (Functor.PullbackObjObj.ofHasPullback internalHom j
        ((MarkedPresheaf.forget (D := edgeMarking)).map c)).fst ≫
        (grayHomSimplicialComparison A).app C :=
  IsPullback.lift_fst _ _ _ _

@[reassoc (attr := simp↓)]
theorem leibnizTargetComparison_snd :
    leibnizTargetComparison j c ≫ DiagSet.toSSet.map
      (Functor.PullbackObjObj.ofHasPullback grayHomRightBifunctor
        (SSet.toDiagSet.map j) (faceNerveRight.map c)).snd =
      (Functor.PullbackObjObj.ofHasPullback internalHom j
        ((MarkedPresheaf.forget (D := edgeMarking)).map c)).snd ≫
        (grayHomSimplicialComparison B).app D :=
  IsPullback.lift_snd _ _ _ _

@[reassoc]
theorem pullbackObjObjπ_comp_leibnizTargetComparison :
    (Functor.PullbackObjObj.ofHasPullback internalHom j
      ((MarkedPresheaf.forget (D := edgeMarking)).map c)).π ≫
        leibnizTargetComparison j c =
      (grayHomSimplicialComparison B).app C ≫ DiagSet.toSSet.map
        (Functor.PullbackObjObj.ofHasPullback grayHomRightBifunctor
          (SSet.toDiagSet.map j) (faceNerveRight.map c)).π := by
  apply (DiagSet.toSSet.map_isPullback (Functor.PullbackObjObj.ofHasPullback
    grayHomRightBifunctor (SSet.toDiagSet.map j) (faceNerveRight.map c)).isPullback).hom_ext
  · let q := Functor.PullbackObjObj.ofHasPullback internalHom j
      ((MarkedPresheaf.forget (D := edgeMarking)).map c)
    let r := Functor.PullbackObjObj.ofHasPullback grayHomRightBifunctor
      (SSet.toDiagSet.map j) (faceNerveRight.map c)
    exact (Category.assoc _ _ _).trans
      ((congrArg (q.π ≫ ·) (leibnizTargetComparison_fst j c)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ (grayHomSimplicialComparison A).app C) q.π_fst).trans
            ((pre_app_comp_grayHomSimplicialComparison_app j C).trans
              ((congrArg (fun t ↦ (grayHomSimplicialComparison B).app C ≫
                  DiagSet.toSSet.map t) r.π_fst.symm).trans
                ((congrArg ((grayHomSimplicialComparison B).app C ≫ ·)
                  (DiagSet.toSSet.map_comp r.π r.fst)).trans (Category.assoc _ _ _).symm))))))
  · let q := Functor.PullbackObjObj.ofHasPullback internalHom j
      ((MarkedPresheaf.forget (D := edgeMarking)).map c)
    let r := Functor.PullbackObjObj.ofHasPullback grayHomRightBifunctor
      (SSet.toDiagSet.map j) (faceNerveRight.map c)
    exact (Category.assoc _ _ _).trans
      ((congrArg (q.π ≫ ·) (leibnizTargetComparison_snd j c)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ (grayHomSimplicialComparison B).app D) q.π_snd).trans
            (((grayHomSimplicialComparison B).naturality c).trans
              ((congrArg (fun t ↦ (grayHomSimplicialComparison B).app C ≫
                  DiagSet.toSSet.map t) r.π_snd.symm).trans
                ((congrArg ((grayHomSimplicialComparison B).app C ≫ ·)
                  (DiagSet.toSSet.map_comp r.π r.snd)).trans (Category.assoc _ _ _).symm))))))

open SSet.modelCategoryJoyal MarkedSSet.modelCategoryCartesian

theorem weakEquivalence_leibnizTargetComparison [Mono j] [IsFibrant C] [IsFibrant D] :
    WeakEquivalence (leibnizTargetComparison j c) := by
  have hG (E : MarkedSSet.{u}) [IsFibrant E] : IsInftyCategory 1 (faceNerveRight.obj E) :=
    (isFibrant_infty_iff 1 _).1 (isQuillen_faceNerveAdjunction.isFibrant_obj E)
  have hQ (E : MarkedSSet.{u}) [IsFibrant E] :
      SSet.Quasicategory ((MarkedPresheaf.forget (D := edgeMarking)).obj E) :=
    (isFibrant_iff_quasicategory _).1
      (Atoms.Homotopical.isQuillenEquivalence_flatForgetAdjunction.toIsQuillen.isFibrant_obj E)
  have := hQ C
  have := hQ D
  have hI (K : SSet.{u}) (E : MarkedSSet.{u}) [IsFibrant E] :
      SSet.Quasicategory ((internalHom.obj (Opposite.op K)).obj
        ((MarkedPresheaf.forget (D := edgeMarking)).obj E)) := by
    have := hQ E
    change ((ihom K).obj ((MarkedPresheaf.forget (D := edgeMarking)).obj E)).Quasicategory
    infer_instance
  have := hI A D
  have := hI B D
  have : Fibration ((internalHom.map j.op).app
      ((MarkedPresheaf.forget (D := edgeMarking)).obj D)) :=
    (SSet.modelCategoryJoyal.fibration_iff_isofibration _).2
      (SSet.isofibration_pullbackObjObjπ (terminal.from _) j
        (Functor.PullbackObjObj.ofIsTerminal _ _ _ terminalIsTerminal))
  have := fibration_toInfty_one_grayHomRestrict (SSet.toDiagSet.map j) (hG D)
  have : Fibration (DiagSet.toSSet.map
      ((grayHomRightBifunctor.map (SSet.toDiagSet.map j).op).app (faceNerveRight.obj D))) :=
    isQuillen_sSetDiagSetAdj.fibration_map
      ((DiagSet.toInfty 1).map ((grayHomRestrict (SSet.toDiagSet.map j)).app _))
  have hF (E : MarkedSSet.{u}) [IsFibrant E] :
      IsFibrant ((internalHom.obj (Opposite.op A)).obj
        ((MarkedPresheaf.forget (D := edgeMarking)).obj E)) :=
    have := hQ E
    (isFibrant_iff_quasicategory _).2
      (inferInstanceAs (((ihom A).obj
        ((MarkedPresheaf.forget (D := edgeMarking)).obj E)).Quasicategory))
  have := hF C
  have := hF D
  have hR (E : MarkedSSet.{u}) [IsFibrant E] :
      IsFibrant (DiagSet.toSSet.obj
        ((grayHomRightBifunctor.obj (Opposite.op (SSet.toDiagSet.obj A))).obj
          (faceNerveRight.obj E))) :=
    isFibrant_toSSet_obj (isInftyCategory_grayHomRight _ (hG E))
  have := hR C
  have := hR D
  let wE : (internalHom.obj (Opposite.op B)).obj
      ((MarkedPresheaf.forget (D := edgeMarking)).obj D) ⟶
      DiagSet.toSSet.obj ((grayHomRightBifunctor.obj (Opposite.op (SSet.toDiagSet.obj B))).obj
        (faceNerveRight.obj D)) := (grayHomSimplicialComparison B).app D
  let wB : (internalHom.obj (Opposite.op A)).obj
      ((MarkedPresheaf.forget (D := edgeMarking)).obj D) ⟶
      DiagSet.toSSet.obj ((grayHomRightBifunctor.obj (Opposite.op (SSet.toDiagSet.obj A))).obj
        (faceNerveRight.obj D)) := (grayHomSimplicialComparison A).app D
  let wA : (internalHom.obj (Opposite.op A)).obj
      ((MarkedPresheaf.forget (D := edgeMarking)).obj C) ⟶
      DiagSet.toSSet.obj ((grayHomRightBifunctor.obj (Opposite.op (SSet.toDiagSet.obj A))).obj
        (faceNerveRight.obj C)) := (grayHomSimplicialComparison A).app C
  have : WeakEquivalence wE := weakEquivalence_grayHomSimplicialComparison_app B D
  have : WeakEquivalence wB := weakEquivalence_grayHomSimplicialComparison_app A D
  have : WeakEquivalence wA := weakEquivalence_grayHomSimplicialComparison_app A C
  exact (Functor.PullbackObjObj.ofHasPullback internalHom j
      ((MarkedPresheaf.forget (D := edgeMarking)).map c)).isPullback.flip
    |>.weakEquivalence_map_of_fibration
      (DiagSet.toSSet.map_isPullback (Functor.PullbackObjObj.ofHasPullback
        grayHomRightBifunctor (SSet.toDiagSet.map j) (faceNerveRight.map c)).isPullback).flip
      wE wB wA (leibnizTargetComparison j c)
      (pre_app_comp_grayHomSimplicialComparison_app j D)
      ((grayHomSimplicialComparison A).naturality c)
      (leibnizTargetComparison_snd j c) (leibnizTargetComparison_fst j c)

private noncomputable def outputVertexIso :
    Arrow.mk (SSet.toDiagSet.{u}.map (SSet.stdSimplex.δ (0 : Fin 2))) ≅
      Arrow.mk (uliftYoneda.{u}.map (atomGlobeVertex true)) :=
  Arrow.isoMk (toDiagSetObjStdSimplexIso 0)
    (toDiagSetObjStdSimplexIso 1 ≪≫ uliftYoneda.mapIso atomSimplexOneIsoGlobe) (by
      have h : SSet.toDiagSet.{u}.map (SSet.stdSimplex.δ (0 : Fin 2)) ≫
          (toDiagSetObjStdSimplexIso 1).hom = (toDiagSetObjStdSimplexIso 0).hom ≫
            uliftYoneda.map (simplexHom (SimplexCategory.δ (0 : Fin 2)).toOrderHom) :=
        stdSimplexCompToDiagSetIso.hom.naturality _
      have hδ : simplexHom (SimplexCategory.δ (0 : Fin 2)).toOrderHom ≫
          atomSimplexOneIsoGlobe.hom = atomGlobeVertex true :=
        simplexHom_δ_comp_atomSimplexOneIsoGlobe_hom true
      refine Eq.trans ?_ ((h =≫ uliftYoneda.map atomSimplexOneIsoGlobe.hom).symm.trans
        (Category.assoc _ _ _))
      rw [Category.assoc, ← Functor.map_comp, hδ]
      rfl)

noncomputable def markedIntervalVertexArrowIso :
    Arrow.mk (SSet.toDiagSet.{u}.map (SSet.stdSimplex.δ (0 : Fin 2))) ≅
      Arrow.mk ((MarkedPresheaf.forget (D := atomMarking)).map
        (markedIntervalVertex.{u} true)) :=
  outputVertexIso ≪≫ Arrow.isoMk (Iso.refl _)
    (ballIsoForgetYoneda (MarkedSite.marked (atomGlobe 1) markable_atomGlobe_one))
    (by
      simp only [markedIntervalVertex, MarkedPresheaf.forget_map_homMk]
      rfl)

@[simp]
theorem markedIntervalVertexArrowIso_hom_left :
    markedIntervalVertexArrowIso.{u}.hom.left =
      (toDiagSetObjStdSimplexIso 0).hom := by
  rfl

@[simp]
theorem markedIntervalVertexArrowIso_hom_right :
    markedIntervalVertexArrowIso.{u}.hom.right =
      (toDiagSetObjStdSimplexIso 1).hom ≫ uliftYoneda.map atomSimplexOneIsoGlobe.hom ≫
      (ballIsoForgetYoneda (MarkedSite.marked (atomGlobe 1) markable_atomGlobe_one)).hom := by
  rfl

@[simp]
theorem markedIntervalVertexArrowIso_inv_left :
    markedIntervalVertexArrowIso.{u}.inv.left =
      (toDiagSetObjStdSimplexIso 0).inv := by
  rfl

@[simp]
theorem markedIntervalVertexArrowIso_inv_right :
    markedIntervalVertexArrowIso.{u}.inv.right =
      (ballIsoForgetYoneda (MarkedSite.marked (atomGlobe 1) markable_atomGlobe_one)).inv ≫
      uliftYoneda.map atomSimplexOneIsoGlobe.inv ≫ (toDiagSetObjStdSimplexIso 1).inv := by
  rfl

private noncomputable def intervalTargetIso :
    Arrow.mk (Functor.PullbackObjObj.ofHasPullback grayHomRightBifunctor
      (SSet.toDiagSet.map (SSet.stdSimplex.δ (0 : Fin 2))) (faceNerveRight.map c)).π ≅
    Arrow.mk (Functor.PullbackObjObj.ofHasPullback grayHomRightBifunctor
      ((MarkedPresheaf.forget (D := atomMarking)).map (markedIntervalVertex.{u} true))
      (faceNerveRight.map c)).π :=
  (Functor.PullbackObjObj.π_iso_of_iso_left
      (f₁ := Arrow.mk (SSet.toDiagSet.map (SSet.stdSimplex.δ (0 : Fin 2))))
      (f₁' := Arrow.mk ((MarkedPresheaf.forget (D := atomMarking)).map
        (markedIntervalVertex.{u} true))) (f₃ := Arrow.mk (faceNerveRight.map c))
      (Functor.PullbackObjObj.ofHasPullback grayHomRightBifunctor _ _)
      (Functor.PullbackObjObj.ofHasPullback grayHomRightBifunctor _ _)
      markedIntervalVertexArrowIso)

noncomputable def arrowLeibnizComparison :
    (Functor.PullbackObjObj.ofHasPullback internalHom (SSet.stdSimplex.δ (0 : Fin 2))
      ((MarkedPresheaf.forget (D := edgeMarking)).map c)).pt ⟶
    DiagSet.toSSet.obj (Functor.PullbackObjObj.ofHasPullback grayHomRightBifunctor
      ((MarkedPresheaf.forget (D := atomMarking)).map (markedIntervalVertex.{u} true))
      (faceNerveRight.map c)).pt :=
  leibnizTargetComparison (SSet.stdSimplex.δ (0 : Fin 2)) c ≫ DiagSet.toSSet.map
    (intervalTargetIso c).hom.right

@[reassoc]
theorem pullbackObjObjπ_comp_arrowLeibnizComparison :
    (Functor.PullbackObjObj.ofHasPullback internalHom (SSet.stdSimplex.δ (0 : Fin 2))
      ((MarkedPresheaf.forget (D := edgeMarking)).map c)).π ≫ arrowLeibnizComparison c =
      ((grayHomSimplicialComparison Δ[1]).app C ≫ DiagSet.toSSet.map
        ((grayHomRestrict markedIntervalVertexArrowIso.inv.right).app (faceNerveRight.obj C))) ≫
        DiagSet.toSSet.map (Functor.PullbackObjObj.ofHasPullback grayHomRightBifunctor
          ((MarkedPresheaf.forget (D := atomMarking)).map (markedIntervalVertex.{u} true))
          (faceNerveRight.map c)).π := by
  dsimp only [arrowLeibnizComparison]
  erw [← Category.assoc, pullbackObjObjπ_comp_leibnizTargetComparison, Category.assoc,
    ← Functor.map_comp, ← (intervalTargetIso c).hom.w, Functor.map_comp,
    ← Category.assoc]

@[reassoc]
theorem arrowLeibnizComparison_fst :
    arrowLeibnizComparison c ≫ DiagSet.toSSet.map
      (Functor.PullbackObjObj.ofHasPullback grayHomRightBifunctor
        ((MarkedPresheaf.forget (D := atomMarking)).map (markedIntervalVertex.{u} true))
        (faceNerveRight.map c)).fst =
      (Functor.PullbackObjObj.ofHasPullback internalHom (SSet.stdSimplex.δ (0 : Fin 2))
        ((MarkedPresheaf.forget (D := edgeMarking)).map c)).fst ≫
        (grayHomSimplicialComparison Δ[0]).app C ≫ DiagSet.toSSet.map
          ((grayHomRestrict markedIntervalVertexArrowIso.inv.left).app (faceNerveRight.obj C)) := by
  dsimp only [arrowLeibnizComparison]
  rw [Category.assoc, ← Functor.map_comp]
  simp only [intervalTargetIso, Functor.PullbackObjObj.π_iso_of_iso_left_hom,
    Functor.PullbackObjObj.mapArrowLeft_right]
  erw [IsPullback.lift_fst, Functor.map_comp, ← Category.assoc,
    leibnizTargetComparison_fst, Category.assoc]

@[reassoc]
theorem arrowLeibnizComparison_snd :
    arrowLeibnizComparison c ≫ DiagSet.toSSet.map
      (Functor.PullbackObjObj.ofHasPullback grayHomRightBifunctor
        ((MarkedPresheaf.forget (D := atomMarking)).map (markedIntervalVertex.{u} true))
        (faceNerveRight.map c)).snd =
      (Functor.PullbackObjObj.ofHasPullback internalHom (SSet.stdSimplex.δ (0 : Fin 2))
        ((MarkedPresheaf.forget (D := edgeMarking)).map c)).snd ≫
        (grayHomSimplicialComparison Δ[1]).app D ≫ DiagSet.toSSet.map
          ((grayHomRestrict markedIntervalVertexArrowIso.inv.right).app
            (faceNerveRight.obj D)) := by
  dsimp only [arrowLeibnizComparison]
  rw [Category.assoc, ← Functor.map_comp]
  simp only [intervalTargetIso, Functor.PullbackObjObj.π_iso_of_iso_left_hom,
    Functor.PullbackObjObj.mapArrowLeft_right]
  erw [IsPullback.lift_snd, Functor.map_comp, ← Category.assoc,
    leibnizTargetComparison_snd, Category.assoc]

theorem weakEquivalence_arrowLeibnizComparison [IsFibrant C] [IsFibrant D] :
    WeakEquivalence (arrowLeibnizComparison c) := by
  have := weakEquivalence_leibnizTargetComparison (SSet.stdSimplex.δ (0 : Fin 2)) c
  dsimp only [arrowLeibnizComparison]
  infer_instance

end Atoms.Diagrammatic
