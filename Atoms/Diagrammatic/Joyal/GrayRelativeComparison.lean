import Atoms.Homotopical.Simplicial.RelativeFibre
import Atoms.Diagrammatic.MappingSpaceComparison
import Atoms.Diagrammatic.Joyal.GraySegalComparison
import Atoms.Diagrammatic.Joyal.GrayCompositionNaturality
import Atoms.Diagrammatic.Limits.FiniteProduct
import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.SimplexFibre
import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Product
import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Over
import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.MapOver

open CategoryTheory Limits Simplicial MonoidalCategory MonoidalClosed HomotopicalAlgebra
open Atoms.Homotopical Atoms.Shape SSet

universe u

namespace Atoms.Diagrammatic

@[reassoc]
theorem grayHomSimplicialComparison_app_comp_evalVertex (C : MarkedSSet.{u})
    {S : SSet.{u}} (a : S _⦋0⦌) :
    (grayHomSimplicialComparison S).app C ≫
        DiagSet.toSSet.map (grayHomEvalVertex a (faceNerveRight.obj C)) =
      SSet.evalVertex a ((MarkedPresheaf.forget (D := edgeMarking)).obj C) ≫
        faceNerveRightComparison.app C := by
  let Q : SSet.{u} := (MarkedPresheaf.forget (D := edgeMarking)).obj C
  have hc : constDiagram (SSet.toDiagSet.obj Δ[0]) (faceNerveRight.obj C) ≫
      ((grayHomRestrict pointIsoToDiagSetStdSimplex.{u}.hom).app _ ≫
        grayHomRightPointIso.hom.app _) = 𝟙 _ := by
    rw [← Category.assoc, constDiagram_comp_grayHomRestrict,
      constDiagram_comp_grayHomRightPointIso_hom_app]
  have hb : (grayHomSimplicialComparison Δ[0]).app C ≫
      DiagSet.toSSet.map ((grayHomRestrict pointIsoToDiagSetStdSimplex.{u}.hom).app _ ≫
        grayHomRightPointIso.hom.app _) =
      SSet.evalVertex (SSet.yonedaEquiv (𝟙 Δ[0])) Q ≫
        faceNerveRightComparison.app C := by
    apply (cancel_epi (SSet.constDiagram Δ[0] Q)).1
    rw [← Category.assoc, constDiagram_comp_grayHomSimplicialComparison_app]
    rw [Category.assoc, ← Functor.map_comp, hc, CategoryTheory.Functor.map_id]
    simp only [← Category.assoc, SSet.constDiagram_comp_evalVertex,
      Category.id_comp]
    exact Category.comp_id _
  rw [grayHomEvalVertex, grayHomRestrict_comp, NatTrans.comp_app, Category.assoc,
    Functor.map_comp, ← pre_app_comp_grayHomSimplicialComparison_app_assoc, hb,
    ← Category.assoc, SSet.pre_app_comp_evalVertex]
  congr 2
  exact (SSet.yonedaEquiv_comp (𝟙 Δ[0]) (SSet.yonedaEquiv.symm a)).symm.trans
    (by rw [Category.id_comp, Equiv.apply_symm_apply])

noncomputable def grayHomRelativeComparison {T S : SSet.{u}} (i : T ⟶ S)
    (C : MarkedSSet.{u})
    (b : Δ[0] ⟶ (ihom T).obj ((MarkedPresheaf.forget (D := edgeMarking)).obj C)) :
    pullback ((pre i).app ((MarkedPresheaf.forget (D := edgeMarking)).obj C)) b ⟶
      pullback (DiagSet.toSSet.map ((grayHomRestrict (SSet.toDiagSet.map i)).app
        (faceNerveRight.obj C))) (b ≫ (grayHomSimplicialComparison T).app C) :=
  pullback.map _ _ _ _ ((grayHomSimplicialComparison S).app C) (𝟙 _)
    ((grayHomSimplicialComparison T).app C)
    (pre_app_comp_grayHomSimplicialComparison_app i C)
    (Category.id_comp _).symm

@[reassoc]
theorem grayHomRelativeComparison_fst {T S : SSet.{u}} (i : T ⟶ S)
    (C : MarkedSSet.{u})
    (b : Δ[0] ⟶ (ihom T).obj ((MarkedPresheaf.forget (D := edgeMarking)).obj C)) :
    grayHomRelativeComparison i C b ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ (grayHomSimplicialComparison S).app C :=
  pullback.lift_fst _ _ _

noncomputable def grayRelativeRestrict {T S T' S' : SSet.{u}}
    (i : T ⟶ S) (j : T' ⟶ S') (t : T' ⟶ T) (s : S' ⟶ S)
    (h : j ≫ s = t ≫ i) (C : MarkedSSet.{u})
    (b : Δ[0] ⟶ (ihom T).obj ((MarkedPresheaf.forget (D := edgeMarking)).obj C)) :
    pullback (DiagSet.toSSet.map ((grayHomRestrict (SSet.toDiagSet.map i)).app
      (faceNerveRight.obj C))) (b ≫ (grayHomSimplicialComparison T).app C) ⟶
    pullback (DiagSet.toSSet.map ((grayHomRestrict (SSet.toDiagSet.map j)).app
      (faceNerveRight.obj C)))
      ((b ≫ (pre t).app _) ≫ (grayHomSimplicialComparison T').app C) :=
  pullback.map _ _ _ _
    (DiagSet.toSSet.map ((grayHomRestrict (SSet.toDiagSet.map s)).app (faceNerveRight.obj C)))
    (𝟙 _) (DiagSet.toSSet.map
      ((grayHomRestrict (SSet.toDiagSet.map t)).app (faceNerveRight.obj C)))
    (by
      rw [← Functor.map_comp, ← Functor.map_comp, ← NatTrans.comp_app,
        ← grayHomRestrict_comp, ← NatTrans.comp_app, ← grayHomRestrict_comp,
        ← Functor.map_comp, ← Functor.map_comp, h])
    (by
      simpa only [Category.id_comp, Category.assoc, Functor.comp_map] using
        congrArg (b ≫ ·) (pre_app_comp_grayHomSimplicialComparison_app t C).symm)

theorem grayHomRelativeComparison_restrict {T S T' S' : SSet.{u}}
    (i : T ⟶ S) (j : T' ⟶ S') (t : T' ⟶ T) (s : S' ⟶ S)
    (h : j ≫ s = t ≫ i) (C : MarkedSSet.{u})
    (b : Δ[0] ⟶ (ihom T).obj ((MarkedPresheaf.forget (D := edgeMarking)).obj C)) :
    simplicialRelativeRestrict i j t s h _ b ≫
        grayHomRelativeComparison j C (b ≫ (pre t).app _) =
      grayHomRelativeComparison i C b ≫ grayRelativeRestrict i j t s h C b := by
  apply pullback.hom_ext
  · simp only [grayHomRelativeComparison, simplicialRelativeRestrict,
      grayRelativeRestrict, Category.assoc, pullback.map, pullback.lift_fst,
      pullback.lift_fst_assoc]
    simpa only [Category.assoc, Functor.comp_map] using congrArg
      (pullback.fst ((pre i).app _) b ≫ ·)
      (pre_app_comp_grayHomSimplicialComparison_app s C)
  · simp only [grayHomRelativeComparison, simplicialRelativeRestrict,
      grayRelativeRestrict, Category.assoc, pullback.map, pullback.lift_snd,
      Category.comp_id]

noncomputable def grayRelativeTargetMap {T S : SSet.{u}} (i : T ⟶ S)
    {C D : MarkedSSet.{u}} (f : C ⟶ D)
    (b : Δ[0] ⟶ (ihom T).obj ((MarkedPresheaf.forget (D := edgeMarking)).obj C)) :
    pullback (DiagSet.toSSet.map ((grayHomRestrict (SSet.toDiagSet.map i)).app
      (faceNerveRight.obj C))) (b ≫ (grayHomSimplicialComparison T).app C) ⟶
    pullback (DiagSet.toSSet.map ((grayHomRestrict (SSet.toDiagSet.map i)).app
      (faceNerveRight.obj D)))
      ((b ≫ (ihom T).map ((MarkedPresheaf.forget (D := edgeMarking)).map f)) ≫
        (grayHomSimplicialComparison T).app D) :=
  pullback.map _ _ _ _
    (DiagSet.toSSet.map ((grayHomRight (SSet.toDiagSet.obj S)).map (faceNerveRight.map f)))
    (𝟙 _)
    (DiagSet.toSSet.map ((grayHomRight (SSet.toDiagSet.obj T)).map (faceNerveRight.map f)))
    (by
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg DiagSet.toSSet.map ((grayHomRestrict (SSet.toDiagSet.map i)).naturality
        (faceNerveRight.map f)).symm)
    (by
      simpa only [Category.id_comp, Category.assoc, Functor.comp_map] using
        congrArg (b ≫ ·) ((grayHomSimplicialComparison T).naturality f).symm)

theorem grayHomRelativeComparison_target {T S : SSet.{u}} (i : T ⟶ S)
    {C D : MarkedSSet.{u}} (f : C ⟶ D)
    (b : Δ[0] ⟶ (ihom T).obj ((MarkedPresheaf.forget (D := edgeMarking)).obj C)) :
    simplicialRelativeTargetMap i ((MarkedPresheaf.forget (D := edgeMarking)).map f) b ≫
        grayHomRelativeComparison i D
          (b ≫ (ihom T).map ((MarkedPresheaf.forget (D := edgeMarking)).map f)) =
      grayHomRelativeComparison i C b ≫ grayRelativeTargetMap i f b := by
  apply pullback.hom_ext
  · simp only [simplicialRelativeTargetMap, grayRelativeTargetMap,
      grayHomRelativeComparison, Category.assoc, pullback.map, pullback.lift_fst,
      pullback.lift_fst_assoc]
    simpa only [Category.assoc, Functor.comp_map] using congrArg
      (pullback.fst ((pre i).app _) b ≫ ·) ((grayHomSimplicialComparison S).naturality f)
  · simp only [simplicialRelativeTargetMap, grayRelativeTargetMap,
      grayHomRelativeComparison, Category.assoc, pullback.map, pullback.lift_snd,
      Category.comp_id]

open MarkedSSet.modelCategoryCartesian SSet.modelCategoryJoyal

theorem weakEquivalence_grayHomRelativeComparison {T S : SSet.{u}} (i : T ⟶ S)
    [Mono i] (C : MarkedSSet.{u}) [IsFibrant C]
    (b : Δ[0] ⟶ (ihom T).obj ((MarkedPresheaf.forget (D := edgeMarking)).obj C)) :
    WeakEquivalence (grayHomRelativeComparison i C b) := by
  let Q : SSet.{u} := (MarkedPresheaf.forget (D := edgeMarking)).obj C
  have hG : IsFibrant ((DiagSet.toInfty 1).obj (faceNerveRight.obj C)) :=
    isQuillen_faceNerveAdjunction.isFibrant_obj C
  have hGC : IsInftyCategory 1 (faceNerveRight.obj C) :=
    (isFibrant_infty_iff 1 _).1 hG
  have : IsFibrant Q :=
    Atoms.Homotopical.isQuillenEquivalence_flatForgetAdjunction.toIsQuillen.isFibrant_obj C
  have : Q.Quasicategory := (isFibrant_iff_quasicategory _).1 inferInstance
  have : IsFibrant ((ihom T).obj Q) := (isQuillen_ihomAdjunction T).isFibrant_obj Q
  have : IsFibrant ((ihom S).obj Q) := (isQuillen_ihomAdjunction S).isFibrant_obj Q
  have : ((ihom S).obj Q).Quasicategory := (isFibrant_iff_quasicategory _).1 inferInstance
  have : ((ihom T).obj Q).Quasicategory := (isFibrant_iff_quasicategory _).1 inferInstance
  have : IsFibrant (Δ[0] : SSet.{u}) :=
    (isFibrant_iff_of_isTerminal (𝟙 _) SSet.stdSimplex.isTerminalObj₀).2 inferInstance
  have : Fibration ((pre i).app Q) :=
    (SSet.modelCategoryJoyal.fibration_iff_isofibration _).2
      (SSet.isofibration_pullbackObjObjπ (terminal.from Q) i
      (Functor.PullbackObjObj.ofIsTerminal _ _ _ terminalIsTerminal))
  have := fibration_toInfty_one_grayHomRestrict (SSet.toDiagSet.map i) hGC
  have : Fibration (DiagSet.toSSet.map
      ((grayHomRestrict (SSet.toDiagSet.map i)).app (faceNerveRight.obj C))) :=
    isQuillen_sSetDiagSetAdj.fibration_map
      ((DiagSet.toInfty 1).map ((grayHomRestrict (SSet.toDiagSet.map i)).app
        (faceNerveRight.obj C)))
  have : IsFibrant ((DiagSet.toInfty 1).obj
      ((grayHomRight (SSet.toDiagSet.obj T)).obj (faceNerveRight.obj C))) :=
    (isFibrant_infty_iff 1 _).2 (isInftyCategory_grayHomRight _ hGC)
  have : IsFibrant ((faceNerveRight ⋙ grayHomRight (SSet.toDiagSet.obj T) ⋙
      DiagSet.toSSet).obj C) :=
    isQuillen_sSetDiagSetAdj.isFibrant_obj
      ((DiagSet.toInfty 1).obj ((grayHomRight (SSet.toDiagSet.obj T)).obj (faceNerveRight.obj C)))
  have := weakEquivalence_grayHomSimplicialComparison_app T C
  have := weakEquivalence_grayHomSimplicialComparison_app S C
  exact (IsPullback.of_hasPullback ((pre i).app Q) b).weakEquivalence_map_of_fibration
    (IsPullback.of_hasPullback _ _)
    ((grayHomSimplicialComparison S).app C) ((grayHomSimplicialComparison T).app C) (𝟙 _)
    (grayHomRelativeComparison i C b)
    (pre_app_comp_grayHomSimplicialComparison_app i C)
    (Category.id_comp _).symm
    (grayHomRelativeComparison_fst i C b)
    (by rw [Category.comp_id]; exact (pullback.lift_snd _ _ _).trans (Category.comp_id _))

noncomputable def grayHomVerticesIso (p : ℕ) (X : DiagSet.{u}) :
    (grayHomRight (graySimplexVertices p)).obj X ≅ ∏ᶜ fun _ : Fin (p + 1) => X :=
  (isLimitFanGrayHomRestrict (fun _ : Fin (p + 1) => ball.{u} atomPoint) X).conePointUniqueUpToIso
    (limit.isLimit _) ≪≫ Pi.mapIso (fun _ => grayHomRightPointIso.app X)

@[reassoc]
theorem grayHomVerticesIso_hom_π (p : ℕ) (X : DiagSet.{u}) (k : Fin (p + 1)) :
    (grayHomVerticesIso p X).hom ≫ Pi.π _ k =
      (grayHomRestrict (Sigma.ι (fun _ : Fin (p + 1) => ball.{u} atomPoint) k)).app X ≫
        grayHomRightPointIso.hom.app X := by
  rw [grayHomVerticesIso, Iso.trans_hom, Category.assoc, Pi.mapIso_hom_π,
    ← Category.assoc]
  exact congrArg (· ≫ grayHomRightPointIso.hom.app X)
    (IsLimit.conePointUniqueUpToIso_hom_comp
      (isLimitFanGrayHomRestrict (fun _ : Fin (p + 1) => ball.{u} atomPoint) X)
      (limit.isLimit _) (Discrete.mk k))

noncomputable def toSSetGrayHomVerticesIso (p : ℕ) (X : DiagSet.{u}) :
    DiagSet.toSSet.obj ((grayHomRight (graySimplexVertices p)).obj X) ≅
      ∏ᶜ fun _ : Fin (p + 1) => DiagSet.toSSet.obj X :=
  have : PreservesLimitsOfShape (Discrete (Fin (p + 1))) DiagSet.toSSet.{u} :=
    sSetDiagSetAdj.rightAdjoint_preservesLimits.preservesLimitsOfShape
  DiagSet.toSSet.mapIso (grayHomVerticesIso p X) ≪≫ PreservesProduct.iso _ _

@[reassoc]
theorem toSSetGrayHomVerticesIso_hom_π (p : ℕ) (X : DiagSet.{u}) (k : Fin (p + 1)) :
    (toSSetGrayHomVerticesIso p X).hom ≫ Pi.π _ k =
      DiagSet.toSSet.map
        ((grayHomRestrict (Sigma.ι (fun _ : Fin (p + 1) => ball.{u} atomPoint) k)).app X ≫
          grayHomRightPointIso.hom.app X) := by
  rw [toSSetGrayHomVerticesIso, Iso.trans_hom, Category.assoc, PreservesProduct.iso_hom,
    piComparison_comp_π]
  dsimp only [Functor.mapIso_hom]
  rw [← Functor.map_comp, grayHomVerticesIso_hom_π]

noncomputable def grayShapeVerticesι {S : SSet.{u}} {p : ℕ}
    (v : Fin (p + 1) → S _⦋0⦌) : graySimplexVertices.{u} p ⟶ SSet.toDiagSet.obj S :=
  Sigma.desc fun k => pointIsoToDiagSetStdSimplex.hom ≫
    SSet.toDiagSet.map (SSet.yonedaEquiv.symm (v k))

@[reassoc]
theorem grayShapeVerticesι_restrict_π {S : SSet.{u}} {p : ℕ}
    (v : Fin (p + 1) → S _⦋0⦌) (X : DiagSet.{u}) (k : Fin (p + 1)) :
    DiagSet.toSSet.map ((grayHomRestrict (grayShapeVerticesι v)).app X) ≫
        (toSSetGrayHomVerticesIso p X).hom ≫ Pi.π _ k =
      DiagSet.toSSet.map (grayHomEvalVertex (v k) X) := by
  rw [toSSetGrayHomVerticesIso_hom_π, ← Functor.map_comp, ← Category.assoc,
    ← NatTrans.comp_app, ← grayHomRestrict_comp, grayShapeVerticesι, Sigma.ι_desc]
  rfl

theorem grayShapeVerticesι_comparison_square {S : SSet.{u}} {p : ℕ}
    (v : Fin (p + 1) → S _⦋0⦌) (C : MarkedSSet.{u}) :
    (grayHomSimplicialComparison S).app C ≫
        DiagSet.toSSet.map ((grayHomRestrict (grayShapeVerticesι v)).app (faceNerveRight.obj C)) ≫
          (toSSetGrayHomVerticesIso p (faceNerveRight.obj C)).hom =
      SSet.ihomEvalVertices v ((MarkedPresheaf.forget (D := edgeMarking)).obj C) ≫
        Limits.Pi.map (fun _ : Fin (p + 1) => faceNerveRightComparison.app C) := by
  apply Pi.hom_ext
  intro k
  rw [Category.assoc, Category.assoc, grayShapeVerticesι_restrict_π,
    grayHomSimplicialComparison_app_comp_evalVertex]
  exact ((SSet.ihomEvalVertices_π_assoc v _ k _).symm.trans
    ((congrArg (SSet.ihomEvalVertices v _ ≫ ·)
      (Limits.Pi.map_π (fun _ : Fin (p + 1) => faceNerveRightComparison.app C) k)).symm)).trans
        (Category.assoc _ _ _).symm

@[reassoc]
theorem diagramPoint_comp_toSSetGrayHomVerticesIso (X : DiagSet.{u}) {p : ℕ}
    (x : Fin (p + 1) → X.Vertex) :
    toSSetPoint ≫ DiagSet.toSSet.map (diagramPoint ((graySimplexVerticesHomEquiv p X).symm x)) ≫
        (toSSetGrayHomVerticesIso p X).hom =
      Pi.lift (fun k => SSet.yonedaEquiv.symm (X.vertexEquivSSet (x k))) := by
  apply Pi.hom_ext
  intro k
  rw [Category.assoc, Category.assoc, toSSetGrayHomVerticesIso_hom_π,
    ← Functor.map_comp, ← Category.assoc,
    diagramPoint_comp_grayHomRestrict, ι_graySimplexVerticesHomEquiv_symm,
    diagramPoint_comp_grayHomRightPointIso_hom_app]
  have hT : DiagSet.toSSet.map (isTerminalBallAtomPoint.from (ball.{u} atomPoint)) = 𝟙 _ :=
    congrArg DiagSet.toSSet.map (isTerminalBallAtomPoint.hom_ext _ _) |>.trans
      (DiagSet.toSSet.map_id _)
  rw [Functor.map_comp, hT, Category.id_comp]
  rw [Pi.lift_π]
  exact toSSetPoint_comp_toSSet_map_vertexHom _

noncomputable def grayVerticesToDiagSetIso (p : ℕ) :
    graySimplexVertices.{u} p ≅
      SSet.toDiagSet.obj (∐ fun _ : Fin (p + 1) => (Δ[0] : SSet.{u})) :=
  have : PreservesColimits SSet.toDiagSet.{u} :=
    sSetDiagSetAdj.leftAdjoint_preservesColimits
  Sigma.mapIso (fun _ => pointIsoToDiagSetStdSimplex) ≪≫
    (PreservesCoproduct.iso SSet.toDiagSet (fun _ : Fin (p + 1) => (Δ[0] : SSet.{u}))).symm

theorem grayShapeVerticesι_eq {S : SSet.{u}} {p : ℕ}
    (v : Fin (p + 1) → S _⦋0⦌) :
    grayShapeVerticesι v =
      (grayVerticesToDiagSetIso p).hom ≫ SSet.toDiagSet.map (simplicialShapeVerticesι v) := by
  apply Sigma.hom_ext
  intro k
  simp only [grayShapeVerticesι, Sigma.ι_desc, grayVerticesToDiagSetIso,
    Iso.trans_hom, Iso.symm_hom, PreservesCoproduct.inv_hom, Category.assoc,
    Sigma.ι_mapIso_hom_assoc, ι_comp_sigmaComparison_assoc, ← Functor.map_comp,
    simplicialShapeVerticesι, Sigma.ι_desc]

instance mono_grayShapeVerticesι {S : SSet.{u}} {p : ℕ}
    (v : Fin (p + 1) → S _⦋0⦌) [Mono (simplicialShapeVerticesι v)] :
    Mono (grayShapeVerticesι v) := by
  rw [grayShapeVerticesι_eq]
  infer_instance

noncomputable def grayVertexBoundaryComparison (p : ℕ) (C : MarkedSSet.{u}) :
    (∏ᶜ fun _ : Fin (p + 1) => ((MarkedPresheaf.forget (D := edgeMarking)).obj C)) ⟶
      DiagSet.toSSet.obj ((grayHomRight (graySimplexVertices p)).obj (faceNerveRight.obj C)) :=
  Limits.Pi.map (fun _ => faceNerveRightComparison.app C) ≫
    (toSSetGrayHomVerticesIso p (faceNerveRight.obj C)).inv

theorem grayVertexBoundaryComparison_square {S : SSet.{u}} {p : ℕ}
    (v : Fin (p + 1) → S _⦋0⦌) (C : MarkedSSet.{u}) :
    SSet.ihomEvalVertices v ((MarkedPresheaf.forget (D := edgeMarking)).obj C) ≫
        grayVertexBoundaryComparison p C =
      (grayHomSimplicialComparison S).app C ≫
        DiagSet.toSSet.map
          ((grayHomRestrict (grayShapeVerticesι v)).app (faceNerveRight.obj C)) := by
  rw [grayVertexBoundaryComparison, ← Category.assoc,
    ← grayShapeVerticesι_comparison_square]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem grayVertexBoundaryComparison_point (C : MarkedSSet.{u}) {p : ℕ}
    (x : Fin (p + 1) → (faceNerveRight.obj C).Vertex)
    (c : Fin (p + 1) → ((MarkedPresheaf.forget (D := edgeMarking)).obj C) _⦋0⦌)
    (hc : ∀ k, (faceNerveRightComparison.app C).app _ (c k) =
      (faceNerveRight.obj C).vertexEquivSSet (x k)) :
    (Pi.lift fun k => SSet.yonedaEquiv.symm (c k)) ≫ grayVertexBoundaryComparison p C =
      toSSetPoint ≫ DiagSet.toSSet.map
        (diagramPoint ((graySimplexVerticesHomEquiv p (faceNerveRight.obj C)).symm x)) := by
  apply (cancel_mono (toSSetGrayHomVerticesIso p (faceNerveRight.obj C)).hom).1
  rw [grayVertexBoundaryComparison, Category.assoc, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, Category.assoc,
    diagramPoint_comp_toSSetGrayHomVerticesIso]
  apply Pi.hom_ext
  intro k
  exact (Category.assoc _ _ _).trans
    ((congrArg ((Pi.lift fun k => SSet.yonedaEquiv.symm (c k)) ≫ ·)
      (Limits.Pi.map_π (fun _ : Fin (p + 1) => faceNerveRightComparison.app C) k)).trans
      ((Pi.lift_π_assoc _ _ _).trans
        ((SSet.yonedaEquiv_symm_comp _ _).trans
          ((congrArg SSet.yonedaEquiv.symm (hc k)).trans
            (Pi.lift_π (fun j => SSet.yonedaEquiv.symm
              ((faceNerveRight.obj C).vertexEquivSSet (x j))) k).symm))))

noncomputable def grayVertexFibreComparison {S : SSet.{u}} {p : ℕ}
    (v : Fin (p + 1) → S _⦋0⦌) (C : MarkedSSet.{u})
    (x : Fin (p + 1) → (faceNerveRight.obj C).Vertex)
    (c : Fin (p + 1) → ((MarkedPresheaf.forget (D := edgeMarking)).obj C) _⦋0⦌)
    (hc : ∀ k, (faceNerveRightComparison.app C).app _ (c k) =
      (faceNerveRight.obj C).vertexEquivSSet (x k)) :
    SSet.ihomFibre v ((MarkedPresheaf.forget (D := edgeMarking)).obj C) c ⟶
      DiagSet.toSSet.obj (relativeMappingSpace (grayShapeVerticesι v)
        ((graySimplexVerticesHomEquiv p (faceNerveRight.obj C)).symm x)) :=
  (DiagSet.toSSet.map_isPullback (IsPullback.of_hasPullback _ _)).lift
    (SSet.ihomFibre.ι v _ c ≫ (grayHomSimplicialComparison S).app C)
    (pullback.snd _ _ ≫ toSSetPoint)
    (by
      exact (Category.assoc _ _ _).trans
        ((congrArg (SSet.ihomFibre.ι v _ c ≫ ·)
          (grayVertexBoundaryComparison_square v C).symm).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (· ≫ grayVertexBoundaryComparison p C)
              (pullback.condition (f := SSet.ihomEvalVertices v
                ((MarkedPresheaf.forget (D := edgeMarking)).obj C))
                (g := Pi.lift fun k => SSet.yonedaEquiv.symm (c k)))).trans
              ((Category.assoc _ _ _).trans
                ((congrArg (pullback.snd _ _ ≫ ·)
                  (grayVertexBoundaryComparison_point C x c hc)).trans
                    (Category.assoc _ _ _).symm))))))

@[reassoc]
theorem grayVertexFibreComparison_fst {S : SSet.{u}} {p : ℕ}
    (v : Fin (p + 1) → S _⦋0⦌) (C : MarkedSSet.{u})
    (x : Fin (p + 1) → (faceNerveRight.obj C).Vertex)
    (c : Fin (p + 1) → ((MarkedPresheaf.forget (D := edgeMarking)).obj C) _⦋0⦌)
    (hc : ∀ k, (faceNerveRightComparison.app C).app _ (c k) =
      (faceNerveRight.obj C).vertexEquivSSet (x k)) :
    grayVertexFibreComparison v C x c hc ≫ DiagSet.toSSet.map (pullback.fst _ _) =
      SSet.ihomFibre.ι v _ c ≫ (grayHomSimplicialComparison S).app C :=
  IsPullback.lift_fst _ _ _ _

theorem weakEquivalence_grayVertexBoundaryComparison (p : ℕ) (C : MarkedSSet.{u})
    [IsFibrant C] : WeakEquivalence (grayVertexBoundaryComparison p C) := by
  have : IsFibrant ((MarkedPresheaf.forget (D := edgeMarking)).obj C) :=
    Atoms.Homotopical.isQuillenEquivalence_flatForgetAdjunction.toIsQuillen.isFibrant_obj C
  have : IsFibrant ((DiagSet.toInfty 1).obj (faceNerveRight.obj C)) :=
    isQuillen_faceNerveAdjunction.isFibrant_obj C
  have : IsFibrant ((faceNerveRight ⋙ DiagSet.toSSet).obj C) :=
    isQuillen_sSetDiagSetAdj.isFibrant_obj ((DiagSet.toInfty 1).obj (faceNerveRight.obj C))
  have := weakEquivalence_faceNerveRightComparison_app C
  have := weakEquivalence_piMap (fun _ : Fin (p + 1) => faceNerveRightComparison.app C)
  dsimp only [grayVertexBoundaryComparison]
  infer_instance

theorem weakEquivalence_grayVertexFibreComparison {S : SSet.{u}} {p : ℕ}
    (v : Fin (p + 1) → S _⦋0⦌) [Mono (simplicialShapeVerticesι v)]
    (C : MarkedSSet.{u}) [IsFibrant C]
    (x : Fin (p + 1) → (faceNerveRight.obj C).Vertex)
    (c : Fin (p + 1) → ((MarkedPresheaf.forget (D := edgeMarking)).obj C) _⦋0⦌)
    (hc : ∀ k, (faceNerveRightComparison.app C).app _ (c k) =
      (faceNerveRight.obj C).vertexEquivSSet (x k)) :
    WeakEquivalence (grayVertexFibreComparison v C x c hc) := by
  let Q : SSet.{u} := (MarkedPresheaf.forget (D := edgeMarking)).obj C
  have hG : IsFibrant ((DiagSet.toInfty 1).obj (faceNerveRight.obj C)) :=
    isQuillen_faceNerveAdjunction.isFibrant_obj C
  have hGC : IsInftyCategory 1 (faceNerveRight.obj C) := (isFibrant_infty_iff 1 _).1 hG
  have : IsFibrant Q :=
    Atoms.Homotopical.isQuillenEquivalence_flatForgetAdjunction.toIsQuillen.isFibrant_obj C
  have : Q.Quasicategory := (isFibrant_iff_quasicategory _).1 inferInstance
  have := fibration_ihomEvalVertices v Q
  have : IsFibrant ((ihom (∐ fun _ : Fin (p + 1) => (Δ[0] : SSet.{u}))).obj Q) :=
    (isQuillen_ihomAdjunction _).isFibrant_obj Q
  have : IsFibrant (∏ᶜ fun _ : Fin (p + 1) => Q) :=
    isFibrant_of_fibration (ihomVerticesIso p Q).inv
  have := fibration_toInfty_one_grayHomRestrict (grayShapeVerticesι v) hGC
  have : Fibration (DiagSet.toSSet.map
      ((grayHomRestrict (grayShapeVerticesι v)).app (faceNerveRight.obj C))) :=
    isQuillen_sSetDiagSetAdj.fibration_map
      ((DiagSet.toInfty 1).map
        ((grayHomRestrict (grayShapeVerticesι v)).app (faceNerveRight.obj C)))
  have : IsFibrant ((DiagSet.toInfty 1).obj
      ((grayHomRight (graySimplexVertices p)).obj (faceNerveRight.obj C))) :=
    (isFibrant_infty_iff 1 _).2 (isInftyCategory_grayHomRight _ hGC)
  have : IsFibrant (DiagSet.toSSet.obj
      ((grayHomRight (graySimplexVertices p)).obj (faceNerveRight.obj C))) :=
    isQuillen_sSetDiagSetAdj.isFibrant_obj
      ((DiagSet.toInfty 1).obj ((grayHomRight (graySimplexVertices p)).obj (faceNerveRight.obj C)))
  have : IsFibrant (Δ[0] : SSet.{u}) :=
    (isFibrant_iff_of_isTerminal (𝟙 _) SSet.stdSimplex.isTerminalObj₀).2 inferInstance
  have : IsFibrant (DiagSet.toSSet.obj (ball.{u} atomPoint)) :=
    (isFibrant_iff_of_isTerminal (𝟙 _) isTerminalToSSetBallAtomPoint).2 inferInstance
  have : IsIso (toSSetPoint.{u}) :=
    isIso_of_isTerminal SSet.stdSimplex.isTerminalObj₀ isTerminalToSSetBallAtomPoint _
  have := weakEquivalence_grayHomSimplicialComparison_app S C
  have := weakEquivalence_grayVertexBoundaryComparison p C
  exact (IsPullback.of_hasPullback (SSet.ihomEvalVertices v Q)
      (Pi.lift fun k => SSet.yonedaEquiv.symm (c k))).weakEquivalence_map_of_fibration
    (DiagSet.toSSet.map_isPullback (IsPullback.of_hasPullback _ _))
    ((grayHomSimplicialComparison S).app C) (grayVertexBoundaryComparison p C)
    toSSetPoint (grayVertexFibreComparison v C x c hc)
    (grayVertexBoundaryComparison_square v C) (grayVertexBoundaryComparison_point C x c hc)
    (grayVertexFibreComparison_fst v C x c hc) (IsPullback.lift_snd _ _ _ _)

@[reassoc]
theorem relativeMappingSpaceMapOfSquare_fst {V A V' A' X : DiagSet.{u}}
    {i : V ⟶ A} {i' : V' ⟶ A'} (a : A' ⟶ A) (b : V' ⟶ V)
    (w : i' ≫ a = b ≫ i) {f : V ⟶ X} {f' : V' ⟶ X} (hf : f' = b ≫ f) :
    relativeMappingSpaceMapOfSquare a b w hf ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ (grayHomRestrict a).app X := by
  apply ((grayTensorRightAdjunction A').homEquiv _ X).symm.injective
  rw [homEquiv_symm_comp_grayHomRestrict]
  have h := relativeMappingSpaceHomEquiv_relativeMappingSpaceMapOfSquare a b w hf (𝟙 _)
  simpa only [relativeMappingSpaceHomEquiv, Equiv.coe_fn_mk, Category.id_comp] using h

noncomputable def grayVerticesReindex {p q : ℕ} (φ : Fin (q + 1) → Fin (p + 1)) :
    graySimplexVertices.{u} q ⟶ graySimplexVertices.{u} p :=
  Sigma.desc fun k => Sigma.ι (fun _ : Fin (p + 1) => ball.{u} atomPoint) (φ k)

theorem grayShapeVerticesι_reindex {S S' : SSet.{u}} {p q : ℕ}
    (v : Fin (p + 1) → S _⦋0⦌) (v' : Fin (q + 1) → S' _⦋0⦌)
    (s : S' ⟶ S) (φ : Fin (q + 1) → Fin (p + 1))
    (hv : ∀ k, s.app _ (v' k) = v (φ k)) :
    grayShapeVerticesι v' ≫ SSet.toDiagSet.map s =
      grayVerticesReindex φ ≫ grayShapeVerticesι v := by
  apply Sigma.hom_ext
  intro k
  rw [← Category.assoc, grayShapeVerticesι, Sigma.ι_desc, Category.assoc,
    ← Functor.map_comp, SSet.yonedaEquiv_symm_comp, hv,
    ← Category.assoc, grayVerticesReindex, Sigma.ι_desc, grayShapeVerticesι, Sigma.ι_desc]

theorem graySimplexVerticesHomEquiv_symm_reindex {X : DiagSet.{u}} {p q : ℕ}
    (x : Fin (p + 1) → X.Vertex) (φ : Fin (q + 1) → Fin (p + 1)) :
    (graySimplexVerticesHomEquiv q X).symm (x ∘ φ) =
      grayVerticesReindex φ ≫ (graySimplexVerticesHomEquiv p X).symm x := by
  apply Sigma.hom_ext
  intro k
  rw [ι_graySimplexVerticesHomEquiv_symm, ← Category.assoc,
    grayVerticesReindex, Sigma.ι_desc, ι_graySimplexVerticesHomEquiv_symm]
  rfl

theorem grayVertexFibreComparison_restrict {S S' : SSet.{u}} {p q : ℕ}
    (v : Fin (p + 1) → S _⦋0⦌) (v' : Fin (q + 1) → S' _⦋0⦌)
    (s : S' ⟶ S) (φ : Fin (q + 1) → Fin (p + 1))
    (hv : ∀ k, s.app _ (v' k) = v (φ k)) (C : MarkedSSet.{u})
    (x : Fin (p + 1) → (faceNerveRight.obj C).Vertex)
    (c : Fin (p + 1) → ((MarkedPresheaf.forget (D := edgeMarking)).obj C) _⦋0⦌)
    (hc : ∀ k, (faceNerveRightComparison.app C).app _ (c k) =
      (faceNerveRight.obj C).vertexEquivSSet (x k)) :
    SSet.ihomFibre.map s φ hv _ c ≫
        grayVertexFibreComparison v' C (x ∘ φ) (c ∘ φ) (fun k => hc (φ k)) =
      grayVertexFibreComparison v C x c hc ≫ DiagSet.toSSet.map
        (relativeMappingSpaceMapOfSquare (SSet.toDiagSet.map s) (grayVerticesReindex φ)
          (grayShapeVerticesι_reindex v v' s φ hv)
          (graySimplexVerticesHomEquiv_symm_reindex x φ)) := by
  have : PreservesLimitsOfSize.{0, 0} DiagSet.toSSet.{u} :=
    sSetDiagSetAdj.rightAdjoint_preservesLimits
  have : Mono (diagramPoint ((graySimplexVerticesHomEquiv q (faceNerveRight.obj C)).symm
      (x ∘ φ))) := isTerminalBallAtomPoint.mono_from _
  apply (cancel_mono (DiagSet.toSSet.map
    (pullback.fst ((grayHomRestrict (grayShapeVerticesι v')).app (faceNerveRight.obj C))
      (diagramPoint ((graySimplexVerticesHomEquiv q (faceNerveRight.obj C)).symm (x ∘ φ)))))).1
  rw [Category.assoc, grayVertexFibreComparison_fst, SSet.ihomFibre.map_ι_assoc,
    Category.assoc, ← Functor.map_comp, relativeMappingSpaceMapOfSquare_fst,
    Functor.map_comp, grayVertexFibreComparison_fst_assoc]
  exact congrArg (SSet.ihomFibre.ι v _ c ≫ ·)
    (pre_app_comp_grayHomSimplicialComparison_app s C)

theorem grayVertexFibreComparison_target_lift {C D : MarkedSSet.{u}} (f : C ⟶ D) {p : ℕ}
    (x : Fin (p + 1) → (faceNerveRight.obj C).Vertex)
    (c : Fin (p + 1) → ((MarkedPresheaf.forget (D := edgeMarking)).obj C) _⦋0⦌)
    (hc : ∀ k, (faceNerveRightComparison.app C).app _ (c k) =
      (faceNerveRight.obj C).vertexEquivSSet (x k)) (k : Fin (p + 1)) :
    (faceNerveRightComparison.app D).app _
      (((MarkedPresheaf.forget (D := edgeMarking)).map f).app _ (c k)) =
      (faceNerveRight.obj D).vertexEquivSSet ((x k).map (faceNerveRight.map f)) := by
  exact (congrArg (fun m => m.app _ (c k)) (faceNerveRightComparison.naturality f)).trans
    (congrArg ((DiagSet.toSSet.map (faceNerveRight.map f)).app _) (hc k))

theorem grayVertexFibreComparison_target {S : SSet.{u}} {p : ℕ}
    (v : Fin (p + 1) → S _⦋0⦌) {C D : MarkedSSet.{u}} (f : C ⟶ D)
    (x : Fin (p + 1) → (faceNerveRight.obj C).Vertex)
    (c : Fin (p + 1) → ((MarkedPresheaf.forget (D := edgeMarking)).obj C) _⦋0⦌)
    (hc : ∀ k, (faceNerveRightComparison.app C).app _ (c k) =
      (faceNerveRight.obj C).vertexEquivSSet (x k)) :
    simplicialVertexFibreTargetMap v ((MarkedPresheaf.forget (D := edgeMarking)).map f) c ≫
        grayVertexFibreComparison v D (fun k => (x k).map (faceNerveRight.map f))
          (fun k => ((MarkedPresheaf.forget (D := edgeMarking)).map f).app _ (c k))
          (grayVertexFibreComparison_target_lift f x c hc) =
      grayVertexFibreComparison v C x c hc ≫ DiagSet.toSSet.map
        (relativeMappingSpaceMapOfEq (grayShapeVerticesι v) (faceNerveRight.map f)
          (graySimplexVerticesHomEquiv_symm_comp (faceNerveRight.map f) x)) := by
  have : PreservesLimitsOfSize.{0, 0} DiagSet.toSSet.{u} :=
    sSetDiagSetAdj.rightAdjoint_preservesLimits
  have : Mono (diagramPoint ((graySimplexVerticesHomEquiv p (faceNerveRight.obj D)).symm
      (fun k => (x k).map (faceNerveRight.map f)))) := isTerminalBallAtomPoint.mono_from _
  apply (cancel_mono (DiagSet.toSSet.map
    (pullback.fst ((grayHomRestrict (grayShapeVerticesι v)).app (faceNerveRight.obj D))
      (diagramPoint ((graySimplexVerticesHomEquiv p (faceNerveRight.obj D)).symm
        (fun k => (x k).map (faceNerveRight.map f))))))).1
  rw [Category.assoc, grayVertexFibreComparison_fst, simplicialVertexFibreTargetMap_ι_assoc,
    Category.assoc, ← Functor.map_comp, relativeMappingSpaceMapOfEq_fst,
    Functor.map_comp, grayVertexFibreComparison_fst_assoc]
  simpa only [Functor.comp_map] using
    congrArg (SSet.ihomFibre.ι v _ c ≫ ·) ((grayHomSimplicialComparison S).naturality f)

theorem grayVertexFibreComparison_targetOfEq {S : SSet.{u}} {p : ℕ}
    (v : Fin (p + 1) → S _⦋0⦌) {C D : MarkedSSet.{u}} (f : C ⟶ D)
    (x : Fin (p + 1) → (faceNerveRight.obj C).Vertex)
    (y : Fin (p + 1) → (faceNerveRight.obj D).Vertex)
    (c : Fin (p + 1) → ((MarkedPresheaf.forget (D := edgeMarking)).obj C) _⦋0⦌)
    (d : Fin (p + 1) → ((MarkedPresheaf.forget (D := edgeMarking)).obj D) _⦋0⦌)
    (hx : ∀ k, (faceNerveRightComparison.app C).app _ (c k) =
      (faceNerveRight.obj C).vertexEquivSSet (x k))
    (hy : ∀ k, (faceNerveRightComparison.app D).app _ (d k) =
      (faceNerveRight.obj D).vertexEquivSSet (y k))
    (he : ∀ k, (x k).map (faceNerveRight.map f) = y k)
    (hd : ∀ k, ((MarkedPresheaf.forget (D := edgeMarking)).map f).app _ (c k) = d k) :
    simplicialVertexFibreTargetMapOfEq v
        ((MarkedPresheaf.forget (D := edgeMarking)).map f) c d hd ≫
        grayVertexFibreComparison v D y d hy =
      grayVertexFibreComparison v C x c hx ≫ DiagSet.toSSet.map
        (relativeMappingSpaceMapOfEq (grayShapeVerticesι v) (faceNerveRight.map f)
          ((graySimplexVerticesHomEquiv_symm_comp (faceNerveRight.map f) x).trans
            (congrArg (graySimplexVerticesHomEquiv p _).symm (funext he)))) := by
  obtain rfl : (fun k => (x k).map (faceNerveRight.map f)) = y := funext he
  obtain rfl : (fun k => ((MarkedPresheaf.forget (D := edgeMarking)).map f).app _ (c k)) = d :=
    funext hd
  exact grayVertexFibreComparison_target v f x c hx

theorem relativeMappingSpaceMapOfSquare_mapOfEq {V A V' A' X Y : DiagSet.{u}}
    {i : V ⟶ A} {i' : V' ⟶ A'} (a : A' ⟶ A) (b : V' ⟶ V)
    (w : i' ≫ a = b ≫ i) {f : V ⟶ X} {f' : V' ⟶ X} (hf : f' = b ≫ f)
    {g : V ⟶ Y} {g' : V' ⟶ Y} (hg : g' = b ≫ g) (t : X ⟶ Y)
    (h : f ≫ t = g) (h' : f' ≫ t = g') :
    relativeMappingSpaceMapOfSquare a b w hf ≫ relativeMappingSpaceMapOfEq i' t h' =
      relativeMappingSpaceMapOfEq i t h ≫ relativeMappingSpaceMapOfSquare a b w hg := by
  have : Mono (diagramPoint g') := isTerminalBallAtomPoint.mono_from _
  apply (cancel_mono (pullback.fst ((grayHomRestrict i').app Y) (diagramPoint g'))).1
  rw [Category.assoc, relativeMappingSpaceMapOfEq_fst,
    relativeMappingSpaceMapOfSquare_fst_assoc, Category.assoc,
    relativeMappingSpaceMapOfSquare_fst, relativeMappingSpaceMapOfEq_fst_assoc]
  exact congrArg (pullback.fst _ _ ≫ ·) ((grayHomRestrict a).naturality t)

theorem relativeMappingSpaceMapOfEq_square {V A X₀ X₁ X₂ X₃ : DiagSet.{u}}
    (i : V ⟶ A) (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₃) (f' : X₀ ⟶ X₂) (g' : X₂ ⟶ X₃)
    (w : f ≫ g = f' ≫ g') {c₀ : V ⟶ X₀} {c₁ : V ⟶ X₁}
    {c₂ : V ⟶ X₂} {c₃ : V ⟶ X₃}
    (h₀₁ : c₀ ≫ f = c₁) (h₁₃ : c₁ ≫ g = c₃)
    (h₀₂ : c₀ ≫ f' = c₂) (h₂₃ : c₂ ≫ g' = c₃) :
    relativeMappingSpaceMapOfEq i f h₀₁ ≫ relativeMappingSpaceMapOfEq i g h₁₃ =
      relativeMappingSpaceMapOfEq i f' h₀₂ ≫ relativeMappingSpaceMapOfEq i g' h₂₃ := by
  apply pullback.hom_ext
  · simp only [Category.assoc, relativeMappingSpaceMapOfEq_fst,
      relativeMappingSpaceMapOfEq_fst_assoc, ← Functor.map_comp, w]
  · simp only [relativeMappingSpaceMapOfEq, pullback.map, Category.assoc,
      pullback.lift_snd, Category.comp_id]

private theorem vertexEquivSSet_map {X Y : DiagSet.{u}} (f : X ⟶ Y) (x : X.Vertex) :
    (DiagSet.toSSet.map f).app _ (X.vertexEquivSSet x) = Y.vertexEquivSSet (x.map f) := rfl

section Localization

variable {H : Type*} [Category* H] (W : MorphismProperty SSet.{u})
  (hW : weakEquivalences SSet.{u} ≤ W) (L : SSet.{u} ⥤ H) [L.IsLocalization W]

noncomputable def grayRelativeFibreIso {S : SSet.{u}} {p : ℕ}
    (v : Fin (p + 1) → S _⦋0⦌) [Mono (simplicialShapeVerticesι v)]
    {X : DiagSet.{u}} (hX : IsInftyCategory 1 X)
    {C : MarkedSSet.{u}} [IsFibrant C] (η : X ⟶ faceNerveRight.obj C)
    [WeakEquivalence ((DiagSet.toInfty 1).map η)] (x : Fin (p + 1) → X.Vertex) :
    L.obj (DiagSet.toSSet.obj (relativeMappingSpace (grayShapeVerticesι v)
      ((graySimplexVerticesHomEquiv p X).symm x))) ≅
      L.obj (SSet.ihomFibre v (DiagSet.toSSet.obj X) (fun k => X.vertexEquivSSet (x k))) := by
  let c := fun k => faceNerveRightVertexLift C
    ((faceNerveRight.obj C).vertexEquivSSet ((x k).map η))
  have hc k : (faceNerveRightComparison.app C).app _ (c k) =
      (faceNerveRight.obj C).vertexEquivSSet ((x k).map η) :=
    faceNerveRightComparison_app_vertexLift C _
  have hG : IsInftyCategory 1 (faceNerveRight.obj C) :=
    (isFibrant_infty_iff 1 _).1 (isQuillen_faceNerveAdjunction.isFibrant_obj C)
  have : IsFibrant ((DiagSet.toInfty 1).obj X) := (isFibrant_infty_iff 1 _).2 hX
  have : IsFibrant ((DiagSet.toInfty 1).obj (faceNerveRight.obj C)) :=
    (isFibrant_infty_iff 1 _).2 hG
  have : (DiagSet.toSSet.obj X).Quasicategory :=
    (isFibrant_iff_quasicategory _).1
      (isQuillen_sSetDiagSetAdj.isFibrant_obj ((DiagSet.toInfty 1).obj X))
  have : SSet.Quasicategory ((faceNerveRight ⋙ DiagSet.toSSet).obj C) :=
    (isFibrant_iff_quasicategory _).1
      (isQuillen_sSetDiagSetAdj.isFibrant_obj ((DiagSet.toInfty 1).obj (faceNerveRight.obj C)))
  have : (DiagSet.toSSet.obj (faceNerveRight.obj C)).Quasicategory :=
    (isFibrant_iff_quasicategory _).1
      (isQuillen_sSetDiagSetAdj.isFibrant_obj ((DiagSet.toInfty 1).obj (faceNerveRight.obj C)))
  have : SSet.Quasicategory ((MarkedPresheaf.forget (D := edgeMarking)).obj C) :=
    (isFibrant_iff_quasicategory _).1
      (Atoms.Homotopical.isQuillenEquivalence_flatForgetAdjunction.toIsQuillen.isFibrant_obj C)
  have : WeakEquivalence (faceNerveRightComparison.app C) :=
    weakEquivalence_faceNerveRightComparison_app C
  have : WeakEquivalence (DiagSet.toSSet.map η) :=
    isQuillen_sSetDiagSetAdj.weakEquivalence_map_of_isFibrant ((DiagSet.toInfty 1).map η)
  exact Localization.isoOfHom L W
      (DiagSet.toSSet.map (relativeMappingSpaceMapOfEq (grayShapeVerticesι v) η
        (graySimplexVerticesHomEquiv_symm_comp η x)))
      (hW _ (weakEquivalence_toSSet_relativeMappingSpaceMapOfEq (grayShapeVerticesι v) η
        (graySimplexVerticesHomEquiv_symm_comp η x) hX hG).mem) ≪≫
    (Localization.isoOfHom L W (grayVertexFibreComparison v C
        (fun k => (x k).map η) c hc)
      (hW _ (weakEquivalence_grayVertexFibreComparison v C _ c hc).mem)).symm ≪≫
    Localization.isoOfHom L W
      (simplicialVertexFibreTargetMapOfEq v (faceNerveRightComparison.app C) c
        (fun k => (faceNerveRight.obj C).vertexEquivSSet ((x k).map η)) hc)
      (hW _ (weakEquivalence_simplicialVertexFibreTargetMapOfEq v
        (faceNerveRightComparison.app C) c _ hc).mem) ≪≫
    (Localization.isoOfHom L W
      (simplicialVertexFibreTargetMapOfEq v (DiagSet.toSSet.map η)
        (fun k => X.vertexEquivSSet (x k))
        (fun k => (faceNerveRight.obj C).vertexEquivSSet ((x k).map η))
        (fun k => vertexEquivSSet_map η (x k)))
      (hW _ (weakEquivalence_simplicialVertexFibreTargetMapOfEq v
        (DiagSet.toSSet.map η) _ _ (fun k => vertexEquivSSet_map η (x k))).mem)).symm

theorem grayRelativeFibreIso_hom_restrict {S S' : SSet.{u}} {p q : ℕ}
    (v : Fin (p + 1) → S _⦋0⦌) (v' : Fin (q + 1) → S' _⦋0⦌)
    [Mono (simplicialShapeVerticesι v)] [Mono (simplicialShapeVerticesι v')]
    (s : S' ⟶ S) (φ : Fin (q + 1) → Fin (p + 1))
    (hv : ∀ k, s.app _ (v' k) = v (φ k))
    {X : DiagSet.{u}} (hX : IsInftyCategory 1 X)
    {C : MarkedSSet.{u}} [IsFibrant C] (η : X ⟶ faceNerveRight.obj C)
    [WeakEquivalence ((DiagSet.toInfty 1).map η)] (x : Fin (p + 1) → X.Vertex) :
    L.map (DiagSet.toSSet.map
      (relativeMappingSpaceMapOfSquare (SSet.toDiagSet.map s) (grayVerticesReindex φ)
        (grayShapeVerticesι_reindex v v' s φ hv)
        (graySimplexVerticesHomEquiv_symm_reindex x φ))) ≫
        (grayRelativeFibreIso W hW L v' hX η (x ∘ φ)).hom =
      (grayRelativeFibreIso W hW L v hX η x).hom ≫
        L.map (SSet.ihomFibre.map s φ hv (DiagSet.toSSet.obj X)
          (fun k => X.vertexEquivSSet (x k))) := by
  let c := fun k => faceNerveRightVertexLift C
    ((faceNerveRight.obj C).vertexEquivSSet ((x k).map η))
  have hc k : (faceNerveRightComparison.app C).app _ (c k) =
      (faceNerveRight.obj C).vertexEquivSSet ((x k).map η) :=
    faceNerveRightComparison_app_vertexLift C _
  have h₁ := congrArg DiagSet.toSSet.map
    (relativeMappingSpaceMapOfSquare_mapOfEq (SSet.toDiagSet.map s) (grayVerticesReindex φ)
      (grayShapeVerticesι_reindex v v' s φ hv)
      (graySimplexVerticesHomEquiv_symm_reindex x φ)
      (graySimplexVerticesHomEquiv_symm_reindex (fun k => (x k).map η) φ) η
      (graySimplexVerticesHomEquiv_symm_comp η x)
      (graySimplexVerticesHomEquiv_symm_comp η (x ∘ φ)))
  simp only [Functor.map_comp] at h₁
  have h₂ := (grayVertexFibreComparison_restrict v v' s φ hv C
    (fun k => (x k).map η) c hc).symm
  have h₃ := simplicialVertexFibreTargetMapOfEq_restrict v v' s φ hv
    (faceNerveRightComparison.app C) c
    (fun k => (faceNerveRight.obj C).vertexEquivSSet ((x k).map η)) hc
  have h₄ := simplicialVertexFibreTargetMapOfEq_restrict v v' s φ hv
    (DiagSet.toSSet.map η) (fun k => X.vertexEquivSSet (x k))
    (fun k => (faceNerveRight.obj C).vertexEquivSSet ((x k).map η))
    (fun k => vertexEquivSSet_map η (x k))
  dsimp only [grayRelativeFibreIso, Iso.trans_hom, Iso.symm_hom]
  simp only [Localization.isoOfHom_hom, Category.assoc]
  erw [← L.map_comp_assoc, h₁, L.map_comp_assoc,
    Localization.map_comp_isoOfHom_inv_assoc L W _ _ _ _ _ _ h₂,
    ← L.map_comp_assoc, ← h₃, L.map_comp_assoc,
    Localization.map_comp_isoOfHom_inv L W _ _ _ _ _ _ h₄]

private theorem grayVertexComparison_target_square {S : SSet.{u}} {p : ℕ}
    (v : Fin (p + 1) → S _⦋0⦌) {C D : MarkedSSet.{u}} (t : C ⟶ D)
    (a : Fin (p + 1) → (faceNerveRight.obj C).Vertex)
    (b : Fin (p + 1) → (faceNerveRight.obj D).Vertex)
    (c : Fin (p + 1) → ((MarkedPresheaf.forget (D := edgeMarking)).obj C) _⦋0⦌)
    (d : Fin (p + 1) → ((MarkedPresheaf.forget (D := edgeMarking)).obj D) _⦋0⦌)
    (hc : ∀ k, (faceNerveRightComparison.app C).app _ (c k) =
      (faceNerveRight.obj C).vertexEquivSSet (a k))
    (hd : ∀ k, (faceNerveRightComparison.app D).app _ (d k) =
      (faceNerveRight.obj D).vertexEquivSSet (b k))
    (he : ∀ k, (a k).map (faceNerveRight.map t) = b k)
    (ht : ∀ k, ((MarkedPresheaf.forget (D := edgeMarking)).map t).app _ (c k) = d k) :
    simplicialVertexFibreTargetMapOfEq v (faceNerveRightComparison.app C) c
        (fun k => (faceNerveRight.obj C).vertexEquivSSet (a k)) hc ≫
      simplicialVertexFibreTargetMapOfEq v (DiagSet.toSSet.map (faceNerveRight.map t))
        (fun k => (faceNerveRight.obj C).vertexEquivSSet (a k))
        (fun k => (faceNerveRight.obj D).vertexEquivSSet (b k))
        (fun k => (vertexEquivSSet_map (faceNerveRight.map t) (a k)).trans
          (congrArg (faceNerveRight.obj D).vertexEquivSSet (he k))) =
    simplicialVertexFibreTargetMapOfEq v
        ((MarkedPresheaf.forget (D := edgeMarking)).map t) c d ht ≫
      simplicialVertexFibreTargetMapOfEq v (faceNerveRightComparison.app D) d
        (fun k => (faceNerveRight.obj D).vertexEquivSSet (b k)) hd :=
  simplicialVertexFibreTargetMapOfEq_square v (faceNerveRightComparison.app C)
    (DiagSet.toSSet.map (faceNerveRight.map t))
    ((MarkedPresheaf.forget (D := edgeMarking)).map t) (faceNerveRightComparison.app D)
    (faceNerveRightComparison.naturality t).symm c
    (fun k => (faceNerveRight.obj C).vertexEquivSSet (a k)) d
    (fun k => (faceNerveRight.obj D).vertexEquivSSet (b k)) hc
    (fun k => (vertexEquivSSet_map (faceNerveRight.map t) (a k)).trans
      (congrArg (faceNerveRight.obj D).vertexEquivSSet (he k))) ht hd

private theorem grayRelativeFibreIso_target_middle_square {S : SSet.{u}} {p : ℕ}
    (v : Fin (p + 1) → S _⦋0⦌)
    {X Y : DiagSet.{u}}
    {C D : MarkedSSet.{u}}
    (η : X ⟶ faceNerveRight.obj C)
    (η' : Y ⟶ faceNerveRight.obj D)
    (f : X ⟶ Y) (t : C ⟶ D) (w : η ≫ faceNerveRight.map t = f ≫ η')
    (x : Fin (p + 1) → X.Vertex) :
    let a := fun k => (x k).map η
    let b := fun k => ((x k).map f).map η'
    let c := fun k => faceNerveRightVertexLift C ((faceNerveRight.obj C).vertexEquivSSet (a k))
    let d := fun k => faceNerveRightVertexLift D ((faceNerveRight.obj D).vertexEquivSSet (b k))
    let hc := fun k => faceNerveRightComparison_app_vertexLift C
      ((faceNerveRight.obj C).vertexEquivSSet (a k))
    let hd := fun k => faceNerveRightComparison_app_vertexLift D
      ((faceNerveRight.obj D).vertexEquivSSet (b k))
    let he := fun k => congrArg (x k).map w
    let ht := fun k => (forget_map_app_faceNerveRightVertexLift t _).trans
      (congrArg (fun z => faceNerveRightVertexLift D
        ((faceNerveRight.obj D).vertexEquivSSet z)) (he k))
    grayVertexFibreComparison v C a c hc ≫ DiagSet.toSSet.map
        (relativeMappingSpaceMapOfEq (grayShapeVerticesι v) (faceNerveRight.map t)
          ((graySimplexVerticesHomEquiv_symm_comp (faceNerveRight.map t) a).trans
            (congrArg (graySimplexVerticesHomEquiv p _).symm (funext he)))) =
      simplicialVertexFibreTargetMapOfEq v
          ((MarkedPresheaf.forget (D := edgeMarking)).map t) c d ht ≫
        grayVertexFibreComparison v D b d hd := by
  let a := fun k => (x k).map η
  let b := fun k => ((x k).map f).map η'
  let c := fun k => faceNerveRightVertexLift C ((faceNerveRight.obj C).vertexEquivSSet (a k))
  let d := fun k => faceNerveRightVertexLift D ((faceNerveRight.obj D).vertexEquivSSet (b k))
  have he k : (a k).map (faceNerveRight.map t) = b k := congrArg (x k).map w
  have hc k : (faceNerveRightComparison.app C).app _ (c k) =
      (faceNerveRight.obj C).vertexEquivSSet (a k) := faceNerveRightComparison_app_vertexLift C _
  have hd k : (faceNerveRightComparison.app D).app _ (d k) =
      (faceNerveRight.obj D).vertexEquivSSet (b k) := faceNerveRightComparison_app_vertexLift D _
  have ht k : ((MarkedPresheaf.forget (D := edgeMarking)).map t).app _ (c k) = d k :=
    (forget_map_app_faceNerveRightVertexLift t _).trans
      (congrArg (fun z => faceNerveRightVertexLift D
        ((faceNerveRight.obj D).vertexEquivSSet z)) (he k))
  exact (grayVertexFibreComparison_targetOfEq v t a b c d hc hd he ht).symm

theorem grayRelativeFibreIso_hom_naturality_of_comp_eq {S : SSet.{u}} {p : ℕ}
    (v : Fin (p + 1) → S _⦋0⦌) [Mono (simplicialShapeVerticesι v)]
    {X Y : DiagSet.{u}} (hX : IsInftyCategory 1 X) (hY : IsInftyCategory 1 Y)
    {C D : MarkedSSet.{u}} [IsFibrant C] [IsFibrant D]
    (η : X ⟶ faceNerveRight.obj C) [WeakEquivalence ((DiagSet.toInfty 1).map η)]
    (η' : Y ⟶ faceNerveRight.obj D) [WeakEquivalence ((DiagSet.toInfty 1).map η')]
    (f : X ⟶ Y) (t : C ⟶ D) (w : η ≫ faceNerveRight.map t = f ≫ η')
    (x : Fin (p + 1) → X.Vertex) :
    L.map (DiagSet.toSSet.map (relativeMappingSpaceMapOfEq (grayShapeVerticesι v) f
        (graySimplexVerticesHomEquiv_symm_comp f x))) ≫
        (grayRelativeFibreIso W hW L v hY η' (fun k => (x k).map f)).hom =
      (grayRelativeFibreIso W hW L v hX η x).hom ≫
        L.map (simplicialVertexFibreTargetMapOfEq v (DiagSet.toSSet.map f)
          (fun k => X.vertexEquivSSet (x k))
          (fun k => Y.vertexEquivSSet ((x k).map f)) (fun k => vertexEquivSSet_map f (x k))) := by
  let a := fun k => (x k).map η
  let b := fun k => ((x k).map f).map η'
  let c := fun k => faceNerveRightVertexLift C ((faceNerveRight.obj C).vertexEquivSSet (a k))
  let d := fun k => faceNerveRightVertexLift D ((faceNerveRight.obj D).vertexEquivSSet (b k))
  have he k : (a k).map (faceNerveRight.map t) = b k := congrArg (x k).map w
  have hc k : (faceNerveRightComparison.app C).app _ (c k) =
      (faceNerveRight.obj C).vertexEquivSSet (a k) := faceNerveRightComparison_app_vertexLift C _
  have hd k : (faceNerveRightComparison.app D).app _ (d k) =
      (faceNerveRight.obj D).vertexEquivSSet (b k) := faceNerveRightComparison_app_vertexLift D _
  have ht k : ((MarkedPresheaf.forget (D := edgeMarking)).map t).app _ (c k) = d k :=
    (forget_map_app_faceNerveRightVertexLift t _).trans
      (congrArg (fun z => faceNerveRightVertexLift D
        ((faceNerveRight.obj D).vertexEquivSSet z)) (he k))
  let m := relativeMappingSpaceMapOfEq (grayShapeVerticesι v) (faceNerveRight.map t)
    ((graySimplexVerticesHomEquiv_symm_comp (faceNerveRight.map t) a).trans
      (congrArg (graySimplexVerticesHomEquiv p _).symm (funext he)))
  have h₁ : DiagSet.toSSet.map (relativeMappingSpaceMapOfEq (grayShapeVerticesι v) f
        (graySimplexVerticesHomEquiv_symm_comp f x)) ≫
        DiagSet.toSSet.map (relativeMappingSpaceMapOfEq (grayShapeVerticesι v) η'
          (graySimplexVerticesHomEquiv_symm_comp η' (fun k => (x k).map f))) =
      DiagSet.toSSet.map (relativeMappingSpaceMapOfEq (grayShapeVerticesι v) η
        (graySimplexVerticesHomEquiv_symm_comp η x)) ≫ DiagSet.toSSet.map m := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg DiagSet.toSSet.map (relativeMappingSpaceMapOfEq_square
      (grayShapeVerticesι v) f η' η (faceNerveRight.map t) w.symm _ _ _ _)
  have h₂ := grayRelativeFibreIso_target_middle_square v η η' f t w x
  have h₃ := grayVertexComparison_target_square v t a b c d hc hd he ht
  have h₄ := simplicialVertexFibreTargetMapOfEq_square v (DiagSet.toSSet.map f)
    (DiagSet.toSSet.map η') (DiagSet.toSSet.map η)
    (DiagSet.toSSet.map (faceNerveRight.map t))
    (by rw [← Functor.map_comp, ← Functor.map_comp, w])
    (fun k => X.vertexEquivSSet (x k)) (fun k => Y.vertexEquivSSet ((x k).map f))
    (fun k => (faceNerveRight.obj C).vertexEquivSSet (a k))
    (fun k => (faceNerveRight.obj D).vertexEquivSSet (b k))
    (fun k => vertexEquivSSet_map f (x k))
    (fun k => vertexEquivSSet_map η' ((x k).map f))
    (fun k => vertexEquivSSet_map η (x k))
    (fun k => (vertexEquivSSet_map (faceNerveRight.map t) (a k)).trans
      (congrArg (faceNerveRight.obj D).vertexEquivSSet (he k)))
  have k₁ := congrArg L.map h₁
  have k₃ := congrArg L.map h₃.symm
  simp only [Functor.map_comp] at k₁ k₃
  apply CommSq.w
  dsimp only [grayRelativeFibreIso, Iso.trans_hom, Iso.symm_hom]
  simp only [Localization.isoOfHom_hom]
  refine (CommSq.mk k₁).vert_comp
    (CommSq.vert_comp ?_ ((CommSq.mk k₃).vert_comp ?_))
  · exact ⟨Localization.map_comp_isoOfHom_inv L W _ _ _ _ _ _ h₂⟩
  · exact ⟨Localization.map_comp_isoOfHom_inv L W _ _ _ _ _ _ h₄.symm⟩

theorem grayRelativeFibreIso_eq {S : SSet.{u}} {p : ℕ}
    (v : Fin (p + 1) → S _⦋0⦌) [Mono (simplicialShapeVerticesι v)]
    {X : DiagSet.{u}} (hX : IsInftyCategory 1 X)
    {C D : MarkedSSet.{u}} [IsFibrant C] [IsFibrant D]
    (η : X ⟶ faceNerveRight.obj C) [WeakEquivalence ((DiagSet.toInfty 1).map η)]
    (η' : X ⟶ faceNerveRight.obj D) [WeakEquivalence ((DiagSet.toInfty 1).map η')]
    (x : Fin (p + 1) → X.Vertex) :
    grayRelativeFibreIso W hW L v hX η x = grayRelativeFibreIso W hW L v hX η' x := by
  obtain ⟨C₀, _, η₀, _, hη₀⟩ := exists_weakEquivalence_faceNerveRight X
  have key (C₁ : MarkedSSet.{u}) [IsFibrant C₁] (η₁ : X ⟶ faceNerveRight.obj C₁)
      [WeakEquivalence ((DiagSet.toInfty 1).map η₁)] :
      grayRelativeFibreIso W hW L v hX η₀ x = grayRelativeFibreIso W hW L v hX η₁ x := by
    obtain ⟨t, ht⟩ := hη₀ C₁ η₁
    have hn := grayRelativeFibreIso_hom_naturality_of_comp_eq W hW L v hX hX η₀ η₁
      (𝟙 X) t (ht.trans (Category.id_comp η₁).symm) x
    have h₁ : relativeMappingSpaceMapOfEq (grayShapeVerticesι v) (𝟙 X)
        (graySimplexVerticesHomEquiv_symm_comp (𝟙 X) x) = 𝟙 _ := by
      apply pullback.hom_ext
      · change _ = 𝟙 _ ≫ pullback.fst _ (diagramPoint
          ((graySimplexVerticesHomEquiv p X).symm x))
        simp only [relativeMappingSpaceMapOfEq_fst, CategoryTheory.Functor.map_id,
          Category.comp_id, Category.id_comp]
      · change _ = 𝟙 _ ≫ pullback.snd _ (diagramPoint
          ((graySimplexVerticesHomEquiv p X).symm x))
        simp only [relativeMappingSpaceMapOfEq, pullback.map, pullback.lift_snd,
          Category.comp_id, Category.id_comp]
    have h₂ : simplicialVertexFibreTargetMapOfEq v (DiagSet.toSSet.map (𝟙 X))
        (fun k => X.vertexEquivSSet (x k)) (fun k => X.vertexEquivSSet ((x k).map (𝟙 X)))
        (fun k => vertexEquivSSet_map (𝟙 X) (x k)) = 𝟙 _ := by
      apply SSet.ihomFibre.hom_ext
      change _ = 𝟙 _ ≫ SSet.ihomFibre.ι v _ (fun k => X.vertexEquivSSet (x k))
      rw [simplicialVertexFibreTargetMapOfEq_ι, CategoryTheory.Functor.map_id,
        CategoryTheory.Functor.map_id,
        Category.comp_id, Category.id_comp]
    erw [h₁, h₂, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
      Category.id_comp, Category.comp_id] at hn
    exact Iso.ext hn.symm
  exact (key C η).symm.trans (key D η')

theorem grayRelativeFibreIso_hom_naturality {S : SSet.{u}} {p : ℕ}
    (v : Fin (p + 1) → S _⦋0⦌) [Mono (simplicialShapeVerticesι v)]
    {X Y : DiagSet.{u}} (hX : IsInftyCategory 1 X) (hY : IsInftyCategory 1 Y)
    {C D : MarkedSSet.{u}} [IsFibrant C] [IsFibrant D]
    (η : X ⟶ faceNerveRight.obj C) [WeakEquivalence ((DiagSet.toInfty 1).map η)]
    (η' : Y ⟶ faceNerveRight.obj D) [WeakEquivalence ((DiagSet.toInfty 1).map η')]
    (f : X ⟶ Y) (x : Fin (p + 1) → X.Vertex) :
    L.map (DiagSet.toSSet.map (relativeMappingSpaceMapOfEq (grayShapeVerticesι v) f
        (graySimplexVerticesHomEquiv_symm_comp f x))) ≫
        (grayRelativeFibreIso W hW L v hY η' (fun k => (x k).map f)).hom =
      (grayRelativeFibreIso W hW L v hX η x).hom ≫
        L.map (simplicialVertexFibreTargetMapOfEq v (DiagSet.toSSet.map f)
          (fun k => X.vertexEquivSSet (x k))
          (fun k => Y.vertexEquivSSet ((x k).map f)) (fun k => vertexEquivSSet_map f (x k))) := by
  obtain ⟨C₀, _, η₀, _, hη₀⟩ := exists_weakEquivalence_faceNerveRight X
  obtain ⟨t, ht⟩ := hη₀ D (f ≫ η')
  rw [grayRelativeFibreIso_eq W hW L v hX η η₀]
  exact grayRelativeFibreIso_hom_naturality_of_comp_eq W hW L v hX hY η₀ η' f t ht x

noncomputable def grayRelativeFibreIsoOfEq {S : SSet.{u}} {p : ℕ}
    (v : Fin (p + 1) → S _⦋0⦌) [Mono (simplicialShapeVerticesι v)]
    (i : graySimplexVertices p ⟶ SSet.toDiagSet.obj S) (hi : i = grayShapeVerticesι v)
    {X : DiagSet.{u}} (hX : IsInftyCategory 1 X)
    {C : MarkedSSet.{u}} [IsFibrant C] (η : X ⟶ faceNerveRight.obj C)
    [WeakEquivalence ((DiagSet.toInfty 1).map η)] (x : Fin (p + 1) → X.Vertex) :
    L.obj (DiagSet.toSSet.obj (relativeMappingSpace i
      ((graySimplexVerticesHomEquiv p X).symm x))) ≅
      L.obj (SSet.ihomFibre v (DiagSet.toSSet.obj X) (fun k => X.vertexEquivSSet (x k))) := by
  subst i
  exact grayRelativeFibreIso W hW L v hX η x

theorem grayRelativeFibreIsoOfEq_hom_restrict {S S' : SSet.{u}} {p q : ℕ}
    (v : Fin (p + 1) → S _⦋0⦌) (v' : Fin (q + 1) → S' _⦋0⦌)
    [Mono (simplicialShapeVerticesι v)] [Mono (simplicialShapeVerticesι v')]
    (i : graySimplexVertices p ⟶ SSet.toDiagSet.obj S) (hi : i = grayShapeVerticesι v)
    (i' : graySimplexVertices q ⟶ SSet.toDiagSet.obj S') (hi' : i' = grayShapeVerticesι v')
    (s : S' ⟶ S) (φ : Fin (q + 1) → Fin (p + 1))
    (hv : ∀ k, s.app _ (v' k) = v (φ k))
    (w : i' ≫ SSet.toDiagSet.map s = grayVerticesReindex φ ≫ i)
    {X : DiagSet.{u}} (hX : IsInftyCategory 1 X)
    {C : MarkedSSet.{u}} [IsFibrant C] (η : X ⟶ faceNerveRight.obj C)
    [WeakEquivalence ((DiagSet.toInfty 1).map η)] (x : Fin (p + 1) → X.Vertex) :
    L.map (DiagSet.toSSet.map (relativeMappingSpaceMapOfSquare (SSet.toDiagSet.map s)
      (grayVerticesReindex φ) w (graySimplexVerticesHomEquiv_symm_reindex x φ))) ≫
        (grayRelativeFibreIsoOfEq W hW L v' i' hi' hX η (x ∘ φ)).hom =
      (grayRelativeFibreIsoOfEq W hW L v i hi hX η x).hom ≫
        L.map (SSet.ihomFibre.map s φ hv (DiagSet.toSSet.obj X)
          (fun k => X.vertexEquivSSet (x k))) := by
  subst i
  subst i'
  exact grayRelativeFibreIso_hom_restrict W hW L v v' s φ hv hX η x

end Localization

theorem grayShapeVerticesι_simplex (p : ℕ) :
    grayShapeVerticesι (SSet.stdSimplex.obj₀Equiv.symm :
        Fin (p + 1) → (Δ[p] : SSet.{u}) _⦋0⦌) = legacyGraySimplexVerticesι p := by
  apply (cancel_mono (toDiagSetObjStdSimplexIso p).hom).1
  apply Sigma.hom_ext
  intro k
  rw [grayShapeVerticesι, Sigma.ι_desc_assoc, ι_graySimplexVerticesι_comp_hom]
  change pointIsoToDiagSetStdSimplex.hom ≫
    SSet.toDiagSet.map (SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋p⦌ k)) ≫ _ = _
  refine (congrArg (pointIsoToDiagSetStdSimplex.hom ≫ ·)
    (stdSimplexCompToDiagSetIso.{u}.hom.naturality
      (SimplexCategory.const ⦋0⦌ ⦋p⦌ k))).trans ?_
  have e₀ : (toDiagSetObjStdSimplexIso 0).symm.hom ≫
      stdSimplexCompToDiagSetIso.{u}.hom.app (SimplexCategory.mk 0) = 𝟙 _ := Iso.inv_hom_id _
  rw [pointIsoToDiagSetStdSimplex, Iso.trans_hom, Category.assoc, reassoc_of% e₀]
  exact (congrArg (· ≫ 𝟙 _ ≫ uliftYoneda.map
      (simplexHom (SimplexCategory.const ⦋0⦌ ⦋p⦌ k).toOrderHom))
    (uliftYoneda.{u}.map_id (atomSimplex 0))).trans
      ((Category.id_comp _).trans (Category.id_comp _))

theorem grayShapeVerticesι_spine (p : ℕ) :
    grayShapeVerticesι (SSet.spineSubcomplex.spineId.{u} p).vertex =
      legacyGraySpineVerticesι p := by
  have : Mono (SSet.toDiagSet.map (SSet.spineSubcomplex.{u} p).ι) := SSet.toDiagSet.map_mono _
  apply (cancel_mono (SSet.toDiagSet.map (SSet.spineSubcomplex.{u} p).ι)).1
  have h := grayShapeVerticesι_reindex SSet.stdSimplex.obj₀Equiv.symm
    (SSet.spineSubcomplex.spineId.{u} p).vertex (SSet.spineSubcomplex p).ι id (fun _ => rfl)
  have hi : grayVerticesReindex.{u} (id : Fin (p + 1) → Fin (p + 1)) = 𝟙 _ := by
    apply Sigma.hom_ext
    intro k
    simp only [grayVerticesReindex, Sigma.ι_desc, Category.comp_id, id_eq]
  erw [hi, Category.id_comp, grayShapeVerticesι_simplex] at h
  exact h

section Specialization

variable {H : Type*} [Category* H] (W : MorphismProperty SSet.{u})
  (hW : weakEquivalences SSet.{u} ≤ W) (L : SSet.{u} ⥤ H) [L.IsLocalization W]
  {X : DiagSet.{u}} (hX : IsInftyCategory 1 X)
  {C : MarkedSSet.{u}} [IsFibrant C] (η : X ⟶ faceNerveRight.obj C)
  [WeakEquivalence ((DiagSet.toInfty 1).map η)]

noncomputable def graySimplexRelativeIso {p : ℕ} (x : Fin (p + 1) → X.Vertex) :
    L.obj (DiagSet.toSSet.obj (legacyGraySimplexFibre X x)) ≅
      L.obj (SSet.simplexFibre (DiagSet.toSSet.obj X)
        (fun k => X.vertexEquivSSet (x k))) := by
  exact grayRelativeFibreIsoOfEq W hW L SSet.stdSimplex.obj₀Equiv.symm
    (legacyGraySimplexVerticesι p) (grayShapeVerticesι_simplex p).symm hX η x

noncomputable def graySpineRelativeIso {p : ℕ} (x : Fin (p + 1) → X.Vertex) :
    L.obj (DiagSet.toSSet.obj (legacyGraySpineFibre X x)) ≅
      L.obj (SSet.spineFibre (DiagSet.toSSet.obj X)
        (fun k => X.vertexEquivSSet (x k))) := by
  exact grayRelativeFibreIsoOfEq W hW L (SSet.spineSubcomplex.spineId p).vertex
    (legacyGraySpineVerticesι p) (grayShapeVerticesι_spine p).symm hX η x

noncomputable def grayNativeSimplexRelativeIso {p : ℕ} (x : Fin (p + 1) → X.Vertex) :
    L.obj (DiagSet.toSSet.obj (graySimplexFibre X x)) ≅
      L.obj (SSet.simplexFibre (DiagSet.toSSet.obj X)
        (fun k => X.vertexEquivSSet (x k))) :=
  L.mapIso (DiagSet.toSSet.mapIso (nativeGraySimplexFibreIso X x)) ≪≫
    graySimplexRelativeIso W hW L hX η x

noncomputable def grayNativeSpineRelativeIso {p : ℕ} (x : Fin (p + 1) → X.Vertex) :
    L.obj (DiagSet.toSSet.obj (graySpineFibre X x)) ≅
      L.obj (SSet.spineFibre (DiagSet.toSSet.obj X)
        (fun k => X.vertexEquivSSet (x k))) :=
  L.mapIso (DiagSet.toSSet.mapIso (nativeGraySpineFibreIso X x)) ≪≫
    graySpineRelativeIso W hW L hX η x

theorem graySimplexRelativeIso_hom_restrict {p q : ℕ} (f : ⦋q⦌ ⟶ ⦋p⦌)
    (x : Fin (p + 1) → X.Vertex) :
    L.map (DiagSet.toSSet.map (graySimplexFibreMap X f x (x ∘ f.toOrderHom) (fun _ => rfl))) ≫
        (graySimplexRelativeIso W hW L hX η (x ∘ f.toOrderHom)).hom =
      (graySimplexRelativeIso W hW L hX η x).hom ≫
        L.map (SSet.simplexFibreMap (DiagSet.toSSet.obj X) f
          (fun k => X.vertexEquivSSet (x k))) := by
  exact grayRelativeFibreIsoOfEq_hom_restrict W hW L SSet.stdSimplex.obj₀Equiv.symm
    SSet.stdSimplex.obj₀Equiv.symm _ (grayShapeVerticesι_simplex p).symm
    _ (grayShapeVerticesι_simplex q).symm (SSet.stdSimplex.map f) f.toOrderHom
    (fun _ => rfl) (graySimplexVerticesι_comp_toDiagSet_map f) hX η x

theorem grayRelativeIso_hom_segal {p : ℕ} (x : Fin (p + 1) → X.Vertex) :
    L.map (DiagSet.toSSet.map (legacyGraySegalMap X x)) ≫
        (graySpineRelativeIso W hW L hX η x).hom =
      (graySimplexRelativeIso W hW L hX η x).hom ≫
        L.map (SSet.simplexFibreSegalMap (DiagSet.toSSet.obj X)
          (fun k => X.vertexEquivSSet (x k))) := by
  have hi : grayVerticesReindex.{u} (id : Fin (p + 1) → Fin (p + 1)) = 𝟙 _ := by
    apply Sigma.hom_ext
    intro k
    simp only [grayVerticesReindex, Sigma.ι_desc, Category.comp_id, id_eq]
  have w : legacyGraySpineVerticesι.{u} p ≫ SSet.toDiagSet.map (SSet.spineSubcomplex p).ι =
      grayVerticesReindex id ≫ legacyGraySimplexVerticesι p := by
    rw [hi, Category.id_comp]
    rfl
  have h := grayRelativeFibreIsoOfEq_hom_restrict W hW L SSet.stdSimplex.obj₀Equiv.symm
    (SSet.spineSubcomplex.spineId p).vertex _ (grayShapeVerticesι_simplex p).symm
    _ (grayShapeVerticesι_spine p).symm (SSet.spineSubcomplex p).ι id (fun _ => rfl) w hX η x
  have he : relativeMappingSpaceMapOfSquare (SSet.toDiagSet.map (SSet.spineSubcomplex p).ι)
      (grayVerticesReindex id) w (graySimplexVerticesHomEquiv_symm_reindex x id) =
        legacyGraySegalMap X x := by
    have : Mono (diagramPoint ((graySimplexVerticesHomEquiv p X).symm x)) :=
      isTerminalBallAtomPoint.mono_from _
    apply (cancel_mono (pullback.fst ((grayHomRestrict (legacyGraySpineVerticesι p)).app X)
      (diagramPoint ((graySimplexVerticesHomEquiv p X).symm x)))).1
    erw [relativeMappingSpaceMapOfSquare_fst]
    exact (pullback.lift_fst _ _ _).symm
  rw [he] at h
  exact h

theorem grayNativeRelativeIso_hom_segal {p : ℕ} (x : Fin (p + 1) → X.Vertex) :
    L.map (DiagSet.toSSet.map (graySegalMap X x)) ≫
        (grayNativeSpineRelativeIso W hW L hX η x).hom =
      (grayNativeSimplexRelativeIso W hW L hX η x).hom ≫
        L.map (SSet.simplexFibreSegalMap (DiagSet.toSSet.obj X)
          (fun k => X.vertexEquivSSet (x k))) := by
  dsimp only [grayNativeSpineRelativeIso, grayNativeSimplexRelativeIso, Iso.trans_hom]
  simp only [Functor.mapIso_hom, Category.assoc]
  rw [← L.map_comp_assoc, ← DiagSet.toSSet.map_comp, graySegalMap_comparison,
    DiagSet.toSSet.map_comp, L.map_comp_assoc, grayRelativeIso_hom_segal]

theorem grayLongEdge_eq_relative_restrict (x : Fin 3 → X.Vertex) :
    grayLongEdge X x =
      graySimplexFibreMap X (SimplexCategory.δ 1) x
        (x ∘ (SimplexCategory.δ (1 : Fin 3)).toOrderHom) (fun _ => rfl) ≫
          (graySimplexFibreOneIso X (x ∘ (SimplexCategory.δ (1 : Fin 3)).toOrderHom)).hom := by
  apply (isEdgeRestriction_grayLongEdge X x).eq
  intro T t
  erw [← Category.assoc, mappingSpaceHomEquiv_graySimplexFibreOneIso,
    relativeMappingSpaceHomEquiv_graySimplexFibreMap, ← Category.assoc, ← Functor.map_comp]

noncomputable def grayMappingRelativeIso (x : Fin 2 → X.Vertex) :
    L.obj (DiagSet.toSSet.obj (X.mappingSpace (x 0) (x 1)).toFunctor) ≅
      L.obj (SSet.mappingSpace (DiagSet.toSSet.obj X)
        (X.vertexEquivSSet (x 0)) (X.vertexEquivSSet (x 1))) :=
  L.mapIso (DiagSet.toSSet.mapIso (graySimplexFibreOneIso X x).symm) ≪≫
    graySimplexRelativeIso W hW L hX η x ≪≫
      L.mapIso (SSet.simplexFibreOneIso (DiagSet.toSSet.obj X)
        (fun k => X.vertexEquivSSet (x k)))

theorem grayNativeRelativeIso_hom_edge {p : ℕ} (f : ⦋1⦌ ⟶ ⦋p⦌)
    (x : Fin (p + 1) → X.Vertex) :
    L.map (DiagSet.toSSet.map ((nativeGraySimplexFibreIso X x).hom ≫
        graySimplexFibreMap X f x (x ∘ f.toOrderHom) (fun _ => rfl) ≫
          (graySimplexFibreOneIso X (x ∘ f.toOrderHom)).hom)) ≫
        (grayMappingRelativeIso W hW L hX η (x ∘ f.toOrderHom)).hom =
      (grayNativeSimplexRelativeIso W hW L hX η x).hom ≫
        L.map (SSet.simplexFibreMap (DiagSet.toSSet.obj X) f
          (fun k => X.vertexEquivSSet (x k)) ≫
            (SSet.simplexFibreOneIso (DiagSet.toSSet.obj X)
              (fun k => X.vertexEquivSSet ((x ∘ f.toOrderHom) k))).hom) := by
  dsimp only [grayMappingRelativeIso, grayNativeSimplexRelativeIso, Iso.trans_hom,
    Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv]
  simp only [Functor.map_comp, Category.assoc]
  rw [← L.map_comp_assoc (DiagSet.toSSet.map (graySimplexFibreOneIso X
      (x ∘ f.toOrderHom)).hom), ← DiagSet.toSSet.map_comp, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp]
  simpa only [Category.assoc, Functor.map_comp] using congrArg
    (fun m => L.map (DiagSet.toSSet.map (nativeGraySimplexFibreIso X x).hom) ≫ m ≫
      L.map (SSet.simplexFibreOneIso (DiagSet.toSSet.obj X)
        (fun k => X.vertexEquivSSet ((x ∘ f.toOrderHom) k))).hom)
    (graySimplexRelativeIso_hom_restrict W hW L hX η f x)

theorem grayNativeRelativeIso_hom_longEdge (x : Fin 3 → X.Vertex) :
    L.map (DiagSet.toSSet.map ((nativeGraySimplexFibreIso X x).hom ≫ grayLongEdge X x)) ≫
        (grayMappingRelativeIso W hW L hX η
          (x ∘ (SimplexCategory.δ (1 : Fin 3)).toOrderHom)).hom =
      (grayNativeSimplexRelativeIso W hW L hX η x).hom ≫
        L.map (SSet.simplexFibreEdge (DiagSet.toSSet.obj X)
          (fun k => X.vertexEquivSSet (x k)) 0 2 (by decide)) := by
  have h := grayNativeRelativeIso_hom_edge W hW L hX η (SimplexCategory.δ 1) x
  have e := grayLongEdge_eq_relative_restrict (X := X) x
  have hf : SimplexCategory.mkOfLe (0 : Fin 3) 2 (by decide) =
      SimplexCategory.δ 1 := by decide
  have hs : SSet.simplexFibreMap (DiagSet.toSSet.obj X) (SimplexCategory.δ 1)
        (fun k => X.vertexEquivSSet (x k)) ≫
        (SSet.simplexFibreOneIso (DiagSet.toSSet.obj X)
          (fun k => X.vertexEquivSSet ((x ∘ (SimplexCategory.δ 1).toOrderHom) k))).hom =
      SSet.simplexFibreEdge (DiagSet.toSSet.obj X)
        (fun k => X.vertexEquivSSet (x k)) 0 2 (by decide) := by
    apply pullback.hom_ext
    · erw [Category.assoc, SSet.simplexFibreOneIso_hom_fst,
        SSet.simplexFibreMap_ι, SSet.simplexFibreEdge_fst, hf]
    · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [← hs]
  exact (congrArg (fun m => L.map (DiagSet.toSSet.map
    ((nativeGraySimplexFibreIso X x).hom ≫ m)) ≫
      (grayMappingRelativeIso W hW L hX η
        (x ∘ (SimplexCategory.δ (1 : Fin 3)).toOrderHom)).hom) e).trans h

noncomputable def toSSetGraySpineTwoIso (x : Fin 3 → X.Vertex) :
    DiagSet.toSSet.obj (graySpineFibre X x) ≅
      DiagSet.toSSet.obj (X.mappingSpace (x 0) (x 1)).toFunctor ⨯
        DiagSet.toSSet.obj (X.mappingSpace (x 1) (x 2)).toFunctor :=
  have : PreservesLimitsOfShape (Discrete WalkingPair) DiagSet.toSSet.{u} :=
    sSetDiagSetAdj.rightAdjoint_preservesLimits.preservesLimitsOfShape
  DiagSet.toSSet.mapIso (graySpineFibreTwoIso X x) ≪≫
    asIso (prodComparison DiagSet.toSSet _ _)

theorem toSSetGraySpineTwoIso_hom (x : Fin 3 → X.Vertex) :
    (toSSetGraySpineTwoIso x).hom =
      (toSSetGraySpineFibreIso X x).hom ≫ prod.lift (Pi.π _ 0) (Pi.π _ 1) :=
  toSSet_map_graySpineFibreTwoIso_hom_prodComparison X x

noncomputable def grayBinaryRelativeIso (x : Fin 3 → X.Vertex) :
    L.obj (DiagSet.toSSet.obj (X.mappingSpace (x 0) (x 1)).toFunctor ⨯
      DiagSet.toSSet.obj (X.mappingSpace (x 1) (x 2)).toFunctor) ≅
      L.obj (SSet.mappingSpace (DiagSet.toSSet.obj X)
        (X.vertexEquivSSet (x 0)) (X.vertexEquivSSet (x 1)) ⨯
          SSet.mappingSpace (DiagSet.toSSet.obj X)
            (X.vertexEquivSSet (x 1)) (X.vertexEquivSSet (x 2))) :=
  (L.mapIso (toSSetGraySpineTwoIso x)).symm ≪≫
    grayNativeSpineRelativeIso W hW L hX η x ≪≫
      L.mapIso (SSet.simplexFibreSpineTwoIso (DiagSet.toSSet.obj X)
        (fun k => X.vertexEquivSSet (x k)))

theorem grayBinaryRelativeIso_hom_segal (x : Fin 3 → X.Vertex) :
    L.map (DiagSet.toSSet.map (graySegalMap X x) ≫
        (toSSetGraySpineTwoIso x).hom) ≫
          (grayBinaryRelativeIso W hW L hX η x).hom =
      (grayNativeSimplexRelativeIso W hW L hX η x).hom ≫
        L.map (SSet.simplexFibreSegalMap (DiagSet.toSSet.obj X)
          (fun k => X.vertexEquivSSet (x k)) ≫
            (SSet.simplexFibreSpineTwoIso (DiagSet.toSSet.obj X)
              (fun k => X.vertexEquivSSet (x k))).hom) := by
  dsimp only [grayBinaryRelativeIso, Iso.trans_hom, Iso.symm_hom]
  simp only [Functor.mapIso_inv, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [← L.map_comp_assoc (toSSetGraySpineTwoIso x).hom,
    Iso.hom_inv_id, L.map_id, Category.id_comp]
  simpa only [Category.assoc] using congrArg
    (· ≫ L.map (SSet.simplexFibreSpineTwoIso (DiagSet.toSSet.obj X)
      (fun k => X.vertexEquivSSet (x k))).hom)
    (grayNativeRelativeIso_hom_segal W hW L hX η x)

end Specialization

end Atoms.Diagrammatic
