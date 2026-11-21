import Atoms.Diagrammatic.Joyal.GrayHomComparison
import Atoms.Diagrammatic.Joyal.DimensionShift
import Atoms.Diagrammatic.KanComparison
import Atoms.Diagrammatic.Limits.GrayHomBoundary
import Atoms.Homotopical.Simplicial.JoyalKan
import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.MappingSpaceMap
import Atoms.Homotopical.Simplicial.FullyFaithful

open CategoryTheory Limits Simplicial MonoidalClosed HomotopicalAlgebra Opposite
open Atoms.Shape Atoms.Homotopical

universe u

namespace Atoms.Diagrammatic

private noncomputable def isColimitToDiagSetBoundary :
    IsColimit (BinaryCofan.mk
      (SSet.toDiagSet.map (SSet.boundary.ι 1 : Δ[0] ⟶ (∂Δ[1] : SSet.{u})))
      (SSet.toDiagSet.map (SSet.boundary.ι 0 : Δ[0] ⟶ (∂Δ[1] : SSet.{u})))) :=
  have : PreservesColimitsOfSize.{0, 0} SSet.toDiagSet.{u} :=
    sSetDiagSetAdj.leftAdjoint_preservesColimits
  isColimitMapCoconeBinaryCofanEquiv SSet.toDiagSet _ _
    (isColimitOfPreserves SSet.toDiagSet SSet.boundaryOneIsColimit)

noncomputable def intervalBoundaryToDiagSet :
    intervalBoundary.{u} ⟶ SSet.toDiagSet.obj (∂Δ[1] : SSet.{u}) :=
  coprod.desc (pointIsoToDiagSetStdSimplex.hom ≫ SSet.toDiagSet.map (SSet.boundary.ι 1))
    (pointIsoToDiagSetStdSimplex.hom ≫ SSet.toDiagSet.map (SSet.boundary.ι 0))

@[reassoc]
private theorem intervalBoundaryToDiagSet_comp_inclusion (α : Bool) :
    cond α (coprod.inr : ball.{u} atomPoint ⟶ intervalBoundary) coprod.inl ≫
        intervalBoundaryToDiagSet =
      pointIsoToDiagSetStdSimplex.hom ≫
        SSet.toDiagSet.map (SSet.boundary.ι (cond α 0 1)) := by
  cases α <;> simp only [cond_false, cond_true, intervalBoundaryToDiagSet,
    coprod.inl_desc, coprod.inr_desc]

instance isIso_intervalBoundaryToDiagSet : IsIso intervalBoundaryToDiagSet.{u} := by
  let l : SSet.toDiagSet.obj (∂Δ[1] : SSet.{u}) ⟶ intervalBoundary.{u} :=
    isColimitToDiagSetBoundary.{u}.desc (BinaryCofan.mk
      (pointIsoToDiagSetStdSimplex.{u}.inv ≫ (coprod.inl : _ ⟶ intervalBoundary.{u}))
      (pointIsoToDiagSetStdSimplex.{u}.inv ≫ (coprod.inr : _ ⟶ intervalBoundary.{u})))
  have hl (α : Bool) : SSet.toDiagSet.map (SSet.boundary.ι (cond α 0 1)) ≫ l =
      pointIsoToDiagSetStdSimplex.{u}.inv ≫
        cond α (coprod.inr : _ ⟶ intervalBoundary.{u}) coprod.inl := by
    cases α
    · exact isColimitToDiagSetBoundary.{u}.fac _ ⟨.left⟩
    · exact isColimitToDiagSetBoundary.{u}.fac _ ⟨.right⟩
  have hli (α : Bool) :
      cond α (coprod.inr : ball.{u} atomPoint ⟶ intervalBoundary) coprod.inl ≫
        intervalBoundaryToDiagSet ≫ l =
      cond α coprod.inr coprod.inl ≫ 𝟙 _ := by
    rw [intervalBoundaryToDiagSet_comp_inclusion_assoc, hl,
      Iso.hom_inv_id_assoc, Category.comp_id]
  have hri (α : Bool) :
      SSet.toDiagSet.map (SSet.boundary.ι (cond α 0 1)) ≫
        l ≫ intervalBoundaryToDiagSet =
      SSet.toDiagSet.map (SSet.boundary.ι (cond α 0 1)) ≫ 𝟙 _ := by
    rw [reassoc_of% hl α, intervalBoundaryToDiagSet_comp_inclusion,
      Iso.inv_hom_id_assoc, Category.comp_id]
  exact ⟨l, coprod.hom_ext (hli false) (hli true),
    BinaryCofan.IsColimit.hom_ext isColimitToDiagSetBoundary.{u} (hri false) (hri true)⟩

private theorem pointIso_comp_toDiagSet_map_δ (i : Fin 2) :
    pointIsoToDiagSetStdSimplex.{u}.hom ≫ SSet.toDiagSet.map (SSet.stdSimplex.δ i) ≫
        (toDiagSetObjStdSimplexIso 1).hom =
      uliftYoneda.map (simplexHom (SimplexCategory.δ i).toOrderHom) := by
  refine (congrArg (pointIsoToDiagSetStdSimplex.{u}.hom ≫ ·)
    (stdSimplexCompToDiagSetIso.{u}.hom.naturality (SimplexCategory.δ i))).trans ?_
  have e₀ : (toDiagSetObjStdSimplexIso 0).symm.hom ≫
      stdSimplexCompToDiagSetIso.{u}.hom.app (SimplexCategory.mk 0) = 𝟙 _ :=
    Iso.inv_hom_id _
  rw [pointIsoToDiagSetStdSimplex, Iso.trans_hom, Category.assoc, reassoc_of% e₀]
  exact (congrArg (· ≫ 𝟙 _ ≫ uliftYoneda.map (simplexHom (SimplexCategory.δ i).toOrderHom))
    (uliftYoneda.{u}.map_id (atomSimplex 0))).trans
    ((Category.id_comp _).trans (Category.id_comp _))

@[reassoc]
theorem intervalBoundaryToDiagSet_comp_toDiagSet_map_ι :
    intervalBoundaryToDiagSet.{u} ≫ SSet.toDiagSet.map (∂Δ[1] : (Δ[1] : SSet.{u}).Subcomplex).ι ≫
        (toDiagSetObjStdSimplexIso 1).hom = intervalBoundaryι := by
  have h (α : Bool) :
      cond α (coprod.inr : ball.{u} atomPoint ⟶ intervalBoundary) coprod.inl ≫
          intervalBoundaryToDiagSet ≫ SSet.toDiagSet.map (∂Δ[1] : (Δ[1] : SSet.{u}).Subcomplex).ι ≫
          (toDiagSetObjStdSimplexIso 1).hom =
        cond α coprod.inr coprod.inl ≫ intervalBoundaryι.{u} := by
    rw [intervalBoundaryToDiagSet_comp_inclusion_assoc,
      ← Functor.map_comp_assoc, SSet.boundary.ι_ι, pointIso_comp_toDiagSet_map_δ]
    cases α <;> simp only [cond_false, cond_true, intervalBoundaryι,
      coprod.inl_desc, coprod.inr_desc] <;> rfl
  exact coprod.hom_ext (h false) (h true)

private theorem subsingleton_atomPoint_ogp : Subsingleton atomPoint.ogp :=
  atomPoint.toMoleculeShape.subsingleton_of_dimension_eq_zero dimension_atomPoint

private theorem faceNerve_toDiagSet_point_hom_ext {K : MarkedSSet.{u}}
    (f g : K ⟶ faceNerve.obj (SSet.toDiagSet.obj (Δ[0] : SSet.{u}))) : f = g := by
  have := subsingleton_atomPoint_ogp
  refine (cancel_mono (faceNerve.map pointIsoToDiagSetStdSimplex.{u}.inv ≫
    yonedaCompFaceNerveIso.{u}.hom.app atomPoint)).1 (MarkedPresheaf.hom_ext ?_)
  ext ⟨⟨k⟩⟩ z
  exact nerve.ext_of_isThin (C := ULift.{u} atomPoint.ogp)
    (funext fun _ => ULift.ext _ _ (Subsingleton.elim _ _))

private noncomputable def faceNervePointSection :
    (MarkedPresheaf.flat edgeMarking).obj (Δ[0] : SSet.{u}) ⟶
      faceNerve.obj (SSet.toDiagSet.obj (Δ[0] : SSet.{u})) :=
  ((MarkedPresheaf.flatForgetAdjunction edgeMarking).homEquiv _ _).symm
    (SSet.yonedaEquiv.symm ((MarkedPresheaf.forget.map
      (yonedaCompFaceNerveIso.{u}.inv.app atomPoint ≫
        faceNerve.map pointIsoToDiagSetStdSimplex.{u}.hom)).app _
      (ComposableArrows.mk₀ (ULift.up atomPoint.top))))

noncomputable def faceNerveRightVertexLift (C : MarkedSSet.{u})
    (v : (DiagSet.toSSet.obj (faceNerveRight.obj C)) _⦋0⦌) :
    ((MarkedPresheaf.forget (D := edgeMarking)).obj C) _⦋0⦌ :=
  SSet.yonedaEquiv ((MarkedPresheaf.flatForgetAdjunction edgeMarking).homEquiv _ _
    (faceNervePointSection ≫ (faceNerveSSetAdjunction.homEquiv _ _).symm (SSet.yonedaEquiv.symm v)))

theorem faceNerveRightComparison_app_vertexLift (C : MarkedSSet.{u})
    (v : (DiagSet.toSSet.obj (faceNerveRight.obj C)) _⦋0⦌) :
    (faceNerveRightComparison.app C).app _ (faceNerveRightVertexLift C v) = v := by
  let g := faceNervePointSection.{u} ≫
    (faceNerveSSetAdjunction.homEquiv _ _).symm (SSet.yonedaEquiv.symm v)
  have h := homEquiv_conjugateEquiv_app (MarkedPresheaf.flatForgetAdjunction edgeMarking)
    faceNerveSSetAdjunction faceNerveToDiagSetFlat g
  have e : faceNerveToDiagSetFlat.app _ ≫ g =
      (faceNerveSSetAdjunction.homEquiv _ _).symm (SSet.yonedaEquiv.symm v) :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
      (faceNerve_toDiagSet_point_hom_ext _ (𝟙 _))).trans (Category.id_comp _))
  have h' : SSet.yonedaEquiv.symm v =
      (MarkedPresheaf.flatForgetAdjunction edgeMarking).homEquiv _ _ g ≫
        faceNerveRightComparison.app C :=
    ((Equiv.apply_symm_apply (faceNerveSSetAdjunction.homEquiv _ _) _).symm.trans
      (congrArg (faceNerveSSetAdjunction.homEquiv _ _) e.symm)).trans h
  exact ((SSet.yonedaEquiv_comp _ _).symm.trans (congrArg SSet.yonedaEquiv h'.symm)).trans
    (Equiv.apply_symm_apply _ _)

theorem forget_map_app_faceNerveRightVertexLift {C C' : MarkedSSet.{u}} (c : C ⟶ C')
    (v : (DiagSet.toSSet.obj (faceNerveRight.obj C)) _⦋0⦌) :
    ((MarkedPresheaf.forget (D := edgeMarking)).map c).app _ (faceNerveRightVertexLift C v) =
      faceNerveRightVertexLift C' ((DiagSet.toSSet.map (faceNerveRight.map c)).app _ v) := by
  refine (SSet.yonedaEquiv_comp _ _).symm.trans (congrArg SSet.yonedaEquiv ?_)
  rw [← Adjunction.homEquiv_naturality_right]
  exact congrArg _ ((Category.assoc _ _ _).trans (congrArg (faceNervePointSection ≫ ·)
    ((faceNerveSSetAdjunction.homEquiv_naturality_right_symm (SSet.yonedaEquiv.symm v) c).symm.trans
      (congrArg _ (SSet.yonedaEquiv_symm_comp _ _)))))

section Restriction

variable (C : MarkedSSet.{u})

noncomputable def intervalComparison :
    (ihom Δ[1]).obj ((MarkedPresheaf.forget (D := edgeMarking)).obj C) ⟶
      DiagSet.toSSet.obj ((grayHomRight (ball.{u} (atomSimplex 1))).obj (faceNerveRight.obj C)) :=
  (grayHomSimplicialComparison Δ[1]).app C ≫
    DiagSet.toSSet.map ((grayHomRestrict (toDiagSetObjStdSimplexIso 1).inv).app _)

noncomputable def boundaryComparison :
    (ihom (∂Δ[1] : SSet.{u})).obj ((MarkedPresheaf.forget (D := edgeMarking)).obj C) ⟶
      DiagSet.toSSet.obj ((grayHomRight intervalBoundary.{u}).obj (faceNerveRight.obj C)) :=
  (grayHomSimplicialComparison (∂Δ[1] : SSet.{u})).app C ≫
    DiagSet.toSSet.map ((grayHomRestrict intervalBoundaryToDiagSet).app _)

@[reassoc]
theorem pre_app_comp_boundaryComparison :
    (pre (∂Δ[1] : (Δ[1] : SSet.{u}).Subcomplex).ι).app _ ≫ boundaryComparison C =
      intervalComparison C ≫
        DiagSet.toSSet.map ((grayHomRestrict intervalBoundaryι).app (faceNerveRight.obj C)) := by
  have e : intervalBoundaryToDiagSet.{u} ≫
      SSet.toDiagSet.map (∂Δ[1] : (Δ[1] : SSet.{u}).Subcomplex).ι =
        intervalBoundaryι ≫ (toDiagSetObjStdSimplexIso 1).inv :=
    (Iso.eq_comp_inv _).2 ((Category.assoc _ _ _).trans
      intervalBoundaryToDiagSet_comp_toDiagSet_map_ι)
  rw [boundaryComparison, pre_app_comp_grayHomSimplicialComparison_app_assoc, intervalComparison,
    Category.assoc, ← Functor.map_comp, ← Functor.map_comp, ← NatTrans.comp_app,
    ← NatTrans.comp_app, ← grayHomRestrict_comp, ← grayHomRestrict_comp, e]

private theorem grayHomRestrict_intervalBoundaryToDiagSet_comp_proj (Y : DiagSet.{u})
    (α : Bool) :
    (grayHomRestrict intervalBoundaryToDiagSet).app Y ≫
        cond α (grayHomBoundaryFan Y).snd (grayHomBoundaryFan Y).fst =
      grayHomEvalVertex (SSet.yonedaEquiv
        (SSet.boundary.ι (cond α 0 1) : Δ[0] ⟶ (∂Δ[1] : SSet.{u}))) Y := by
  have h := intervalBoundaryToDiagSet_comp_inclusion.{u} α
  have e : cond α (grayHomBoundaryFan Y).snd (grayHomBoundaryFan Y).fst =
      (grayHomRestrict (cond α (coprod.inr : ball.{u} atomPoint ⟶ intervalBoundary)
        coprod.inl)).app Y ≫ grayHomRightPointIso.hom.app Y := by
    cases α <;> rfl
  exact (congrArg ((grayHomRestrict intervalBoundaryToDiagSet).app Y ≫ ·) e).trans (by
    rw [grayHomEvalVertex, Equiv.symm_apply_apply]
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ grayHomRightPointIso.hom.app Y)
        ((NatTrans.congr_app (grayHomRestrict_comp _ _) Y).symm.trans
          (congrArg (fun f => (grayHomRestrict f).app Y) h))))

private theorem boundary_ι_comp_ihomPointEquiv_boundaryPoint {Q : SSet.{u}}
    (c₀ c₁ : Q _⦋0⦌) (α : Bool) :
    SSet.boundary.ι (cond α 0 1) ≫
        SSet.ihomPointEquiv _ Q (SSet.boundaryPoint c₀ c₁) =
      SSet.yonedaEquiv.symm (cond α c₁ c₀) := by
  have h := SSet.boundaryPoint_comp_boundaryEval c₀ c₁
  rw [SSet.boundaryEval, CartesianMonoidalCategory.comp_lift] at h
  rw [← Equiv.symm_apply_apply SSet.yonedaEquiv (SSet.boundary.ι (cond α 0 1)),
    ← SSet.comp_evalVertex_eq]
  have e := congrArg (· ≫ cond α (CartesianMonoidalCategory.snd _ _)
    (CartesianMonoidalCategory.fst _ _)) h
  cases α <;> simpa using e

@[reassoc]
theorem boundaryPoint_comp_boundaryComparison
    {c₀ c₁ : ((MarkedPresheaf.forget (D := edgeMarking)).obj C) _⦋0⦌}
    {y₀ y₁ : (faceNerveRight.obj C).Vertex}
    (h₀ : (faceNerveRightComparison.app C).app _ c₀ = (faceNerveRight.obj C).vertexEquivSSet y₀)
    (h₁ : (faceNerveRightComparison.app C).app _ c₁ = (faceNerveRight.obj C).vertexEquivSSet y₁) :
    SSet.boundaryPoint c₀ c₁ ≫ boundaryComparison C =
      toSSetPoint ≫ DiagSet.toSSet.map ((faceNerveRight.obj C).endpointsPoint y₀ y₁) := by
  have hT : isTerminalBallAtomPoint.{u}.from (ball atomPoint) = 𝟙 _ :=
    isTerminalBallAtomPoint.hom_ext _ _
  have L (α : Bool) : (SSet.boundaryPoint c₀ c₁ ≫ boundaryComparison C) ≫
      DiagSet.toSSet.map (cond α (grayHomBoundaryFan (faceNerveRight.obj C)).snd
        (grayHomBoundaryFan (faceNerveRight.obj C)).fst) =
        SSet.yonedaEquiv.symm ((faceNerveRight.obj C).vertexEquivSSet (cond α y₁ y₀)) := by
    have hpα := boundary_ι_comp_ihomPointEquiv_boundaryPoint c₀ c₁ α
    have e : DiagSet.toSSet.map ((grayHomRestrict intervalBoundaryToDiagSet).app
          (faceNerveRight.obj C)) ≫
        DiagSet.toSSet.map (cond α (grayHomBoundaryFan (faceNerveRight.obj C)).snd
        (grayHomBoundaryFan (faceNerveRight.obj C)).fst) =
          DiagSet.toSSet.map (grayHomEvalVertex
            (SSet.yonedaEquiv (SSet.boundary.ι (cond α 0 1) : Δ[0] ⟶ (∂Δ[1] : SSet.{u})))
      _) :=
      (DiagSet.toSSet.map_comp _ _).symm.trans
        (congrArg DiagSet.toSSet.map (grayHomRestrict_intervalBoundaryToDiagSet_comp_proj _ α))
    exact (Category.assoc _ _ _).trans ((congrArg (SSet.boundaryPoint c₀ c₁ ≫ ·)
      ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) e))).trans
      ((comp_grayHomSimplicialComparison_app_grayHomEvalVertex C _ _).trans
        ((congrArg (· ≫ faceNerveRightComparison.app C)
          ((congrArg (· ≫ _) (Equiv.symm_apply_apply _ _)).trans hpα)).trans
          ((SSet.yonedaEquiv_symm_comp _ _).trans (congrArg _ (by cases α <;> assumption))))))
  have R (α : Bool) : (toSSetPoint ≫ DiagSet.toSSet.map ((faceNerveRight.obj C).endpointsPoint y₀
      y₁)) ≫
      DiagSet.toSSet.map (cond α (grayHomBoundaryFan (faceNerveRight.obj C)).snd
        (grayHomBoundaryFan (faceNerveRight.obj C)).fst) =
        SSet.yonedaEquiv.symm ((faceNerveRight.obj C).vertexEquivSSet (cond α y₁ y₀)) := by
    have e : (faceNerveRight.obj C).endpointsPoint y₀ y₁ ≫
        cond α (grayHomBoundaryFan (faceNerveRight.obj C)).snd
          (grayHomBoundaryFan (faceNerveRight.obj C)).fst =
        isTerminalBallAtomPoint.from _ ≫ vertexHom (cond α y₁ y₀) := by
      cases α
      · exact DiagSet.endpointsPoint_comp_grayHomBoundaryFan_fst y₀ y₁
      · exact DiagSet.endpointsPoint_comp_grayHomBoundaryFan_snd y₀ y₁
    refine (Category.assoc _ _ _).trans ((congrArg (toSSetPoint ≫ ·)
      ((DiagSet.toSSet.map_comp _ _).symm.trans (congrArg DiagSet.toSSet.map e))).trans ?_)
    rw [hT, Category.id_comp]
    exact toSSetPoint_comp_toSSet_map_vertexHom _
  exact BinaryFan.IsLimit.hom_ext ((isLimitMapConeBinaryFanEquiv DiagSet.toSSet _ _)
    (isLimitOfPreserves DiagSet.toSSet (isLimitGrayHomBoundaryFan (faceNerveRight.obj C))))
    ((L false).trans (R false).symm) ((L true).trans (R true).symm)

noncomputable def mappingSpaceToGray
    {c₀ c₁ : ((MarkedPresheaf.forget (D := edgeMarking)).obj C) _⦋0⦌}
    {y₀ y₁ : (faceNerveRight.obj C).Vertex}
    (h₀ : (faceNerveRightComparison.app C).app _ c₀ = (faceNerveRight.obj C).vertexEquivSSet y₀)
    (h₁ : (faceNerveRightComparison.app C).app _ c₁ = (faceNerveRight.obj C).vertexEquivSSet y₁) :
    SSet.mappingSpace ((MarkedPresheaf.forget (D := edgeMarking)).obj C) c₀ c₁ ⟶
      DiagSet.toSSet.obj ((faceNerveRight.obj C).mappingSpace y₀ y₁).toFunctor :=
  (DiagSet.toSSet.map_isPullback ((faceNerveRight.obj C).isPullback_mappingSpace y₀ y₁)).lift
    (pullback.fst _ _ ≫ intervalComparison C) (pullback.snd _ _ ≫ toSSetPoint)
    ((Category.assoc _ _ _).trans ((congrArg (pullback.fst _ _ ≫ ·)
      (pre_app_comp_boundaryComparison C).symm).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ boundaryComparison C) (SSet.mappingSpace_fst_pre c₀ c₁)).trans
          ((Category.assoc _ _ _).trans ((congrArg (pullback.snd _ _ ≫ ·)
            (boundaryPoint_comp_boundaryComparison C h₀ h₁)).trans
              (Category.assoc _ _ _).symm))))))

end Restriction

section Fibres

open SSet.modelCategoryJoyal MarkedSSet.modelCategoryCartesian

private theorem isFibrant_of_isTerminal {T : SSet.{u}} (hT : IsTerminal T) : IsFibrant T :=
  (isFibrant_iff_of_isTerminal (𝟙 T) hT).2 inferInstance

private theorem fibration_pre_boundary_app (Q : SSet.{u}) [Q.Quasicategory] :
    Fibration ((pre (∂Δ[1] : (Δ[1] : SSet.{u}).Subcomplex).ι).app Q) :=
  (SSet.modelCategoryJoyal.fibration_iff_isofibration _).2
    (SSet.isofibration_pre_boundaryOne Q)

theorem fibration_toSSet_map_grayHomRestrict_and_isFibrant {Y : DiagSet.{u}}
    (hY : IsInftyCategory 1 Y) :
    Fibration (DiagSet.toSSet.map ((grayHomRestrict intervalBoundaryι).app Y)) ∧
      IsFibrant (DiagSet.toSSet.obj ((grayHomRight intervalBoundary.{u}).obj Y)) :=
  have := fibration_toInfty_one_grayHomRestrict intervalBoundaryι hY
  ⟨isQuillen_sSetDiagSetAdj.fibration_map
    ((DiagSet.toInfty 1).map ((grayHomRestrict intervalBoundaryι).app Y)),
    isFibrant_toSSet_obj (isInftyCategory_grayHomRight _ hY)⟩

theorem weakEquivalence_toSSet_map_mappingSpaceMap {X Y : DiagSet.{u}} (hX : IsInftyCategory 1 X)
    (hY : IsInftyCategory 1 Y) (f : X ⟶ Y) [WeakEquivalence ((DiagSet.toInfty 1).map f)]
    (x y : X.Vertex) : WeakEquivalence (DiagSet.toSSet.map (X.mappingSpaceMap f x y)) := by
  obtain ⟨_, _⟩ := fibration_toSSet_map_grayHomRestrict_and_isFibrant hX
  obtain ⟨_, _⟩ := fibration_toSSet_map_grayHomRestrict_and_isFibrant hY
  have := isFibrant_of_isTerminal isTerminalToSSetBallAtomPoint.{u}
  have := weakEquivalence_toSSet_map_grayHomRight_map_of_isInftyCategory
    (ball.{u} (atomSimplex 1)) hX hY f
  have := weakEquivalence_toSSet_map_grayHomRight_map_of_isInftyCategory
    intervalBoundary.{u} hX hY f
  exact (DiagSet.toSSet.map_isPullback
      (X.isPullback_mappingSpace x y)).weakEquivalence_map_of_fibration
    (DiagSet.toSSet.map_isPullback (Y.isPullback_mappingSpace (x.map f) (y.map f)))
    (DiagSet.toSSet.map ((grayHomRight (ball.{u} (atomSimplex 1))).map f))
    (DiagSet.toSSet.map ((grayHomRight intervalBoundary.{u}).map f)) (𝟙 _)
    (DiagSet.toSSet.map (X.mappingSpaceMap f x y))
    (by rw [← Functor.map_comp, ← Functor.map_comp, (grayHomRestrict _).naturality])
    (by rw [Category.id_comp, ← Functor.map_comp, DiagSet.endpointsPoint_comp_grayHomRight_map])
    (by rw [← Functor.map_comp, ← Functor.map_comp, DiagSet.mappingSpaceMap_ι])
    (by rw [Category.comp_id, ← Functor.map_comp]
        exact congrArg _ (isTerminalBallAtomPoint.hom_ext _ _))

theorem weakEquivalence_mappingSpaceToGray (C : MarkedSSet.{u}) [IsFibrant C]
    {c₀ c₁ : ((MarkedPresheaf.forget (D := edgeMarking)).obj C) _⦋0⦌}
    {y₀ y₁ : (faceNerveRight.obj C).Vertex}
    (h₀ : (faceNerveRightComparison.app C).app _ c₀ = (faceNerveRight.obj C).vertexEquivSSet y₀)
    (h₁ : (faceNerveRightComparison.app C).app _ c₁ = (faceNerveRight.obj C).vertexEquivSSet y₁) :
    WeakEquivalence (mappingSpaceToGray C h₀ h₁) := by
  have hG : IsInftyCategory 1 (faceNerveRight.obj C) :=
    (isFibrant_infty_iff 1 _).1 (isQuillen_faceNerveAdjunction.isFibrant_obj C)
  have : SSet.Quasicategory ((MarkedPresheaf.forget (D := edgeMarking)).obj C) :=
    (isFibrant_iff_quasicategory _).1
      (Atoms.Homotopical.isQuillenEquivalence_flatForgetAdjunction.toIsQuillen.isFibrant_obj C)
  have := fibration_pre_boundary_app ((MarkedPresheaf.forget (D := edgeMarking)).obj C)
  have : IsFibrant ((ihom (∂Δ[1] : SSet.{u})).obj
      ((MarkedPresheaf.forget (D := edgeMarking)).obj C)) :=
    (isFibrant_iff_quasicategory _).2 inferInstance
  have : IsFibrant (Δ[0] : SSet.{u}) := isFibrant_of_isTerminal SSet.stdSimplex.isTerminalObj₀
  obtain ⟨_, _⟩ := fibration_toSSet_map_grayHomRestrict_and_isFibrant hG
  have := isFibrant_of_isTerminal isTerminalToSSetBallAtomPoint.{u}
  have := weakEquivalence_grayHomSimplicialComparison_app Δ[1] C
  have := weakEquivalence_grayHomSimplicialComparison_app (∂Δ[1] : SSet.{u}) C
  have : WeakEquivalence (intervalComparison C) := by
    dsimp only [intervalComparison]
    infer_instance
  have : WeakEquivalence (boundaryComparison C) := by
    dsimp only [boundaryComparison]
    infer_instance
  have : IsIso (toSSetPoint.{u}) :=
    isIso_of_isTerminal SSet.stdSimplex.isTerminalObj₀ isTerminalToSSetBallAtomPoint _
  exact (SSet.isPullback_mappingSpace_pre _ c₀ c₁).weakEquivalence_map_of_fibration
    (DiagSet.toSSet.map_isPullback ((faceNerveRight.obj C).isPullback_mappingSpace y₀ y₁))
    (intervalComparison C) (boundaryComparison C) toSSetPoint (mappingSpaceToGray C h₀ h₁)
    (pre_app_comp_boundaryComparison C) (boundaryPoint_comp_boundaryComparison C h₀ h₁)
    (IsPullback.lift_fst _ _ _ _) (IsPullback.lift_snd _ _ _ _)

private theorem isFibrant_toSSet_mappingSpace {X : DiagSet.{u}} (hX : IsInftyCategory 1 X)
    (x y : X.Vertex) : IsFibrant (DiagSet.toSSet.obj (X.mappingSpace x y).toFunctor) :=
  have := DiagSet.isFibrant_mappingSpace hX x y
  isQuillen_sSetDiagSetAdj.isFibrant_obj ((DiagSet.toInfty 1).obj (X.mappingSpace x y).toFunctor)

private theorem exists_weakEquivalence_reverse {A B : SSet.{u}} [IsFibrant A] [IsFibrant B]
    (f : A ⟶ B) [WeakEquivalence f] : ∃ g : B ⟶ A, WeakEquivalence g := by
  obtain ⟨g, h₁, h₂⟩ := RightHomotopyClass.whitehead f
  exact ⟨g, weakEquivalence_of_rightHomotopyRel g f h₂ h₁⟩

private theorem isFibrant_mappingSpace (Q : SSet.{u}) [Q.Quasicategory] (a b : Q _⦋0⦌) :
    IsFibrant (SSet.mappingSpace Q a b) :=
  have := SSet.kanComplex_mappingSpace Q a b
  (isFibrant_iff_quasicategory _).2 inferInstance

theorem weakEquivalence_mappingSpaceMap_toSSet_map {X Y : DiagSet.{u}} (hX : IsInftyCategory 1 X)
    (hY : IsInftyCategory 1 Y) (f : X ⟶ Y) [WeakEquivalence ((DiagSet.toInfty 1).map f)]
    (a b : (DiagSet.toSSet.obj X) _⦋0⦌) :
    WeakEquivalence (SSet.mappingSpaceMap (DiagSet.toSSet.map f) a b) := by
  have : IsFibrant ((DiagSet.toInfty 1).obj X) := (isFibrant_infty_iff 1 _).2 hX
  have : IsFibrant ((DiagSet.toInfty 1).obj Y) := (isFibrant_infty_iff 1 _).2 hY
  have : SSet.Quasicategory (DiagSet.toSSet.obj X) :=
    quasicategory_toSSet_obj ((DiagSet.toInfty 1).obj X) inferInstance
  have : SSet.Quasicategory (DiagSet.toSSet.obj Y) :=
    quasicategory_toSSet_obj ((DiagSet.toInfty 1).obj Y) inferInstance
  have : WeakEquivalence (DiagSet.toSSet.map f) :=
    isQuillen_sSetDiagSetAdj.weakEquivalence_map_of_isFibrant ((DiagSet.toInfty 1).map f)
  exact SSet.modelCategoryJoyal.isFullyFaithful_of_weakEquivalence (DiagSet.toSSet.map f) a b

theorem weakEquivalence_mappingSpaceMap_faceNerveRightComparison_app (C : MarkedSSet.{u})
    [IsFibrant C] (c₀ c₁ : ((MarkedPresheaf.forget (D := edgeMarking)).obj C) _⦋0⦌) :
    WeakEquivalence (SSet.mappingSpaceMap (faceNerveRightComparison.app C) c₀ c₁) := by
  have : SSet.Quasicategory ((MarkedPresheaf.forget (D := edgeMarking)).obj C) :=
    (isFibrant_iff_quasicategory _).1
      (Atoms.Homotopical.isQuillenEquivalence_flatForgetAdjunction.toIsQuillen.isFibrant_obj C)
  have := weakEquivalence_faceNerveRightComparison_app C
  have : SSet.Quasicategory ((faceNerveRight ⋙ DiagSet.toSSet).obj C) :=
    quasicategory_toSSet_obj _ ((isFibrant_infty_iff 1 _).2 (isInftyCategory_faceNerveRight_obj C))
  exact SSet.modelCategoryJoyal.isFullyFaithful_of_weakEquivalence
    (faceNerveRightComparison.app C) c₀ c₁

theorem mappingSpaceComparison_exists_joyal {X : DiagSet.{u}} (hX : IsInftyCategory 1 X)
    (x y : X.Vertex) :
    ∃ (Z : SSet.{u}) (l : Z ⟶ DiagSet.toSSet.obj (X.mappingSpace x y).toFunctor)
      (r : Z ⟶ SSet.mappingSpace (DiagSet.toSSet.obj X)
        (X.vertexEquivSSet x) (X.vertexEquivSSet y)),
      Z.KanComplex ∧ WeakEquivalence l ∧ WeakEquivalence r := by
  obtain ⟨C, _, η, _, -⟩ := exists_weakEquivalence_faceNerveRight X
  have hG := isInftyCategory_faceNerveRight_obj C
  have h₀ := faceNerveRightComparison_app_vertexLift C
    ((faceNerveRight.obj C).vertexEquivSSet (x.map η))
  have h₁ := faceNerveRightComparison_app_vertexLift C
    ((faceNerveRight.obj C).vertexEquivSSet (y.map η))
  have := weakEquivalence_toSSet_map_mappingSpaceMap hX hG η x y
  have := weakEquivalence_mappingSpaceMap_toSSet_map hX hG η
    (X.vertexEquivSSet x) (X.vertexEquivSSet y)
  have := isFibrant_toSSet_mappingSpace hX x y
  have := isFibrant_toSSet_mappingSpace hG (x.map η) (y.map η)
  have : SSet.Quasicategory (DiagSet.toSSet.obj X) :=
    quasicategory_toSSet_obj ((DiagSet.toInfty 1).obj X) ((isFibrant_infty_iff 1 _).2 hX)
  have : SSet.Quasicategory (DiagSet.toSSet.obj (faceNerveRight.obj C)) :=
    quasicategory_toSSet_obj ((DiagSet.toInfty 1).obj (faceNerveRight.obj C))
      ((isFibrant_infty_iff 1 _).2 hG)
  have := isFibrant_mappingSpace (DiagSet.toSSet.obj X) (X.vertexEquivSSet x) (X.vertexEquivSSet y)
  have := isFibrant_mappingSpace (DiagSet.toSSet.obj (faceNerveRight.obj C))
    ((DiagSet.toSSet.map η).app _ (X.vertexEquivSSet x))
    ((DiagSet.toSSet.map η).app _ (X.vertexEquivSSet y))
  obtain ⟨g, _⟩ := exists_weakEquivalence_reverse (DiagSet.toSSet.map (X.mappingSpaceMap η x y))
  obtain ⟨g', _⟩ := exists_weakEquivalence_reverse
    (SSet.mappingSpaceMap (DiagSet.toSSet.map η) (X.vertexEquivSSet x) (X.vertexEquivSSet y))
  have := weakEquivalence_mappingSpaceToGray C h₀ h₁
  have := weakEquivalence_mappingSpaceMap_faceNerveRightComparison_app C
    (faceNerveRightVertexLift C ((faceNerveRight.obj C).vertexEquivSSet (x.map η)))
    (faceNerveRightVertexLift C ((faceNerveRight.obj C).vertexEquivSSet (y.map η)))
  have : SSet.Quasicategory ((MarkedPresheaf.forget (D := edgeMarking)).obj C) :=
    (isFibrant_iff_quasicategory _).1
      (Atoms.Homotopical.isQuillenEquivalence_flatForgetAdjunction.toIsQuillen.isFibrant_obj C)
  exact ⟨_, mappingSpaceToGray C h₀ h₁ ≫ g,
    SSet.mappingSpaceMap (faceNerveRightComparison.app C) _ _ ≫
      eqToHom (by rw [h₀, h₁]; rfl) ≫ g',
    SSet.kanComplex_mappingSpace _ _ _, inferInstance, inferInstance⟩

end Fibres

theorem kanComplex_toSSet_mappingSpace {X : DiagSet.{u}} (hX : IsInftyCategory 1 X)
    (x y : X.Vertex) : (DiagSet.toSSet.obj (X.mappingSpace x y).toFunctor).KanComplex :=
  kanComplex_toSSet_obj (X.isInftyCategory_zero_mappingSpace hX x y)

theorem kanComplex_mappingSpace_toSSet_obj {X : DiagSet.{u}} (hX : IsInftyCategory 1 X)
    (x y : X.Vertex) :
    (SSet.mappingSpace (DiagSet.toSSet.obj X) (X.vertexEquivSSet x)
      (X.vertexEquivSSet y)).KanComplex :=
  have : (DiagSet.toSSet.obj X).Quasicategory :=
    (SSet.modelCategoryJoyal.isFibrant_iff_quasicategory _).1 (isFibrant_toSSet_obj hX)
  SSet.kanComplex_mappingSpace _ _ _

open SSet.modelCategoryQuillen in
theorem mappingSpaceComparison_exists {X : DiagSet.{u}} (hX : IsInftyCategory 1 X)
    (x y : X.Vertex) :
    ∃ (Z : SSet.{u}) (l : Z ⟶ DiagSet.toSSet.obj (X.mappingSpace x y).toFunctor)
      (r : Z ⟶ SSet.mappingSpace (DiagSet.toSSet.obj X)
        (X.vertexEquivSSet x) (X.vertexEquivSSet y)),
      WeakEquivalence l ∧ WeakEquivalence r := by
  obtain ⟨Z, l, r, -, hl, hr⟩ := mappingSpaceComparison_exists_joyal hX x y
  exact ⟨Z, l, r, ⟨joyal_weakEquivalences_le_kanWeak _ hl.mem⟩,
    ⟨joyal_weakEquivalences_le_kanWeak _ hr.mem⟩⟩

section Naturality

open SSet.modelCategoryJoyal MarkedSSet.modelCategoryCartesian

@[reassoc]
theorem intervalComparison_naturality {C C' : MarkedSSet.{u}} (c : C ⟶ C') :
    intervalComparison C ≫ DiagSet.toSSet.map
        ((grayHomRight (ball.{u} (atomSimplex 1))).map (faceNerveRight.map c)) =
      (ihom Δ[1]).map ((MarkedPresheaf.forget (D := edgeMarking)).map c) ≫
        intervalComparison C' := by
  have h : (grayHomSimplicialComparison Δ[1]).app C ≫ DiagSet.toSSet.map
      ((grayHomRight (SSet.toDiagSet.obj Δ[1])).map (faceNerveRight.map c)) =
      (ihom Δ[1]).map ((MarkedPresheaf.forget (D := edgeMarking)).map c) ≫
        (grayHomSimplicialComparison Δ[1]).app C' :=
    ((grayHomSimplicialComparison Δ[1]).naturality c).symm
  rw [intervalComparison, intervalComparison, Category.assoc, ← Functor.map_comp,
    ← (grayHomRestrict _).naturality, Functor.map_comp, reassoc_of% h]

@[reassoc]
theorem mappingSpaceToGray_ι (C : MarkedSSet.{u})
    {c₀ c₁ : ((MarkedPresheaf.forget (D := edgeMarking)).obj C) _⦋0⦌}
    {y₀ y₁ : (faceNerveRight.obj C).Vertex}
    (h₀ : (faceNerveRightComparison.app C).app _ c₀ = (faceNerveRight.obj C).vertexEquivSSet y₀)
    (h₁ : (faceNerveRightComparison.app C).app _ c₁ = (faceNerveRight.obj C).vertexEquivSSet y₁) :
    mappingSpaceToGray C h₀ h₁ ≫ DiagSet.toSSet.map ((faceNerveRight.obj C).mappingSpace y₀ y₁).ι =
      pullback.fst _ _ ≫ intervalComparison C :=
  IsPullback.lift_fst _ _ _ _

private noncomputable def toSSetMappingSpaceMap {Y Z : DiagSet.{u}} (g : Y ⟶ Z) {p q : Y.Vertex}
    {p' q' : Z.Vertex} (hp : p.map g = p') (hq : q.map g = q') :
    DiagSet.toSSet.obj (Y.mappingSpace p q).toFunctor ⟶
      DiagSet.toSSet.obj (Z.mappingSpace p' q').toFunctor :=
  DiagSet.toSSet.map (Y.mappingSpaceMap g p q) ≫ eqToHom (by rw [hp, hq])

@[reassoc]
private theorem toSSetMappingSpaceMap_ι {Y Z : DiagSet.{u}} (g : Y ⟶ Z) {p q : Y.Vertex}
    {p' q' : Z.Vertex} (hp : p.map g = p') (hq : q.map g = q') :
    toSSetMappingSpaceMap g hp hq ≫ DiagSet.toSSet.map (Z.mappingSpace p' q').ι =
      DiagSet.toSSet.map ((Y.mappingSpace p q).ι ≫
        (grayHomRight (ball.{u} (atomSimplex 1))).map g) := by
  subst hp hq
  rw [toSSetMappingSpaceMap, eqToHom_refl, Category.comp_id, ← Functor.map_comp,
    DiagSet.mappingSpaceMap_ι]

private theorem weakEquivalence_mappingSpaceMapOfEq (C : MarkedSSet.{u}) [IsFibrant C]
    {c₀ c₁ : ((MarkedPresheaf.forget (D := edgeMarking)).obj C) _⦋0⦌}
    {a b : (DiagSet.toSSet.obj (faceNerveRight.obj C)) _⦋0⦌}
    (h₀ : (faceNerveRightComparison.app C).app _ c₀ = a)
    (h₁ : (faceNerveRightComparison.app C).app _ c₁ = b) :
    WeakEquivalence (SSet.mappingSpaceMapOfEq (faceNerveRightComparison.app C) h₀ h₁) := by
  have := weakEquivalence_mappingSpaceMap_faceNerveRightComparison_app C c₀ c₁
  dsimp only [SSet.mappingSpaceMapOfEq]
  infer_instance

theorem faceNerveRightComparison_app_forget_map_app {X Y : DiagSet.{u}} {C C' : MarkedSSet.{u}}
    {η : X ⟶ faceNerveRight.obj C} {η' : Y ⟶ faceNerveRight.obj C'} {f : X ⟶ Y} {c : C ⟶ C'}
    (h : η ≫ faceNerveRight.map c = f ≫ η') {x : X.Vertex}
    {c₀ : ((MarkedPresheaf.forget (D := edgeMarking)).obj C) _⦋0⦌}
    (h₀ : (faceNerveRightComparison.app C).app _ c₀ =
      (faceNerveRight.obj C).vertexEquivSSet (x.map η)) :
    (faceNerveRightComparison.app C').app _
        (((MarkedPresheaf.forget (D := edgeMarking)).map c).app _ c₀) =
      (faceNerveRight.obj C').vertexEquivSSet ((x.map f).map η') :=
  ((congrArg (fun φ => φ.app (op ⦋0⦌) c₀) (faceNerveRightComparison.naturality c)).trans
    (congrArg ((DiagSet.toSSet.map (faceNerveRight.map c)).app _) h₀)).trans
    (congrArg (fun φ => (faceNerveRight.obj C').vertexEquivSSet (x.map φ)) h)

variable {H : Type*} [Category* H] (W : MorphismProperty SSet.{u})
  (hW : weakEquivalences SSet.{u} ≤ W) (L : SSet.{u} ⥤ H) [L.IsLocalization W]

private noncomputable def mappingSpaceIsoOfLift {X : DiagSet.{u}} (hX : IsInftyCategory 1 X)
    {C : MarkedSSet.{u}} [IsFibrant C] (η : X ⟶ faceNerveRight.obj C)
    [WeakEquivalence ((DiagSet.toInfty 1).map η)] (x y : X.Vertex)
    {c₀ c₁ : ((MarkedPresheaf.forget (D := edgeMarking)).obj C) _⦋0⦌}
    (h₀ : (faceNerveRightComparison.app C).app _ c₀ =
      (faceNerveRight.obj C).vertexEquivSSet (x.map η))
    (h₁ : (faceNerveRightComparison.app C).app _ c₁ =
      (faceNerveRight.obj C).vertexEquivSSet (y.map η)) :
    L.obj (DiagSet.toSSet.obj (X.mappingSpace x y).toFunctor) ≅
      L.obj (SSet.mappingSpace (DiagSet.toSSet.obj X) (X.vertexEquivSSet x)
        (X.vertexEquivSSet y)) :=
  Localization.isoOfHom L W (DiagSet.toSSet.map (X.mappingSpaceMap η x y))
      (hW _ (weakEquivalence_toSSet_map_mappingSpaceMap hX
        (isInftyCategory_faceNerveRight_obj C) η x y).mem) ≪≫
    (Localization.isoOfHom L W (mappingSpaceToGray C h₀ h₁)
      (hW _ (weakEquivalence_mappingSpaceToGray C h₀ h₁).mem)).symm ≪≫
    Localization.isoOfHom L W (SSet.mappingSpaceMapOfEq (faceNerveRightComparison.app C)
        (a' := (DiagSet.toSSet.map η).app _ (X.vertexEquivSSet x))
        (b' := (DiagSet.toSSet.map η).app _ (X.vertexEquivSSet y)) h₀ h₁)
      (hW _ (weakEquivalence_mappingSpaceMapOfEq C _ _).mem) ≪≫
    (Localization.isoOfHom L W
      (SSet.mappingSpaceMap (DiagSet.toSSet.map η) (X.vertexEquivSSet x) (X.vertexEquivSSet y))
      (hW _ (weakEquivalence_mappingSpaceMap_toSSet_map hX
        (isInftyCategory_faceNerveRight_obj C) η _ _).mem)).symm

private theorem mappingSpaceIsoOfLift_congr {X : DiagSet.{u}} (hX : IsInftyCategory 1 X)
    {C : MarkedSSet.{u}} [IsFibrant C] (η : X ⟶ faceNerveRight.obj C)
    [WeakEquivalence ((DiagSet.toInfty 1).map η)] (x y : X.Vertex)
    {c₀ c₁ c₀' c₁' : ((MarkedPresheaf.forget (D := edgeMarking)).obj C) _⦋0⦌}
    (e₀ : c₀ = c₀') (e₁ : c₁ = c₁')
    (h₀ : (faceNerveRightComparison.app C).app _ c₀ =
      (faceNerveRight.obj C).vertexEquivSSet (x.map η))
    (h₁ : (faceNerveRightComparison.app C).app _ c₁ =
      (faceNerveRight.obj C).vertexEquivSSet (y.map η))
    (h₀' : (faceNerveRightComparison.app C).app _ c₀' =
      (faceNerveRight.obj C).vertexEquivSSet (x.map η))
    (h₁' : (faceNerveRightComparison.app C).app _ c₁' =
      (faceNerveRight.obj C).vertexEquivSSet (y.map η)) :
    mappingSpaceIsoOfLift W hW L hX η x y h₀ h₁ =
      mappingSpaceIsoOfLift W hW L hX η x y h₀' h₁' := by
  subst e₀ e₁
  rfl

private theorem comparisonMappingSpaceMap_square {X Y : DiagSet.{u}}
    {C C' : MarkedSSet.{u}} (η : X ⟶ faceNerveRight.obj C)
    (η' : Y ⟶ faceNerveRight.obj C')
    (f : X ⟶ Y) (c : C ⟶ C') (h : η ≫ faceNerveRight.map c = f ≫ η') (x y : X.Vertex)
    {c₀ c₁ : ((MarkedPresheaf.forget (D := edgeMarking)).obj C) _⦋0⦌}
    (h₀ : (faceNerveRightComparison.app C).app _ c₀ =
      (faceNerveRight.obj C).vertexEquivSSet (x.map η))
    (h₁ : (faceNerveRightComparison.app C).app _ c₁ =
      (faceNerveRight.obj C).vertexEquivSSet (y.map η))
    (ha : (DiagSet.toSSet.map (faceNerveRight.map c)).app _
      ((DiagSet.toSSet.map η).app _ (X.vertexEquivSSet x)) =
        (DiagSet.toSSet.map η').app _ (Y.vertexEquivSSet (x.map f)))
    (hb : (DiagSet.toSSet.map (faceNerveRight.map c)).app _
      ((DiagSet.toSSet.map η).app _ (X.vertexEquivSSet y)) =
        (DiagSet.toSSet.map η').app _ (Y.vertexEquivSSet (y.map f)))
    : SSet.mappingSpaceMapOfEq (faceNerveRightComparison.app C)
        (a' := (DiagSet.toSSet.map η).app _ (X.vertexEquivSSet x))
        (b' := (DiagSet.toSSet.map η).app _ (X.vertexEquivSSet y)) h₀ h₁ ≫
        SSet.mappingSpaceMapOfEq (DiagSet.toSSet.map (faceNerveRight.map c)) ha hb =
      SSet.mappingSpaceMap ((MarkedPresheaf.forget (D := edgeMarking)).map c) c₀ c₁ ≫
        SSet.mappingSpaceMapOfEq (faceNerveRightComparison.app C')
          (a' := (DiagSet.toSSet.map η').app _ (Y.vertexEquivSSet (x.map f)))
          (b' := (DiagSet.toSSet.map η').app _ (Y.vertexEquivSSet (y.map f)))
          (faceNerveRightComparison_app_forget_map_app h h₀)
          (faceNerveRightComparison_app_forget_map_app h h₁) := by
  have h₀' := faceNerveRightComparison_app_forget_map_app h h₀
  have h₁' := faceNerveRightComparison_app_forget_map_app h h₁
  refine SSet.mappingSpace_hom_ext ?_
  exact ((CommSq.mk (SSet.mappingSpaceMapOfEq_fst _ h₀ h₁)).horiz_comp
    (CommSq.mk (SSet.mappingSpaceMapOfEq_fst _ ha hb))).w.trans
    ((congrArg (pullback.fst _ _ ≫ ·) (((ihom Δ[1]).map_comp _ _).symm.trans
      ((congrArg (ihom Δ[1]).map (faceNerveRightComparison.naturality c).symm).trans
        ((ihom Δ[1]).map_comp _ _)))).trans
      ((CommSq.mk (SSet.mappingSpaceMap_fst _ c₀ c₁)).horiz_comp
        (CommSq.mk (SSet.mappingSpaceMapOfEq_fst _ h₀' h₁'))).w.symm)

private theorem restrictionMappingSpaceMap_square {X Y : DiagSet.{u}}
    {C C' : MarkedSSet.{u}} (η : X ⟶ faceNerveRight.obj C)
    (η' : Y ⟶ faceNerveRight.obj C')
    (f : X ⟶ Y) (c : C ⟶ C') (h : η ≫ faceNerveRight.map c = f ≫ η') (x y : X.Vertex)
    (ha : (DiagSet.toSSet.map (faceNerveRight.map c)).app _
      ((DiagSet.toSSet.map η).app _ (X.vertexEquivSSet x)) =
        (DiagSet.toSSet.map η').app _ (Y.vertexEquivSSet (x.map f)))
    (hb : (DiagSet.toSSet.map (faceNerveRight.map c)).app _
      ((DiagSet.toSSet.map η).app _ (X.vertexEquivSSet y)) =
        (DiagSet.toSSet.map η').app _ (Y.vertexEquivSSet (y.map f)))
    : SSet.mappingSpaceMap (DiagSet.toSSet.map η) (X.vertexEquivSSet x)
        (X.vertexEquivSSet y) ≫
        SSet.mappingSpaceMapOfEq (DiagSet.toSSet.map (faceNerveRight.map c)) ha hb =
      SSet.mappingSpaceMap (DiagSet.toSSet.map f) (X.vertexEquivSSet x) (X.vertexEquivSSet y) ≫
        SSet.mappingSpaceMap (DiagSet.toSSet.map η') (Y.vertexEquivSSet (x.map f))
          (Y.vertexEquivSSet (y.map f)) := by
  refine SSet.mappingSpace_hom_ext ?_
  exact ((CommSq.mk (SSet.mappingSpaceMap_fst _ _ _)).horiz_comp
    (CommSq.mk (SSet.mappingSpaceMapOfEq_fst _ ha hb))).w.trans
    ((congrArg (pullback.fst _ _ ≫ ·) (((ihom Δ[1]).map_comp _ _).symm.trans
      ((congrArg (ihom Δ[1]).map ((DiagSet.toSSet.map_comp _ _).symm.trans
        ((congrArg DiagSet.toSSet.map h).trans (DiagSet.toSSet.map_comp _ _)))).trans
        ((ihom Δ[1]).map_comp _ _)))).trans
      ((CommSq.mk (SSet.mappingSpaceMap_fst _ _ _)).horiz_comp
        (CommSq.mk (SSet.mappingSpaceMap_fst _ _ _))).w.symm)

private theorem toSSetMappingSpaceMap_square {X Y : DiagSet.{u}} {C C' : MarkedSSet.{u}}
    (η : X ⟶ faceNerveRight.obj C) (η' : Y ⟶ faceNerveRight.obj C') (f : X ⟶ Y) (c : C ⟶ C')
    (h : η ≫ faceNerveRight.map c = f ≫ η') (x y : X.Vertex)
    (hp : (x.map η).map (faceNerveRight.map c) = (x.map f).map η')
    (hq : (y.map η).map (faceNerveRight.map c) = (y.map f).map η') :
    DiagSet.toSSet.map (X.mappingSpaceMap η x y) ≫
        toSSetMappingSpaceMap (faceNerveRight.map c) hp hq =
      DiagSet.toSSet.map (X.mappingSpaceMap f x y) ≫
        DiagSet.toSSet.map (Y.mappingSpaceMap η' (x.map f) (y.map f)) := by
  refine (cancel_mono (DiagSet.toSSet.map
    ((faceNerveRight.obj C').mappingSpace ((x.map f).map η') ((y.map f).map η')).ι)).1 ?_
  simp only [Category.assoc, toSSetMappingSpaceMap_ι, ← Functor.map_comp,
    DiagSet.mappingSpaceMap_ι, DiagSet.mappingSpaceMap_ι_assoc, h]

private theorem mappingSpaceToGray_square {X Y : DiagSet.{u}} {C C' : MarkedSSet.{u}}
    (η : X ⟶ faceNerveRight.obj C) (η' : Y ⟶ faceNerveRight.obj C') (f : X ⟶ Y) (c : C ⟶ C')
    (h : η ≫ faceNerveRight.map c = f ≫ η') (x y : X.Vertex)
    (hp : (x.map η).map (faceNerveRight.map c) = (x.map f).map η')
    (hq : (y.map η).map (faceNerveRight.map c) = (y.map f).map η')
    {c₀ c₁ : ((MarkedPresheaf.forget (D := edgeMarking)).obj C) _⦋0⦌}
    (h₀ : (faceNerveRightComparison.app C).app _ c₀ =
      (faceNerveRight.obj C).vertexEquivSSet (x.map η))
    (h₁ : (faceNerveRightComparison.app C).app _ c₁ =
      (faceNerveRight.obj C).vertexEquivSSet (y.map η)) :
    mappingSpaceToGray C h₀ h₁ ≫ toSSetMappingSpaceMap (faceNerveRight.map c) hp hq =
      SSet.mappingSpaceMap ((MarkedPresheaf.forget (D := edgeMarking)).map c) c₀ c₁ ≫
        mappingSpaceToGray C' (faceNerveRightComparison_app_forget_map_app h h₀)
          (faceNerveRightComparison_app_forget_map_app h h₁) := by
  have h₀' := faceNerveRightComparison_app_forget_map_app h h₀
  have h₁' := faceNerveRightComparison_app_forget_map_app h h₁
  refine (cancel_mono (DiagSet.toSSet.map
    ((faceNerveRight.obj C').mappingSpace ((x.map f).map η') ((y.map f).map η')).ι)).1 ?_
  exact ((CommSq.mk (mappingSpaceToGray_ι C h₀ h₁)).horiz_comp (CommSq.mk
    ((toSSetMappingSpaceMap_ι _ hp hq).trans (Functor.map_comp _ _ _)))).w.trans
    ((congrArg (pullback.fst _ _ ≫ ·) (intervalComparison_naturality c)).trans
      ((CommSq.mk (SSet.mappingSpaceMap_fst _ c₀ c₁)).horiz_comp
        (CommSq.mk (mappingSpaceToGray_ι C' h₀' h₁'))).w.symm)

private theorem mappingSpaceIsoOfLift_hom_naturality {X Y : DiagSet.{u}}
    (hX : IsInftyCategory 1 X) (hY : IsInftyCategory 1 Y) {C C' : MarkedSSet.{u}} [IsFibrant C]
    [IsFibrant C'] (η : X ⟶ faceNerveRight.obj C) [WeakEquivalence ((DiagSet.toInfty 1).map η)]
    (η' : Y ⟶ faceNerveRight.obj C') [WeakEquivalence ((DiagSet.toInfty 1).map η')]
    (f : X ⟶ Y) (c : C ⟶ C') (h : η ≫ faceNerveRight.map c = f ≫ η') (x y : X.Vertex)
    {c₀ c₁ : ((MarkedPresheaf.forget (D := edgeMarking)).obj C) _⦋0⦌}
    (h₀ : (faceNerveRightComparison.app C).app _ c₀ =
      (faceNerveRight.obj C).vertexEquivSSet (x.map η))
    (h₁ : (faceNerveRightComparison.app C).app _ c₁ =
      (faceNerveRight.obj C).vertexEquivSSet (y.map η)) :
    L.map (DiagSet.toSSet.map (X.mappingSpaceMap f x y)) ≫
        (mappingSpaceIsoOfLift W hW L hY η' (x.map f) (y.map f)
          (faceNerveRightComparison_app_forget_map_app h h₀)
          (faceNerveRightComparison_app_forget_map_app h h₁)).hom =
      (mappingSpaceIsoOfLift W hW L hX η x y h₀ h₁).hom ≫
        L.map (SSet.mappingSpaceMap (DiagSet.toSSet.map f) _ _) := by
  have hp : (x.map η).map (faceNerveRight.map c) = (x.map f).map η' := congrArg x.map h
  have hq : (y.map η).map (faceNerveRight.map c) = (y.map f).map η' := congrArg y.map h
  have ha : (DiagSet.toSSet.map (faceNerveRight.map c)).app _
      ((DiagSet.toSSet.map η).app _ (X.vertexEquivSSet x)) =
        (DiagSet.toSSet.map η').app _ (Y.vertexEquivSSet (x.map f)) :=
    congrArg (fun φ => (faceNerveRight.obj C').vertexEquivSSet (x.map φ)) h
  have hb : (DiagSet.toSSet.map (faceNerveRight.map c)).app _
      ((DiagSet.toSSet.map η).app _ (X.vertexEquivSSet y)) =
        (DiagSet.toSSet.map η').app _ (Y.vertexEquivSSet (y.map f)) :=
    congrArg (fun φ => (faceNerveRight.obj C').vertexEquivSSet (y.map φ)) h
  have h₀' := faceNerveRightComparison_app_forget_map_app h h₀
  have h₁' := faceNerveRightComparison_app_forget_map_app h h₁
  have s₁ := toSSetMappingSpaceMap_square η η' f c h x y hp hq
  have s₂ := mappingSpaceToGray_square η η' f c h x y hp hq h₀ h₁
  have s₃ := comparisonMappingSpaceMap_square η η' f c h x y h₀ h₁ ha hb
  have s₄ := restrictionMappingSpaceMap_square η η' f c h x y ha hb
  dsimp only [mappingSpaceIsoOfLift, Iso.trans_hom, Iso.symm_hom]
  simp only [Localization.isoOfHom_hom, Category.assoc]
  rw [← L.map_comp_assoc, ← s₁, L.map_comp_assoc,
    Localization.map_comp_isoOfHom_inv_assoc L _ _ _ _ _ _ _ s₂, ← L.map_comp_assoc, ← s₃,
    L.map_comp_assoc]
  exact congrArg (_ ≫ _ ≫ _ ≫ ·) (Localization.map_comp_isoOfHom_inv L _ _ _ _ _ _ _ s₄)

theorem weakEquivalence_toSSet_map_mappingSpaceMap_iff {X Y : DiagSet.{u}}
    (hX : IsInftyCategory 1 X) (hY : IsInftyCategory 1 Y) (f : X ⟶ Y) (x y : X.Vertex) :
    WeakEquivalence (DiagSet.toSSet.map (X.mappingSpaceMap f x y)) ↔
      WeakEquivalence (SSet.mappingSpaceMap (DiagSet.toSSet.map f) (X.vertexEquivSSet x)
        (X.vertexEquivSSet y)) := by
  obtain ⟨C, _, η, _, hη⟩ := exists_weakEquivalence_faceNerveRight X
  obtain ⟨C', _, η', _, -⟩ := exists_weakEquivalence_faceNerveRight Y
  obtain ⟨c, h⟩ := hη C' (f ≫ η')
  have h₀ := faceNerveRightComparison_app_vertexLift C
    ((faceNerveRight.obj C).vertexEquivSSet (x.map η))
  have h₁ := faceNerveRightComparison_app_vertexLift C
    ((faceNerveRight.obj C).vertexEquivSSet (y.map η))
  have hp : (x.map η).map (faceNerveRight.map c) = (x.map f).map η' := congrArg x.map h
  have hq : (y.map η).map (faceNerveRight.map c) = (y.map f).map η' := congrArg y.map h
  have ha : (DiagSet.toSSet.map (faceNerveRight.map c)).app _
      ((DiagSet.toSSet.map η).app _ (X.vertexEquivSSet x)) =
        (DiagSet.toSSet.map η').app _ (Y.vertexEquivSSet (x.map f)) :=
    congrArg (fun φ => (faceNerveRight.obj C').vertexEquivSSet (x.map φ)) h
  have hb : (DiagSet.toSSet.map (faceNerveRight.map c)).app _
      ((DiagSet.toSSet.map η).app _ (X.vertexEquivSSet y)) =
        (DiagSet.toSSet.map η').app _ (Y.vertexEquivSSet (y.map f)) :=
    congrArg (fun φ => (faceNerveRight.obj C').vertexEquivSSet (y.map φ)) h
  have h₀' := faceNerveRightComparison_app_forget_map_app h h₀
  have h₁' := faceNerveRightComparison_app_forget_map_app h h₁
  have s₁ := toSSetMappingSpaceMap_square η η' f c h x y hp hq
  have s₂ := mappingSpaceToGray_square η η' f c h x y hp hq h₀ h₁
  have s₃ := comparisonMappingSpaceMap_square η η' f c h x y h₀ h₁ ha hb
  have s₄ := restrictionMappingSpaceMap_square η η' f c h x y ha hb
  have w₁ := weakEquivalence_toSSet_map_mappingSpaceMap hX
    (isInftyCategory_faceNerveRight_obj C) η x y
  have w₁' := weakEquivalence_toSSet_map_mappingSpaceMap hY
    (isInftyCategory_faceNerveRight_obj C') η' (x.map f) (y.map f)
  have w₂ := weakEquivalence_mappingSpaceToGray C h₀ h₁
  have w₂' := weakEquivalence_mappingSpaceToGray C' h₀' h₁'
  have w₃ := weakEquivalence_mappingSpaceMapOfEq C
    (a := (DiagSet.toSSet.map η).app _ (X.vertexEquivSSet x))
    (b := (DiagSet.toSSet.map η).app _ (X.vertexEquivSSet y)) h₀ h₁
  have w₃' := weakEquivalence_mappingSpaceMapOfEq C'
    (a := (DiagSet.toSSet.map η').app _ (Y.vertexEquivSSet (x.map f)))
    (b := (DiagSet.toSSet.map η').app _ (Y.vertexEquivSSet (y.map f))) h₀' h₁'
  have w₄ := weakEquivalence_mappingSpaceMap_toSSet_map hX
    (isInftyCategory_faceNerveRight_obj C) η (X.vertexEquivSSet x) (X.vertexEquivSSet y)
  have w₄' := weakEquivalence_mappingSpaceMap_toSSet_map hY
    (isInftyCategory_faceNerveRight_obj C') η' (Y.vertexEquivSSet (x.map f))
    (Y.vertexEquivSSet (y.map f))
  exact (weakEquivalence_postcomp_iff _ _).symm.trans <|
    (iff_of_eq (congrArg (WeakEquivalence ·) s₁.symm)).trans <|
    (weakEquivalence_precomp_iff _ _).trans <|
    (weakEquivalence_precomp_iff (mappingSpaceToGray C h₀ h₁) _).symm.trans <|
    (iff_of_eq (congrArg (WeakEquivalence ·) s₂)).trans <|
    (weakEquivalence_postcomp_iff _ _).trans <|
    (weakEquivalence_postcomp_iff _ (SSet.mappingSpaceMapOfEq (faceNerveRightComparison.app C')
      (a' := (DiagSet.toSSet.map η').app _ (Y.vertexEquivSSet (x.map f)))
      (b' := (DiagSet.toSSet.map η').app _ (Y.vertexEquivSSet (y.map f))) h₀' h₁')).symm.trans <|
    (iff_of_eq (congrArg (WeakEquivalence ·) s₃.symm)).trans <|
    (weakEquivalence_precomp_iff _ _).trans <|
    (weakEquivalence_precomp_iff (SSet.mappingSpaceMap (DiagSet.toSSet.map η)
      (X.vertexEquivSSet x) (X.vertexEquivSSet y)) _).symm.trans <|
    (iff_of_eq (congrArg (WeakEquivalence ·) s₄)).trans <|
    (weakEquivalence_iff _).trans <|
    ((weakEquivalences SSet.{u}).postcomp_iff _ _ w₄'.mem).trans (weakEquivalence_iff _).symm

noncomputable def mappingSpaceIso {X : DiagSet.{u}} (hX : IsInftyCategory 1 X)
    {C : MarkedSSet.{u}} [IsFibrant C] (η : X ⟶ faceNerveRight.obj C)
    [WeakEquivalence ((DiagSet.toInfty 1).map η)] (x y : X.Vertex) :
    L.obj (DiagSet.toSSet.obj (X.mappingSpace x y).toFunctor) ≅
      L.obj (SSet.mappingSpace (DiagSet.toSSet.obj X) (X.vertexEquivSSet x)
        (X.vertexEquivSSet y)) :=
  mappingSpaceIsoOfLift W hW L hX η x y (faceNerveRightComparison_app_vertexLift C _)
    (faceNerveRightComparison_app_vertexLift C _)

theorem mappingSpaceIso_hom_naturality_of_comp_eq {X Y : DiagSet.{u}}
    (hX : IsInftyCategory 1 X) (hY : IsInftyCategory 1 Y) {C C' : MarkedSSet.{u}} [IsFibrant C]
    [IsFibrant C'] (η : X ⟶ faceNerveRight.obj C) [WeakEquivalence ((DiagSet.toInfty 1).map η)]
    (η' : Y ⟶ faceNerveRight.obj C') [WeakEquivalence ((DiagSet.toInfty 1).map η')]
    (f : X ⟶ Y) (c : C ⟶ C') (h : η ≫ faceNerveRight.map c = f ≫ η') (x y : X.Vertex) :
    L.map (DiagSet.toSSet.map (X.mappingSpaceMap f x y)) ≫
        (mappingSpaceIso W hW L hY η' (x.map f) (y.map f)).hom =
      (mappingSpaceIso W hW L hX η x y).hom ≫
        L.map (SSet.mappingSpaceMap (DiagSet.toSSet.map f) _ _) := by
  have e (z : X.Vertex) :
      ((MarkedPresheaf.forget (D := edgeMarking)).map c).app _
          (faceNerveRightVertexLift C ((faceNerveRight.obj C).vertexEquivSSet (z.map η))) =
        faceNerveRightVertexLift C' ((faceNerveRight.obj C').vertexEquivSSet ((z.map f).map η')) :=
    have hz : (DiagSet.toSSet.map (faceNerveRight.map c)).app _
        ((faceNerveRight.obj C).vertexEquivSSet (z.map η)) =
          (faceNerveRight.obj C').vertexEquivSSet ((z.map f).map η') :=
      congrArg (fun φ => (faceNerveRight.obj C').vertexEquivSSet (z.map φ)) h
    (forget_map_app_faceNerveRightVertexLift c _).trans (congrArg (faceNerveRightVertexLift C') hz)
  have hn := mappingSpaceIsoOfLift_hom_naturality W hW L hX hY η η' f c h x y
    (faceNerveRightComparison_app_vertexLift C _) (faceNerveRightComparison_app_vertexLift C _)
  rwa [mappingSpaceIsoOfLift_congr W hW L hY η' (x.map f) (y.map f) (e x) (e y) _ _
    (faceNerveRightComparison_app_vertexLift C' _)
    (faceNerveRightComparison_app_vertexLift C' _)] at hn

theorem mappingSpaceIso_eq {X : DiagSet.{u}} (hX : IsInftyCategory 1 X) {C C' : MarkedSSet.{u}}
    [IsFibrant C] [IsFibrant C'] (η : X ⟶ faceNerveRight.obj C)
    [WeakEquivalence ((DiagSet.toInfty 1).map η)] (η' : X ⟶ faceNerveRight.obj C')
    [WeakEquivalence ((DiagSet.toInfty 1).map η')] (x y : X.Vertex) :
    mappingSpaceIso W hW L hX η x y = mappingSpaceIso W hW L hX η' x y := by
  obtain ⟨C₀, _, η₀, _, hη₀⟩ := exists_weakEquivalence_faceNerveRight X
  have key (C₁ : MarkedSSet.{u}) [IsFibrant C₁] (η₁ : X ⟶ faceNerveRight.obj C₁)
      [WeakEquivalence ((DiagSet.toInfty 1).map η₁)] :
      mappingSpaceIso W hW L hX η₀ x y = mappingSpaceIso W hW L hX η₁ x y := by
    obtain ⟨c, hc⟩ := hη₀ C₁ η₁
    refine Iso.ext ?_
    have h := mappingSpaceIso_hom_naturality_of_comp_eq W hW L hX hX η₀ η₁ (𝟙 X) c
      (hc.trans (Category.id_comp η₁).symm) x y
    have h₁ : L.map (DiagSet.toSSet.map (X.mappingSpaceMap (𝟙 X) x y)) = 𝟙 _ :=
      (congrArg (fun t => L.map (DiagSet.toSSet.map t)) (DiagSet.mappingSpaceMap_id x y)).trans
        ((congrArg L.map (DiagSet.toSSet.map_id _)).trans (L.map_id _))
    have h₂ : L.map (SSet.mappingSpaceMap (DiagSet.toSSet.map (𝟙 X)) (X.vertexEquivSSet x)
        (X.vertexEquivSSet y)) = 𝟙 _ :=
      (congrArg L.map (SSet.mappingSpaceMap_id _ _ _)).trans (L.map_id _)
    rw [h₁, h₂] at h
    exact (Category.comp_id _).symm.trans (h.symm.trans (Category.id_comp _))
  exact (key C η).symm.trans (key C' η')

theorem mappingSpaceIso_hom_naturality {X Y : DiagSet.{u}} (hX : IsInftyCategory 1 X)
    (hY : IsInftyCategory 1 Y) {C C' : MarkedSSet.{u}} [IsFibrant C] [IsFibrant C']
    (η : X ⟶ faceNerveRight.obj C) [WeakEquivalence ((DiagSet.toInfty 1).map η)]
    (η' : Y ⟶ faceNerveRight.obj C') [WeakEquivalence ((DiagSet.toInfty 1).map η')]
    (f : X ⟶ Y) (x y : X.Vertex) :
    L.map (DiagSet.toSSet.map (X.mappingSpaceMap f x y)) ≫
        (mappingSpaceIso W hW L hY η' (x.map f) (y.map f)).hom =
      (mappingSpaceIso W hW L hX η x y).hom ≫
        L.map (SSet.mappingSpaceMap (DiagSet.toSSet.map f) _ _) := by
  obtain ⟨C₀, _, η₀, _, hη₀⟩ := exists_weakEquivalence_faceNerveRight X
  obtain ⟨c, hc⟩ := hη₀ C' (f ≫ η')
  rw [mappingSpaceIso_eq W hW L hX η η₀]
  exact mappingSpaceIso_hom_naturality_of_comp_eq W hW L hX hY η₀ η' f c hc x y

end Naturality

end Atoms.Diagrammatic
