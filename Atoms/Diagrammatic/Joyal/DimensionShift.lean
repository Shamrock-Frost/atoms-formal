import Atoms.Diagrammatic.Joyal.MarkedGrayTensorModel
import Atoms.Diagrammatic.Limits.Cone

open CategoryTheory Limits Opposite HomotopicalAlgebra MonoidalCategory
open Atoms.Homotopical Atoms.Shape Simplicial

universe u

namespace Atoms.Diagrammatic

noncomputable abbrev relativeMappingSpace {V A X : DiagSet.{u}} (i : V ⟶ A) (f : V ⟶ X) :
    DiagSet.{u} :=
  pullback ((grayHomRestrict i).app X) (diagramPoint f)

noncomputable def relativeMappingSpaceHomEquiv {V A X : DiagSet.{u}} (i : V ⟶ A) (f : V ⟶ X)
    (T : DiagSet.{u}) : (T ⟶ relativeMappingSpace i f) ≃
      {F : grayTensor T A ⟶ X // (grayTensorLeft T).map i ≫ F = grayTensorSnd T V ≫ f} where
  toFun g := ⟨((grayTensorRightAdjunction A).homEquiv T X).symm
      (g ≫ pullback.fst ((grayHomRestrict i).app X) (diagramPoint f)), by
    refine ((grayTensorRightAdjunction V).homEquiv T X).injective ?_
    rw [← homEquiv_comp_grayHomRestrict, Equiv.apply_symm_apply, Category.assoc,
      pullback.condition, ← Category.assoc, comp_diagramPoint]⟩
  invFun F := (pullback.lift ((grayTensorRightAdjunction A).homEquiv T X F.1)
    (isTerminalBallAtomPoint.from T) (by
      rw [homEquiv_comp_grayHomRestrict, F.2, comp_diagramPoint]) :
      T ⟶ pullback ((grayHomRestrict i).app X) (diagramPoint f))
  left_inv g := pullback.hom_ext ((pullback.lift_fst _ _ _).trans (Equiv.apply_symm_apply _ _))
    (isTerminalBallAtomPoint.hom_ext _ _)
  right_inv F := Subtype.ext ((congrArg _ (pullback.lift_fst _ _ _)).trans
    (Equiv.symm_apply_apply _ _))

private noncomputable def flatTensorIso (A : DiagSet.{u}) :
    grayTensorRight A ⋙ MarkedPresheaf.flat atomMarking ≅
      MarkedPresheaf.flat atomMarking ⋙
        tensorRight false ((MarkedPresheaf.flat atomMarking).obj A) :=
  NatIso.ofComponents (fun T => (markedTensorFlatIso T A).symm)
    fun _ => MarkedPresheaf.hom_ext rfl

private noncomputable def forgetMarkedHomRightFlatNatIso (A : DiagSet.{u}) :
    markedHomRight false ((MarkedPresheaf.flat atomMarking).obj A) ⋙ MarkedPresheaf.forget ≅
      MarkedPresheaf.forget ⋙ grayHomRight A :=
  conjugateIsoEquiv ((MarkedPresheaf.flatForgetAdjunction atomMarking).comp
      (tensorRightAdjunction false ((MarkedPresheaf.flat atomMarking).obj A)))
    ((grayTensorRightAdjunction A).comp (MarkedPresheaf.flatForgetAdjunction atomMarking))
    (flatTensorIso A)

noncomputable def forgetMarkedHomRightFlatIso (A : DiagSet.{u}) (Y : MarkedDiagSet.{u}) :
    MarkedPresheaf.forget.obj ((markedHomRight false
      ((MarkedPresheaf.flat atomMarking).obj A)).obj Y) ≅
      (grayHomRight A).obj (MarkedPresheaf.forget.obj Y) :=
  (forgetMarkedHomRightFlatNatIso A).app Y

theorem homEquiv_forgetMarkedHomRightFlatIso {A T : DiagSet.{u}} {Y : MarkedDiagSet.{u}}
    (g : markedGrayTensor ((MarkedPresheaf.flat atomMarking).obj T)
      ((MarkedPresheaf.flat atomMarking).obj A) ⟶ Y) :
    MarkedPresheaf.forget.map
        ((tensorRightAdjunction false ((MarkedPresheaf.flat atomMarking).obj A)).homEquiv _ Y g) ≫
        (forgetMarkedHomRightFlatIso A Y).hom =
      (grayTensorRightAdjunction A).homEquiv T _ (MarkedPresheaf.forget.map g) :=
  (homEquiv_conjugateEquiv_app ((MarkedPresheaf.flatForgetAdjunction atomMarking).comp
      (tensorRightAdjunction false ((MarkedPresheaf.flat atomMarking).obj A)))
    ((grayTensorRightAdjunction A).comp (MarkedPresheaf.flatForgetAdjunction atomMarking))
    (flatTensorIso A).hom g).symm

theorem forget_map_markedHomRestrict_comp_forgetMarkedHomRightFlatIso {V A : DiagSet.{u}}
    (i : V ⟶ A) (Y : MarkedDiagSet.{u}) :
    MarkedPresheaf.forget.map
        ((markedHomRestrict ((MarkedPresheaf.flat atomMarking).map i)).app Y) ≫
        (forgetMarkedHomRightFlatIso V Y).hom =
      (forgetMarkedHomRightFlatIso A Y).hom ≫
        (grayHomRestrict i).app (MarkedPresheaf.forget.obj Y) := by
  have h (T : DiagSet.{u})
      (g : markedGrayTensor ((MarkedPresheaf.flat atomMarking).obj T)
        ((MarkedPresheaf.flat atomMarking).obj A) ⟶ Y) :
      MarkedPresheaf.forget.map ((tensorRightAdjunction false _).homEquiv _ Y g) ≫
        MarkedPresheaf.forget.map
            ((markedHomRestrict ((MarkedPresheaf.flat atomMarking).map i)).app Y) ≫
          (forgetMarkedHomRightFlatIso V Y).hom =
      MarkedPresheaf.forget.map ((tensorRightAdjunction false _).homEquiv _ Y g) ≫
        (forgetMarkedHomRightFlatIso A Y).hom ≫
          (grayHomRestrict i).app (MarkedPresheaf.forget.obj Y) := by
    refine (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ _) (MarkedPresheaf.forget.map_comp _ _).symm).trans <|
      (congrArg (fun k => MarkedPresheaf.forget.map k ≫ (forgetMarkedHomRightFlatIso V Y).hom)
        (homEquiv_markedHomRestrict _ g).symm).trans <|
      (homEquiv_forgetMarkedHomRightFlatIso _).trans <|
      (congrArg _ (MarkedPresheaf.forget.map_comp _ _)).trans <|
      (homEquiv_comp_grayHomRestrict i _).symm.trans <|
      (congrArg (· ≫ _) (homEquiv_forgetMarkedHomRightFlatIso g).symm).trans (Category.assoc _ _ _)
  let g₀ := ((tensorRightAdjunction false ((MarkedPresheaf.flat atomMarking).obj A)).homEquiv
    _ Y).symm (((MarkedPresheaf.flatForgetAdjunction atomMarking).homEquiv _ _).symm (𝟙 _))
  have e : MarkedPresheaf.forget.map
      ((tensorRightAdjunction false ((MarkedPresheaf.flat atomMarking).obj A)).homEquiv _ Y g₀) =
      𝟙 _ :=
    (congrArg MarkedPresheaf.forget.map (Equiv.apply_symm_apply _ _)).trans
      (((MarkedPresheaf.flatForgetAdjunction atomMarking).homEquiv _ _).apply_symm_apply (𝟙 _))
  have := h _ g₀
  rw [e] at this
  exact (Category.id_comp _).symm.trans (this.trans (Category.id_comp _))

theorem forgetMarkedHomRightFlatIso_natural (A Y : DiagSet.{u}) :
    forgetMarkedHomRightFlatIso A (MarkedDiagSet.natural.obj Y) = functorCategoryGrayIso A Y := by
  refine Iso.ext ?_
  let g₀ := ((tensorRightAdjunction false ((MarkedPresheaf.flat atomMarking).obj A)).homEquiv
    _ (MarkedDiagSet.natural.obj Y)).symm
      (((MarkedPresheaf.flatForgetAdjunction atomMarking).homEquiv _ _).symm (𝟙 _))
  have e : MarkedPresheaf.forget.map
      ((tensorRightAdjunction false ((MarkedPresheaf.flat atomMarking).obj A)).homEquiv _ _ g₀) =
      𝟙 _ :=
    (congrArg MarkedPresheaf.forget.map (Equiv.apply_symm_apply _ _)).trans
      (((MarkedPresheaf.flatForgetAdjunction atomMarking).homEquiv _ _).apply_symm_apply (𝟙 _))
  have h := (homEquiv_forgetMarkedHomRightFlatIso g₀).trans
    (homEquiv_functorCategoryToGrayHom g₀).symm
  rw [e] at h
  exact (Category.id_comp _).symm.trans (h.trans (Category.id_comp _))

private noncomputable def markedDiagramPoint {V X : DiagSet.{u}} (f : V ⟶ X) :
    ⊤_ MarkedDiagSet.{u} ⟶ (markedHomRight false ((MarkedPresheaf.flat atomMarking).obj V)).obj
      (MarkedDiagSet.natural.obj X) :=
  (tensorRightAdjunction false _).homEquiv _ _ (markedTensorSnd false _ _ ≫
    ((MarkedPresheaf.flatForgetAdjunction atomMarking).homEquiv V _).symm f)

private noncomputable def forgetTerminalIso :
    MarkedPresheaf.forget.obj (⊤_ MarkedDiagSet.{u}) ≅ ball.{u} atomPoint :=
  (terminalIsTerminal.isTerminalObj MarkedPresheaf.forget _).uniqueUpToIso isTerminalBallAtomPoint

private theorem forget_map_markedDiagramPoint_comp {V X : DiagSet.{u}} (f : V ⟶ X) :
    MarkedPresheaf.forget.map (markedDiagramPoint f) ≫
        (forgetMarkedHomRightFlatIso V (MarkedDiagSet.natural.obj X)).hom =
      forgetTerminalIso.hom ≫ diagramPoint f := by
  let ε := (MarkedPresheaf.flatForgetAdjunction atomMarking).counit.app (⊤_ MarkedDiagSet.{u})
  have hε : MarkedPresheaf.forget.map (ε ≫ markedDiagramPoint f) =
      MarkedPresheaf.forget.map (markedDiagramPoint f) :=
    (MarkedPresheaf.forget.map_comp _ _).trans (Category.id_comp _)
  refine (congrArg (· ≫ _) hε.symm).trans ?_
  refine (congrArg (fun k => MarkedPresheaf.forget.map k ≫ _)
    ((tensorRightAdjunction false _).homEquiv_naturality_left _ _).symm).trans ?_
  refine (congrArg (fun k => MarkedPresheaf.forget.map ((tensorRightAdjunction false _).homEquiv _ _
    k) ≫ (forgetMarkedHomRightFlatIso V (MarkedDiagSet.natural.obj X)).hom)
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _)
      (tensorRight_map_markedTensorSnd ε _)))).trans ?_
  exact (homEquiv_forgetMarkedHomRightFlatIso _).trans (comp_diagramPoint _ f).symm

private theorem exists_app_eq_of_dimension_eq_zero {V A : DiagSet.{u}} (i : V ⟶ A)
    (hi : ∀ a : A.Vertex, ∃ v : V.Vertex, v.map i = a)
    {W : Atom} (hW : W.dimension = 0) (a : diagram A W) : ∃ v, i.app (op W) v = a := by
  have := isIso_toAtomPoint_of_dimension_eq_zero hW
  have : IsIso (toAtomPoint (atomSimplex 0)) :=
    isIso_toAtomPoint_of_dimension_eq_zero (dimension_atomSimplex 0)
  let e : W ≅ atomSimplex 0 := asIso (toAtomPoint W) ≪≫ (asIso (toAtomPoint (atomSimplex 0))).symm
  obtain ⟨v, hv⟩ := hi (A.map e.inv.op a)
  refine ⟨V.map e.hom.op v, (NatTrans.naturality_apply i e.hom.op v).trans ?_⟩
  refine (congrArg (A.map e.hom.op) hv).trans ?_
  rw [← Functor.map_comp_apply, ← op_comp, e.hom_inv_id, op_id, Functor.map_id_apply]

private theorem exists_markingInclusion_comp_eq {V A X : DiagSet.{u}} (i : V ⟶ A)
    (hi : ∀ a : A.Vertex, ∃ v : V.Vertex, v.map i = a)
    (f : V ⟶ X) (hX : IsInftyCategory 1 X) {U : Atom} (hU : 0 < U.dimension)
    (G : markedGrayTensor ((MarkedPresheaf.flat atomMarking).obj (ball.{u} U))
      ((MarkedPresheaf.flat atomMarking).obj A) ⟶ MarkedDiagSet.natural.obj X)
    (hG : markedTensorMap false (𝟙 _) ((MarkedPresheaf.flat atomMarking).map i) ≫ G =
      markedTensorSnd false _ _ ≫
        ((MarkedPresheaf.flatForgetAdjunction atomMarking).homEquiv V
          (MarkedDiagSet.natural.obj X)).symm f) :
    ∃ G' : markedGrayTensor (MarkedDiagSet.markedAtom U hU)
        ((MarkedPresheaf.flat atomMarking).obj A) ⟶ MarkedDiagSet.natural.obj X,
      markedTensorMap false (MarkedDiagSet.markingInclusion U hU) (𝟙 _) ≫ G' = G := by
  have hG' : (grayTensorLeft (ball.{u} U)).map i ≫ MarkedPresheaf.forget.map G =
      grayTensorSnd (ball.{u} U) V ≫ f :=
    (MarkedPresheaf.forget.map_comp _ _).symm.trans ((congrArg MarkedPresheaf.forget.map hG).trans
      (MarkedPresheaf.forget.map_comp _ _))
  have hdeg {T : Atom} {z : diagram (grayTensor (ball.{u} U) A) T}
      (hz : IsDegenerate _ z) : IsEquivalence X ((MarkedPresheaf.forget.map G).app (op T) z) :=
    (MarkedDiagSet.mem_marked_natural_iff X T _).1
      (MarkedDiagSet.mem_marked_of_isDegenerate _ (isDegenerate_app _ hz))
  refine ⟨MarkedPresheaf.homMk (MarkedPresheaf.forget.map G) fun T z hz => ?_,
    MarkedPresheaf.hom_ext ((congrArg (· ≫ _) (grayTensorBifunctor.map_id _)).trans
      (Category.id_comp _))⟩
  refine (MarkedDiagSet.mem_marked_natural_iff X T _).2 ?_
  rcases (mem_marked_markedTensor false _ _ T z).1 hz with hz | ⟨W₁, W₂, u, a, e, hm, rfl⟩
  · exact hdeg hz
  refine (congrArg (IsEquivalence X)
    (NatTrans.naturality_apply (MarkedPresheaf.forget.map G) e.hom.op _)).mpr
    ((isEquivalence_map_iso_iff e _).2 ?_)
  rcases hm with hu | ha | ⟨h, -⟩
  · have hW₁ : 0 < W₁.dimension := MarkedPresheaf.markable _ W₁ u hu
    rcases Nat.eq_zero_or_pos W₂.dimension with hW₂ | hW₂
    · obtain ⟨v, rfl⟩ := exists_app_eq_of_dimension_eq_zero i hi hW₂ a
      have hc := congrArg (fun k => k.app (op (Atom.grayTensor W₁ W₂)) (grayTensorCell u v)) hG'
      refine (congrArg (IsEquivalence X) ((congrArg _
        (grayTensorCell_naturality (𝟙 _) i u v).symm).trans hc)).mpr ?_
      refine (congrArg (IsEquivalence X) ((congrArg (f.app _)
        (grayTensorSnd_app_grayTensorCell u v)).trans (NatTrans.naturality_apply f _ v))).mpr ?_
      exact (MarkedDiagSet.mem_marked_natural_iff X _ _).1
        (MarkedDiagSet.mem_marked_of_isDegenerate _ (isDegenerate_map_of_dimension_eq_zero _ hW₂
          (by rw [Atom.dimension_grayTensor]; omega) _))
    · exact hX.2 _ _ (by rw [Atom.dimension_grayTensor]; exact_mod_cast (by omega))
  · exact hdeg (isDegenerate_grayTensorCell
      (Or.inr ((MarkedDiagSet.mem_marked_flat_iff_isDegenerate A W₂ a).1 ha)))
  · exact absurd h Bool.false_ne_true

theorem isInftyCategory_zero_relativeMappingSpace {V A X : DiagSet.{u}} (i : V ⟶ A) [Mono i]
    (hi : ∀ a : A.Vertex, ∃ v : V.Vertex, v.map i = a)
    (f : V ⟶ X) (hX : IsInftyCategory 1 X) : IsInftyCategory 0 (relativeMappingSpace i f) := by
  let Xn := MarkedDiagSet.natural.obj X
  let iflat := (MarkedPresheaf.flat atomMarking).map i
  have : Mono iflat := (MarkedPresheaf.mono_iff _).2 ‹Mono i›
  let r := (markedHomRestrict iflat).app Xn
  let t := markedDiagramPoint f
  have hr : Fibration ((MarkedDiagSet.toCoinductive 1).map r) :=
    fibration_toCoinductive_one_markedHomRestrict iflat (isFibrant_coinductive_natural 1 hX)
  have hsnd : Fibration ((MarkedDiagSet.toCoinductive 1).map (pullback.snd r t)) :=
    (fibration_iff _).2 ((fibrations (MarkedDiagSet.Coinductive.{u} 1)).of_isPullback
      (IsPullback.of_hasPullback r t) ((fibration_iff _).1 hr))
  have : IsFibrant ((MarkedDiagSet.toCoinductive 1).obj (⊤_ MarkedDiagSet.{u})) :=
    (isFibrant_iff_of_isTerminal (𝟙 _) terminalIsTerminal).2 inferInstance
  have hM : IsFibrant ((MarkedDiagSet.toCoinductive 1).obj (pullback r t)) :=
    isFibrant_of_fibration ((MarkedDiagSet.toCoinductive 1).map (pullback.snd r t))
  obtain ⟨hM₁, hMm⟩ := (isFibrant_coinductive_iff_natural 1 _).1 hM
  have hmarked (U : Atom) (x : diagram (pullback r t).underlying U) (hU : 0 < U.dimension) :
      x ∈ (pullback r t).marked U := by
    let fn := ((MarkedPresheaf.flatForgetAdjunction atomMarking).homEquiv V Xn).symm f
    let q := ((MarkedPresheaf.flatForgetAdjunction atomMarking).homEquiv _ _).symm
      (uliftYonedaEquiv.symm x)
    let G := ((tensorRightAdjunction false ((MarkedPresheaf.flat atomMarking).obj A)).homEquiv
      _ _).symm (q ≫ pullback.fst r t)
    have hG : markedTensorMap false (𝟙 _) iflat ≫ G = markedTensorSnd false _ _ ≫ fn := by
      refine ((tensorRightAdjunction false ((MarkedPresheaf.flat atomMarking).obj V)).homEquiv
        _ _).injective ?_
      refine (homEquiv_markedHomRestrict iflat G).trans ?_
      refine (congrArg (· ≫ r) (Equiv.apply_symm_apply _ _)).trans ?_
      refine (Category.assoc _ _ _).trans ((congrArg (q ≫ ·) pullback.condition).trans ?_)
      refine (Category.assoc _ _ _).symm.trans ?_
      refine ((tensorRightAdjunction false _).homEquiv_naturality_left _ _).symm.trans ?_
      exact congrArg _ ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ fn) (tensorRight_map_markedTensorSnd _ _)))
    obtain ⟨G', hG'⟩ := exists_markingInclusion_comp_eq i hi f hX hU G hG
    let j := MarkedDiagSet.markingInclusion.{u} U hU
    have : Epi j := MarkedPresheaf.forget.epi_of_epi_map (inferInstanceAs (Epi (𝟙 _)))
    let e₁ := (tensorRightAdjunction false ((MarkedPresheaf.flat atomMarking).obj A)).homEquiv
      _ _ G'
    have he₁ : j ≫ e₁ = q ≫ pullback.fst r t :=
      ((tensorRightAdjunction false _).homEquiv_naturality_left _ _).symm.trans
        ((congrArg _ hG').trans (Equiv.apply_symm_apply _ _))
    let l := pullback.lift e₁ (terminal.from _) ((cancel_epi j).1
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ r) he₁).trans
        ((Category.assoc _ _ _).trans ((congrArg (q ≫ ·) pullback.condition).trans
          ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ t)
            (terminal.hom_ext _ _)).trans (Category.assoc _ _ _))))))))
    have hl : j ≫ l = q := pullback.hom_ext ((Category.assoc _ _ _).trans
      ((congrArg (j ≫ ·) (pullback.lift_fst _ _ _)).trans he₁)) (terminal.hom_ext _ _)
    have hx : (MarkedPresheaf.forget.map (j ≫ l)).app (op U)
        (⟨𝟙 U⟩ : (ball.{u} U).obj (op U)) = x :=
      (congrArg (fun k : (MarkedPresheaf.flat atomMarking).obj (ball.{u} U) ⟶ pullback r t =>
        (MarkedPresheaf.forget.map k).app (op U) (⟨𝟙 U⟩ : (ball.{u} U).obj (op U))) hl).trans
        (uliftYonedaEquiv.apply_symm_apply x)
    rw [← hx]
    exact MarkedPresheaf.map_mem_marked l
      ((MarkedPresheaf.mem_marked_ofMarking _ _ U _).2 (Or.inr (IsIso.id U)))
  have h₀ : IsInftyCategory 0 (pullback r t).underlying := ⟨hM₁.1, fun U x hU =>
    (hMm U x).1 (hmarked U x (Nat.cast_pos.1 hU))⟩
  have hP : IsPullback
      (MarkedPresheaf.forget.map (pullback.fst r t) ≫ (forgetMarkedHomRightFlatIso A Xn).hom)
      (MarkedPresheaf.forget.map (pullback.snd r t) ≫ forgetTerminalIso.hom)
      ((grayHomRestrict i).app X) (diagramPoint f) :=
    ((IsPullback.of_hasPullback r t).map MarkedPresheaf.forget).of_iso (Iso.refl _)
      (forgetMarkedHomRightFlatIso A Xn) forgetTerminalIso (forgetMarkedHomRightFlatIso V Xn)
      (Category.id_comp _).symm (Category.id_comp _).symm
      (forget_map_markedHomRestrict_comp_forgetMarkedHomRightFlatIso i Xn)
      (forget_map_markedDiagramPoint_comp f)
  exact isInftyCategory_of_iso hP.isoPullback.symm h₀

theorem DiagSet.isInftyCategory_zero_mappingSpace {X : DiagSet.{u}} (hX : IsInftyCategory 1 X)
    (x y : X.Vertex) : IsInftyCategory 0 (X.mappingSpace x y).toFunctor := by
  have h := isInftyCategory_zero_relativeMappingSpace intervalBoundaryι
    exists_intervalBoundaryι_app_eq (coprod.desc (vertexHom x) (vertexHom y)) hX
  have hP := DiagSet.isPullback_mappingSpace x y
  rw [DiagSet.endpointsPoint_eq_homEquiv] at hP
  exact isInftyCategory_of_iso hP.isoPullback h

end Atoms.Diagrammatic
