import Atoms.Diagrammatic.Fibration.CartesianSquare
import Atoms.Diagrammatic.FullSubpresheaf

open CategoryTheory Limits Opposite MonoidalCategory HomotopicalAlgebra
open Atoms.Shape Atoms.Homotopical

universe u

namespace Atoms.Diagrammatic

noncomputable def DiagSet.grayArrowVertexEquiv (X : DiagSet.{u}) :
    ((grayHomRight markedInterval.{u}.underlying).obj X).Vertex ≃
      diagram X (atomGlobe 1) :=
  (grayHomRightCellEquiv markedInterval.underlying X atomPoint).trans
    ((Iso.homCongr ((GrayDiagSet.leftUnitor markedInterval.underlying) ≪≫
      intervalBallIso.symm) (Iso.refl X)).trans uliftYonedaEquiv)

@[simp] theorem DiagSet.grayArrowVertexEquiv_apply (X : DiagSet.{u})
    (z : ((grayHomRight markedInterval.{u}.underlying).obj X).Vertex) :
    DiagSet.grayArrowVertexEquiv X z = DiagSet.intervalHomVertexCell z := rfl

theorem DiagSet.grayArrowVertexEquiv_map {X Y : DiagSet.{u}} (f : X ⟶ Y)
    (z : ((grayHomRight markedInterval.{u}.underlying).obj X).Vertex) :
    DiagSet.grayArrowVertexEquiv Y (z.map ((grayHomRight markedInterval.underlying).map f)) =
      f.app _ (DiagSet.grayArrowVertexEquiv X z) := by
  simp only [DiagSet.grayArrowVertexEquiv, Equiv.trans_apply, Iso.homCongr_apply,
    Iso.trans_inv, Iso.symm_inv, Iso.refl_hom, Category.comp_id]
  have h : grayHomRightCellEquiv markedInterval.underlying Y atomPoint
      (z.map ((grayHomRight markedInterval.underlying).map f)) =
      grayHomRightCellEquiv markedInterval.underlying X atomPoint z ≫ f := rfl
  rw [h, ← Category.assoc, uliftYonedaEquiv_comp]

private theorem uliftYonedaEquiv_intervalBallIso_hom_comp_leftUnitor_inv_comp {E : DiagSet.{u}}
    (g : grayTensor (ball atomPoint) markedInterval.underlying ⟶ E) :
    uliftYonedaEquiv (intervalBallIso.hom ≫
        (GrayDiagSet.leftUnitor markedInterval.underlying).inv ≫ g) =
      E.map (Atom.grayTensorLeftUnitor (atomGlobe 1)).inv.op
        (g.app _ (grayTensorCell (⟨𝟙 atomPoint⟩ : diagram (ball.{u} atomPoint) atomPoint)
          (intervalBallIso.hom.app _ ⟨𝟙 (atomGlobe 1)⟩))) := by
  let j := intervalBallIso.hom.app (op (atomGlobe 1)) ⟨𝟙 (atomGlobe 1)⟩
  let t := grayTensorCell (X := ball.{u} atomPoint)
    (Y := markedInterval.underlying) (⟨𝟙 atomPoint⟩ : diagram (ball.{u} atomPoint) atomPoint) j
  have hp : toAtomPoint atomPoint = 𝟙 atomPoint := isTerminalAtomPoint.hom_ext _ _
  have ht : (GrayDiagSet.leftUnitor markedInterval.underlying).hom.app _ t =
      markedInterval.underlying.map (Atom.grayTensorLeftUnitor (atomGlobe 1)).hom.op j := by
    simpa only [t, hp, Atom.grayTensorMap_id, Category.id_comp] using
      GrayDiagSet.leftUnitor_hom_app_grayTensorCell
        (⟨𝟙 atomPoint⟩ : diagram (ball.{u} atomPoint) atomPoint) j
  have hi : (GrayDiagSet.leftUnitor markedInterval.underlying).inv.app _ j =
      (grayTensor (ball atomPoint) markedInterval.underlying).map
        (Atom.grayTensorLeftUnitor (atomGlobe 1)).inv.op t := by
    have hh : (GrayDiagSet.leftUnitor markedInterval.underlying).hom.app _
        ((grayTensor (ball atomPoint) markedInterval.underlying).map
          (Atom.grayTensorLeftUnitor (atomGlobe 1)).inv.op t) = j := by
      exact (NatTrans.naturality_apply (GrayDiagSet.leftUnitor markedInterval.underlying).hom
        _ t).trans (congrArg _ ht) |>.trans (by
          rw [← Functor.map_comp_apply, ← op_comp, Iso.inv_hom_id, op_id,
            Functor.map_id_apply])
    exact (congrArg ((GrayDiagSet.leftUnitor markedInterval.underlying).inv.app _) hh).symm.trans
      (Iso.hom_inv_id_app_apply _ _ _)
  change g.app _ ((GrayDiagSet.leftUnitor markedInterval.underlying).inv.app _ j) = _
  exact (congrArg (g.app _) hi).trans (NatTrans.naturality_apply g _ t)

private theorem grayArrowVertexEquiv_map_op {E : DiagSet.{u}} {U : Atom}
    (z : diagram ((grayHomRight markedInterval.underlying).obj E) U)
    (v : atomPoint ⟶ U) :
    DiagSet.grayArrowVertexEquiv E (((grayHomRight markedInterval.underlying).obj E).map v.op z) =
      E.map (Atom.grayTensorLeftUnitor (atomGlobe 1)).inv.op
        ((grayHomRightCellEquiv markedInterval.underlying E U z).app _
          (grayTensorCell (⟨v⟩ : diagram (ball.{u} U) atomPoint)
            (intervalBallIso.hom.app _ ⟨𝟙 (atomGlobe 1)⟩))) := by
  refine (uliftYonedaEquiv_intervalBallIso_hom_comp_leftUnitor_inv_comp
    (grayHomRightCellEquiv markedInterval.underlying E atomPoint
      (((grayHomRight markedInterval.underlying).obj E).map v.op z))).trans
      (congrArg (E.map _) ?_)
  change (grayHomRightCellEquiv markedInterval.underlying E U z).app _
      (((grayTensorRight markedInterval.underlying).map (uliftYoneda.map v)).app _
        (grayTensorCell (⟨𝟙 atomPoint⟩ : diagram (ball.{u} atomPoint) atomPoint) _)) = _
  exact congrArg ((grayHomRightCellEquiv markedInterval.underlying E U z).app _)
    (grayTensorCell_naturality (uliftYoneda.map v) (𝟙 _) _ _)

private theorem app_mem_marked_cartesianMarked_of_vertical {E S A : DiagSet.{u}} (p : E ⟶ S)
    (f : grayTensor A markedInterval.underlying ⟶ E)
    (h : ∀ v : A.Vertex,
      f.app _ (grayTensorCell v (intervalBallIso.hom.app _ ⟨𝟙 (atomGlobe 1)⟩)) ∈
        (DiagSet.cartesianMarked p).marked (Atom.grayTensor atomPoint (atomGlobe 1))) :
    ∀ (T : Atom) (z : diagram (grayTensor A markedInterval.underlying) T),
      z ∈ (markedTensor false ((MarkedPresheaf.flat atomMarking).obj A)
        markedInterval).marked T → f.app _ z ∈ (DiagSet.cartesianMarked p).marked T := by
  intro T z hz
  rcases (mem_marked_markedTensor _ _ _ _ _).1 hz with hd | ⟨U, V, x, y, e, hm, rfl⟩
  · exact MarkedDiagSet.mem_marked_of_isDegenerate _ (isDegenerate_app f hd)
  refine (congrArg (· ∈ (DiagSet.cartesianMarked p).marked T)
    (NatTrans.naturality_apply f e.hom.op (grayTensorCell x y))).mpr ?_
  apply ((DiagSet.cartesianMarked p).transport e _).1
  rcases hm with hx | hy | ⟨hf, -⟩
  · exact MarkedDiagSet.mem_marked_of_isDegenerate _ (isDegenerate_app f
      (isDegenerate_grayTensorCell (Or.inl
        ((MarkedDiagSet.mem_marked_flat_iff_isDegenerate A U x).1 hx))))
  · obtain ⟨k, rfl⟩ : ∃ k : V ⟶ atomGlobe 1,
        intervalBallIso.hom.app _ ⟨k⟩ = y := ⟨y.down.1, rfl⟩
    obtain ⟨-, ⟨-, hk⟩ | hd⟩ := (mem_marked_yoneda_obj_iff _ V _).1 hy
    · change IsIso k at hk
      have := hk
      have hV : V.dimension = 1 :=
        (Atom.dimension_eq_of_iso (asIso k)).trans (dimension_atomGlobe 1)
      by_cases hU : U.dimension = 0
      · have := isIso_toAtomPoint_of_dimension_eq_zero hU
        let v := A.map (inv (toAtomPoint U)).op x
        have hx : A.map (toAtomPoint U).op v = x := by
          exact (A.map_comp_apply _ _ x).symm.trans
            (congrArg (fun t => A.map t x)
              (op_comp.symm.trans (congrArg Quiver.Hom.op
                (IsIso.hom_inv_id (toAtomPoint U)))) |>.trans (A.map_id_apply _ x))
        have hy : markedInterval.underlying.map k.op
            (intervalBallIso.hom.app _ ⟨𝟙 (atomGlobe 1)⟩) =
              intervalBallIso.hom.app _ ⟨k⟩ := by
          exact (NatTrans.naturality_apply intervalBallIso.hom k.op _).symm
        refine (congrArg (fun t => f.app _ t ∈ (DiagSet.cartesianMarked p).marked _)
          (congrArg₂ grayTensorCell hx.symm hy.symm |>.trans
            (grayTensorCell_restrict (toAtomPoint U) k v _))).mpr ?_
        refine (congrArg (· ∈ (DiagSet.cartesianMarked p).marked _)
          (NatTrans.naturality_apply f _ _)).mpr ?_
        exact ((DiagSet.cartesianMarked p).transport
          (Atom.grayTensorFunctor.mapIso ((asIso (toAtomPoint U)).prod (asIso k))) _).1 (h v)
      · exact (DiagSet.mem_marked_cartesianMarked p _ _).2 (Or.inr (Or.inl (by
          rw [Atom.dimension_grayTensor, hV]; omega)))
    · exact MarkedDiagSet.mem_marked_of_isDegenerate _ (isDegenerate_app f
        (isDegenerate_grayTensorCell (Or.inr (isDegenerate_app intervalBallIso.hom
          (isDegenerate_ball_of_degenerate hd)))))
  · exact (Bool.false_ne_true hf).elim

private theorem forall_marked_iff_mem_fullSubpresheaf {E S : DiagSet.{u}} (p : E ⟶ S)
    [Fibration ((DiagSet.toInfty 1).map p)] [IsFibrant ((DiagSet.toInfty 1).obj S)]
    {U : Atom} (z : diagram ((grayHomRight markedInterval.underlying).obj E) U) :
    (∀ T x, x ∈ (markedTensor false ((MarkedPresheaf.flat atomMarking).obj (ball U))
        markedInterval).marked T →
      (grayHomRightCellEquiv markedInterval.underlying E U z).app _ x ∈
        (DiagSet.cartesianMarked p).marked T) ↔
      z ∈ (((grayHomRight markedInterval.underlying).obj E).fullSubpresheaf
        (fun v => DiagSet.IsCartesianEdge p (DiagSet.Edge.ofCell
          (DiagSet.grayArrowVertexEquiv E v)))).obj (op U) := by
  have hc (v : atomPoint ⟶ U) := DiagSet.mem_marked_cartesianMarked_edge_iff p
    (DiagSet.Edge.ofCell (DiagSet.grayArrowVertexEquiv E
      (((grayHomRight markedInterval.underlying).obj E).map v.op z)))
  simp only [grayArrowVertexEquiv_map_op] at hc
  constructor
  · intro h v
    apply (hc v).1
    exact ((DiagSet.cartesianMarked p).transport
      (Atom.grayTensorLeftUnitor (atomGlobe 1)).symm _).1 (h _ _
        ((mem_marked_markedTensor _ _ _ _ _).2 (Or.inr
          ⟨atomPoint, atomGlobe 1, ⟨v⟩, _, Iso.refl _,
            Or.inr (Or.inl intervalBallIso_top_mem_marked), by
              simp only [Iso.refl_hom, op_id, Functor.map_id_apply]
              rfl⟩)))
  · intro h
    apply app_mem_marked_cartesianMarked_of_vertical p
    intro v
    exact ((DiagSet.cartesianMarked p).transport
      (Atom.grayTensorLeftUnitor (atomGlobe 1)).symm _).2 ((hc v.down).2 (h v.down))

private noncomputable def markedHomAsSubtype (X Y : MarkedDiagSet.{u}) :
    (X ⟶ Y) ≃ {f : X.underlying ⟶ Y.underlying //
      ∀ T z, z ∈ X.marked T → f.app _ z ∈ Y.marked T} where
  toFun f := ⟨MarkedPresheaf.forget.map f, fun _ _ => MarkedPresheaf.map_mem_marked f⟩
  invFun f := MarkedPresheaf.homMk f.1 f.2
  left_inv f := MarkedPresheaf.hom_ext (rfl : MarkedPresheaf.forget.map
    (MarkedPresheaf.homMk _ _) = MarkedPresheaf.forget.map f)
  right_inv f := Subtype.ext (rfl : MarkedPresheaf.forget.map
    (MarkedPresheaf.homMk f.1 f.2) = f.1)

private noncomputable def markedIntervalHomCell {E S : DiagSet.{u}} (p : E ⟶ S) (U : Atom) :
    diagram ((MarkedPresheaf.forget (D := atomMarking)).obj
      ((markedHomRight false markedInterval).obj (DiagSet.cartesianMarked p))) U ≃
      {f : grayTensor (ball U) markedInterval.underlying ⟶ E //
        ∀ T z, z ∈ (markedTensor false ((MarkedPresheaf.flat atomMarking).obj (ball U))
          markedInterval).marked T → f.app _ z ∈ (DiagSet.cartesianMarked p).marked T} :=
  (Iso.homCongr
    (((tensorRight false markedInterval).mapIso
      ((MarkedPresheaf.yonedaCompFlatIso atomMarking).app U)).symm)
        (Iso.refl (DiagSet.cartesianMarked p))).trans (markedHomAsSubtype _ _)

noncomputable def DiagSet.forgetMarkedHomRightIso {E S : DiagSet.{u}} (p : E ⟶ S)
    [Fibration ((DiagSet.toInfty 1).map p)] [IsFibrant ((DiagSet.toInfty 1).obj S)] :
    (MarkedPresheaf.forget (D := atomMarking)).obj
      ((markedHomRight false markedInterval).obj (DiagSet.cartesianMarked p)) ≅
        (((grayHomRight markedInterval.underlying).obj E).fullSubpresheaf
          (fun v => DiagSet.IsCartesianEdge p (DiagSet.Edge.ofCell
            (DiagSet.grayArrowVertexEquiv E v)))).toFunctor :=
  NatIso.ofComponents (fun U => Equiv.toIso
    { toFun z := ⟨(grayHomRightCellEquiv _ E U.unop).symm (markedIntervalHomCell p U.unop z).1,
        (forall_marked_iff_mem_fullSubpresheaf p _).1 (markedIntervalHomCell p U.unop z).2⟩
      invFun z := (markedIntervalHomCell p U.unop).symm
        ⟨grayHomRightCellEquiv _ E U.unop z.1, (forall_marked_iff_mem_fullSubpresheaf p z.1).2 z.2⟩
      left_inv z := by
        apply (markedIntervalHomCell p U.unop).injective
        apply Subtype.ext
        simp only [Equiv.apply_symm_apply]
      right_inv z := Subtype.ext (congrArg (grayHomRightCellEquiv _ E U.unop).symm
        (congrArg Subtype.val (Equiv.apply_symm_apply _ _)) |>.trans
          (Equiv.symm_apply_apply _ _)) }) (by
    intro U V f
    ext z
    apply Subtype.ext
    apply (grayHomRightCellEquiv _ E V.unop).injective
    change (markedIntervalHomCell p V.unop
      (((MarkedPresheaf.forget (D := atomMarking)).obj
        ((markedHomRight false markedInterval).obj (DiagSet.cartesianMarked p))).map f z)).1 =
      (grayTensorRight markedInterval.underlying).map (uliftYoneda.map f.unop) ≫
        (markedIntervalHomCell p U.unop z).1
    change (MarkedPresheaf.forget (D := atomMarking)).map
      ((tensorRight false markedInterval).map
        ((MarkedPresheaf.yonedaCompFlatIso atomMarking).hom.app V.unop) ≫
        (tensorRight false markedInterval).map
          ((MarkedSite.unmarked atomMarking ⋙ MarkedPresheaf.yoneda atomMarking).map f.unop) ≫
            z) = _
    have hn := (MarkedPresheaf.yonedaCompFlatIso atomMarking).hom.naturality f.unop
    have hm := congrArg (fun g => (tensorRight false markedInterval).map g ≫ z) hn
    simp only [Functor.map_comp] at hm
    have hh := congrArg ((MarkedPresheaf.forget (D := atomMarking)).map) hm.symm
    exact ((MarkedPresheaf.forget (D := atomMarking)).map_comp _ _).symm.trans hh |>.trans
      ((MarkedPresheaf.forget (D := atomMarking)).map_comp _ _))

private noncomputable def forgetHomComparison (A Y : MarkedDiagSet.{u}) :
    (MarkedPresheaf.forget (D := atomMarking)).obj ((markedHomRight false A).obj Y) ⟶
      (grayHomRight A.underlying).obj Y.underlying where
  app U := TypeCat.ofHom fun z =>
    (grayHomRightCellEquiv A.underlying Y.underlying U.unop).symm
    (MarkedPresheaf.forget.map ((tensorRight false A).map
      ((MarkedPresheaf.yonedaCompFlatIso atomMarking).hom.app U.unop) ≫ z))
  naturality U V f := by
    ext z
    apply (grayHomRightCellEquiv _ _ V.unop).injective
    change MarkedPresheaf.forget.map ((tensorRight false A).map
      ((MarkedPresheaf.yonedaCompFlatIso atomMarking).hom.app V.unop) ≫
      (tensorRight false A).map
        ((MarkedSite.unmarked atomMarking ⋙ MarkedPresheaf.yoneda atomMarking).map f.unop) ≫ z) = _
    have hn := (MarkedPresheaf.yonedaCompFlatIso atomMarking).hom.naturality f.unop
    have hm := congrArg (fun g => (tensorRight false A).map g ≫ z) hn
    simp only [Functor.map_comp] at hm
    have hh := congrArg ((MarkedPresheaf.forget (D := atomMarking)).map) hm.symm
    exact ((MarkedPresheaf.forget (D := atomMarking)).map_comp _ _).symm.trans hh |>.trans
      ((MarkedPresheaf.forget (D := atomMarking)).map_comp _ _)

private noncomputable def forgetHomSharpIso (A : MarkedDiagSet.{u}) (X : DiagSet.{u}) :
    (MarkedPresheaf.forget (D := atomMarking)).obj
      ((markedHomRight false A).obj ((MarkedPresheaf.sharp atomMarking).obj X)) ≅
        (grayHomRight A.underlying).obj X :=
  NatIso.ofComponents (fun U => Equiv.toIso
    ((Iso.homCongr (((tensorRight false A).mapIso
      ((MarkedPresheaf.yonedaCompFlatIso atomMarking).app U.unop)).symm) (Iso.refl _)).trans
        (((MarkedPresheaf.forgetSharpAdjunction atomMarking).homEquiv _ _).symm.trans
          (grayHomRightCellEquiv _ _ U.unop).symm)))
    (fun {_ _} f => (forgetHomComparison A ((MarkedPresheaf.sharp atomMarking).obj X)).naturality f)

private noncomputable def forgetHomUnitIso (Y : MarkedDiagSet.{u}) :
    (MarkedPresheaf.forget (D := atomMarking)).obj
      ((markedHomRight false markedTensorUnit).obj Y) ≅
        (grayHomRight (ball atomPoint)).obj Y.underlying :=
  NatIso.ofComponents (fun U => Equiv.toIso
    ((Iso.homCongr
      ((((tensorRight false markedTensorUnit).mapIso
        ((MarkedPresheaf.yonedaCompFlatIso atomMarking).app U.unop)).symm) ≪≫
          (markedTensorFlatIso (ball U.unop) (ball atomPoint)))
      (Iso.refl Y)).trans
        (((MarkedPresheaf.flatForgetAdjunction atomMarking).homEquiv _ _).trans
          (grayHomRightCellEquiv _ _ U.unop).symm)))
    (fun {_ _} f => (forgetHomComparison markedTensorUnit Y).naturality f)

private theorem forgetHomComparison_naturality (A : MarkedDiagSet.{u})
    {Y Z : MarkedDiagSet.{u}} (f : Y ⟶ Z) :
    MarkedPresheaf.forget.map ((markedHomRight false A).map f) ≫ forgetHomComparison A Z =
      forgetHomComparison A Y ≫ (grayHomRight A.underlying).map (MarkedPresheaf.forget.map f) := by
  ext U z
  apply (grayHomRightCellEquiv _ _ U.unop).injective
  exact congrArg ((MarkedPresheaf.forget (D := atomMarking)).map)
    (Category.assoc _ _ _).symm |>.trans ((MarkedPresheaf.forget (D := atomMarking)).map_comp _ _)

private theorem tensorRightAdjunction_homEquiv_hom_app_id (A Y : MarkedDiagSet.{u}) (U : Atom)
    (g : (tensorRight false A).obj ((MarkedPresheaf.yoneda atomMarking).obj
      ((MarkedSite.unmarked atomMarking).obj U)) ⟶ Y) :
    (((tensorRightAdjunction false A).homEquiv _ _ g).hom.app
      (op ((MarkedSite.unmarked atomMarking).obj U)) ⟨𝟙 _⟩) = g := by
  have hh := MarkedPresheaf.homEquiv_adjunctionOfPreservesColimits_app
    (tensorRight false A) (coversEpi_tensorRight false A) g
      ((MarkedSite.unmarked atomMarking).obj U) ⟨𝟙 _⟩
  have hi : (ObjectProperty.homMk (uliftYonedaEquiv.symm
      (⟨𝟙 ((MarkedSite.unmarked atomMarking).obj U)⟩ :
        ((MarkedPresheaf.yoneda atomMarking).obj
          ((MarkedSite.unmarked atomMarking).obj U)).obj.obj
            (op ((MarkedSite.unmarked atomMarking).obj U)))) :
      (MarkedPresheaf.yoneda atomMarking).obj ((MarkedSite.unmarked atomMarking).obj U) ⟶
        (MarkedPresheaf.yoneda atomMarking).obj ((MarkedSite.unmarked atomMarking).obj U)) =
          𝟙 _ := by
    apply MarkedPresheaf.hom_ext
    ext V z
    simp only [uliftYonedaEquiv, Equiv.coe_fn_symm_mk]
    rfl
  exact hh.trans ((congrArg (fun k => (tensorRight false A).map k ≫ g) hi).trans
    ((congrArg (· ≫ g) ((tensorRight false A).map_id _)).trans (Category.id_comp _)))

private theorem markedHomRestrict_cell {A B Y : MarkedDiagSet.{u}} (i : A ⟶ B)
    (U : Atom) (z : diagram
      ((MarkedPresheaf.forget (D := atomMarking)).obj ((markedHomRight false B).obj Y)) U) :
    (MarkedPresheaf.forget.map ((markedHomRestrict i).app Y)).app (op U) z =
      markedTensorMap false (𝟙 _) i ≫ z := by
  have hh := congrArg (fun f => f.hom.app
    (op ((MarkedSite.unmarked atomMarking).obj U)) ⟨𝟙 _⟩)
      (homEquiv_markedHomRestrict i z)
  have hl := tensorRightAdjunction_homEquiv_hom_app_id A Y U (markedTensorMap false (𝟙 _) i ≫ z)
  have hr := tensorRightAdjunction_homEquiv_hom_app_id B Y U z
  exact (congrArg
    (fun t => (MarkedPresheaf.forget.map ((markedHomRestrict i).app Y)).app (op U) t) hr.symm).trans
      (hh.symm.trans hl)

private theorem forgetHomComparison_restrict {A B Y : MarkedDiagSet.{u}} (i : A ⟶ B) :
    MarkedPresheaf.forget.map ((markedHomRestrict i).app Y) ≫ forgetHomComparison A Y =
      forgetHomComparison B Y ≫ (grayHomRestrict (MarkedPresheaf.forget.map i)).app
        Y.underlying := by
  ext U z
  apply (grayHomRightCellEquiv _ _ U.unop).injective
  change MarkedPresheaf.forget.map ((tensorRight false A).map
    ((MarkedPresheaf.yonedaCompFlatIso atomMarking).hom.app U.unop) ≫
      (MarkedPresheaf.forget.map ((markedHomRestrict i).app Y)).app U z) = _
  have hr := grayHomRightCellEquiv_grayHomRestrict (MarkedPresheaf.forget.map i)
    Y.underlying U.unop ((forgetHomComparison B Y).app U z)
  refine (congrArg (fun t => MarkedPresheaf.forget.map
    ((tensorRight false A).map
      ((MarkedPresheaf.yonedaCompFlatIso atomMarking).hom.app U.unop) ≫ t))
        (markedHomRestrict_cell i U.unop z)).trans ?_
  refine Eq.trans ?_ hr.symm
  have hn := (Functor.curry.obj (markedTensorBifunctor false)).flip.map i |>.naturality
    ((MarkedPresheaf.yonedaCompFlatIso atomMarking).hom.app U.unop)
  have hh := congrArg (fun f => MarkedPresheaf.forget.map (f ≫ z)) hn
  exact hh.trans ((MarkedPresheaf.forget (D := atomMarking)).map_comp _ _)

private theorem isPullback_forget_map_markedLeibniz {E S : DiagSet.{u}} (p : E ⟶ S) :
    let M := Functor.PullbackObjObj.ofHasPullback markedHomRightBifunctor.{u}
      (markedIntervalVertex true) (DiagSet.cartesianMarkedHom p)
    IsPullback
      (MarkedPresheaf.forget.map M.fst ≫ (forgetHomUnitIso (DiagSet.cartesianMarked p)).hom)
      (MarkedPresheaf.forget.map M.snd ≫
        (forgetHomSharpIso markedInterval S).hom)
      ((grayHomRight (ball atomPoint)).map p)
      ((grayHomRestrict (MarkedPresheaf.forget.map (markedIntervalVertex true))).app S) := by
  intro M
  refine M.isPullback.map (MarkedPresheaf.forget (D := atomMarking)) |>.of_iso
    (Iso.refl _) (forgetHomUnitIso (DiagSet.cartesianMarked p))
    (forgetHomSharpIso markedInterval S)
    (forgetHomUnitIso ((MarkedPresheaf.sharp atomMarking).obj S)) ?_ ?_ ?_ ?_
  · exact (Category.id_comp _).symm
  · exact (Category.id_comp _).symm
  · exact forgetHomComparison_naturality markedTensorUnit (DiagSet.cartesianMarkedHom p)
  · exact forgetHomComparison_restrict (markedIntervalVertex true)

noncomputable def DiagSet.forgetMarkedLeibnizTargetIso {E S : DiagSet.{u}} (p : E ⟶ S) :
    (MarkedPresheaf.forget (D := atomMarking)).obj
      (Functor.PullbackObjObj.ofHasPullback markedHomRightBifunctor.{u}
        (markedIntervalVertex true) (DiagSet.cartesianMarkedHom p)).pt ≅
      (Functor.PullbackObjObj.ofHasPullback grayHomRightBifunctor.{u}
        (MarkedPresheaf.forget.map (markedIntervalVertex true)) p).pt :=
  (isPullback_forget_map_markedLeibniz p).isoPullback

private theorem forget_map_π_comp_forgetMarkedLeibnizTargetIso_hom_fst {E S : DiagSet.{u}}
    (p : E ⟶ S) :
    let M := Functor.PullbackObjObj.ofHasPullback markedHomRightBifunctor.{u}
      (markedIntervalVertex true) (DiagSet.cartesianMarkedHom p)
    let Q := Functor.PullbackObjObj.ofHasPullback grayHomRightBifunctor.{u}
      (MarkedPresheaf.forget.map (markedIntervalVertex true)) p
    (MarkedPresheaf.forget.map M.π ≫ (DiagSet.forgetMarkedLeibnizTargetIso p).hom) ≫ Q.fst =
      (forgetHomComparison markedInterval (DiagSet.cartesianMarked p) ≫ Q.π) ≫ Q.fst := by
  intro M Q
  change (MarkedPresheaf.forget.map M.π ≫
    (isPullback_forget_map_markedLeibniz p).isoPullback.hom) ≫ Q.fst = _
  have hl := (Category.assoc (MarkedPresheaf.forget.map M.π) _ Q.fst).trans
    (congrArg (MarkedPresheaf.forget.map M.π ≫ ·)
      (isPullback_forget_map_markedLeibniz p).isoPullback_hom_fst)
  have hm := (Category.assoc (MarkedPresheaf.forget.map M.π)
    (MarkedPresheaf.forget.map M.fst) _).symm.trans
    (congrArg (· ≫ (forgetHomUnitIso (DiagSet.cartesianMarked p)).hom)
      (((MarkedPresheaf.forget (D := atomMarking)).map_comp M.π M.fst).symm.trans
        (congrArg ((MarkedPresheaf.forget (D := atomMarking)).map) M.π_fst)))
  exact (hl.trans hm |>.trans (forgetHomComparison_restrict (markedIntervalVertex true))).trans
    ((congrArg (forgetHomComparison markedInterval (DiagSet.cartesianMarked p) ≫ ·)
      Q.π_fst).symm.trans (Category.assoc _ _ _).symm)

private theorem forget_map_π_comp_forgetMarkedLeibnizTargetIso_hom_snd {E S : DiagSet.{u}}
    (p : E ⟶ S) :
    let M := Functor.PullbackObjObj.ofHasPullback markedHomRightBifunctor.{u}
      (markedIntervalVertex true) (DiagSet.cartesianMarkedHom p)
    let Q := Functor.PullbackObjObj.ofHasPullback grayHomRightBifunctor.{u}
      (MarkedPresheaf.forget.map (markedIntervalVertex true)) p
    (MarkedPresheaf.forget.map M.π ≫ (DiagSet.forgetMarkedLeibnizTargetIso p).hom) ≫ Q.snd =
      (forgetHomComparison markedInterval (DiagSet.cartesianMarked p) ≫ Q.π) ≫ Q.snd := by
  intro M Q
  change (MarkedPresheaf.forget.map M.π ≫
    (isPullback_forget_map_markedLeibniz p).isoPullback.hom) ≫ Q.snd = _
  have hl := (Category.assoc (MarkedPresheaf.forget.map M.π) _ Q.snd).trans
    (congrArg (MarkedPresheaf.forget.map M.π ≫ ·)
      (isPullback_forget_map_markedLeibniz p).isoPullback_hom_snd)
  have hm := (Category.assoc (MarkedPresheaf.forget.map M.π)
    (MarkedPresheaf.forget.map M.snd) _).symm.trans
    (congrArg (· ≫ (forgetHomSharpIso markedInterval S).hom)
      (((MarkedPresheaf.forget (D := atomMarking)).map_comp M.π M.snd).symm.trans
        (congrArg ((MarkedPresheaf.forget (D := atomMarking)).map) M.π_snd)))
  exact (hl.trans hm |>.trans
    (forgetHomComparison_naturality markedInterval (DiagSet.cartesianMarkedHom p))).trans
      ((congrArg (forgetHomComparison markedInterval (DiagSet.cartesianMarked p) ≫ ·)
        Q.π_snd).symm.trans (Category.assoc _ _ _).symm)

private theorem forget_map_π_comp_forgetMarkedLeibnizTargetIso_hom {E S : DiagSet.{u}} (p : E ⟶ S) :
    MarkedPresheaf.forget.map
        (Functor.PullbackObjObj.ofHasPullback markedHomRightBifunctor.{u}
          (markedIntervalVertex true) (DiagSet.cartesianMarkedHom p)).π ≫
        (DiagSet.forgetMarkedLeibnizTargetIso p).hom =
      forgetHomComparison markedInterval (DiagSet.cartesianMarked p) ≫
        (Functor.PullbackObjObj.ofHasPullback grayHomRightBifunctor.{u}
          (MarkedPresheaf.forget.map (markedIntervalVertex true)) p).π := by
  let M := Functor.PullbackObjObj.ofHasPullback markedHomRightBifunctor.{u}
    (markedIntervalVertex true) (DiagSet.cartesianMarkedHom p)
  let Q := Functor.PullbackObjObj.ofHasPullback grayHomRightBifunctor.{u}
    (MarkedPresheaf.forget.map (markedIntervalVertex true)) p
  exact Q.hom_ext (forget_map_π_comp_forgetMarkedLeibnizTargetIso_hom_fst p)
    (forget_map_π_comp_forgetMarkedLeibnizTargetIso_hom_snd p)

theorem DiagSet.forget_map_markedLeibniz_π {E S : DiagSet.{u}} (p : E ⟶ S)
    [Fibration ((DiagSet.toInfty 1).map p)] [IsFibrant ((DiagSet.toInfty 1).obj S)] :
    (MarkedPresheaf.forget (D := atomMarking)).map
        (Functor.PullbackObjObj.ofHasPullback markedHomRightBifunctor.{u}
          (markedIntervalVertex true) (DiagSet.cartesianMarkedHom p)).π ≫
        (DiagSet.forgetMarkedLeibnizTargetIso p).hom =
      (DiagSet.forgetMarkedHomRightIso p).hom ≫
        (((grayHomRight markedInterval.underlying).obj E).fullSubpresheaf
          (fun v => DiagSet.IsCartesianEdge p (DiagSet.Edge.ofCell
            (DiagSet.grayArrowVertexEquiv E v)))).ι ≫
        (Functor.PullbackObjObj.ofHasPullback grayHomRightBifunctor.{u}
          (MarkedPresheaf.forget.map (markedIntervalVertex true)) p).π := by
  let Q := Functor.PullbackObjObj.ofHasPullback grayHomRightBifunctor.{u}
    (MarkedPresheaf.forget.map (markedIntervalVertex true)) p
  have hc : (DiagSet.forgetMarkedHomRightIso p).hom ≫
      (((grayHomRight markedInterval.underlying).obj E).fullSubpresheaf
        (fun v => DiagSet.IsCartesianEdge p (DiagSet.Edge.ofCell
          (DiagSet.grayArrowVertexEquiv E v)))).ι =
        forgetHomComparison markedInterval (DiagSet.cartesianMarked p) := by
    ext U z
    rfl
  exact (forget_map_π_comp_forgetMarkedLeibnizTargetIso_hom p).trans
    ((congrArg (· ≫ Q.π) hc.symm).trans (Category.assoc _ _ _))

end Atoms.Diagrammatic
