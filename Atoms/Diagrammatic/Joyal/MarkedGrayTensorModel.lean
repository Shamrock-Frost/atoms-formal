import Atoms.Diagrammatic.Joyal.Comparison
import Atoms.Diagrammatic.Joyal.GrayTensorModel
import Atoms.Diagrammatic.Marked.GrayTensorMonoidal
import Atoms.Diagrammatic.Marked.PseudoGrayComparison
import Atoms.ForMathlib.CategoryTheory.Adjunction.Mates

open CategoryTheory Limits Opposite HomotopicalAlgebra MonoidalCategory CartesianMonoidalCategory
open Atoms.Homotopical Atoms.Shape Simplicial

universe u

namespace Atoms.Diagrammatic

@[reassoc] private theorem markedTensorMap_markedTensorFst {X Y X' Y' : MarkedDiagSet.{u}}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    markedTensorMap false f g ≫ markedTensorFst false X' Y' = markedTensorFst false X Y ≫ f :=
  MarkedPresheaf.hom_ext (grayTensorBifunctor_map_grayTensorFst _ _)

@[reassoc] private theorem markedTensorMap_markedTensorSnd {X Y X' Y' : MarkedDiagSet.{u}}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    markedTensorMap false f g ≫ markedTensorSnd false X' Y' = markedTensorSnd false X Y ≫ g :=
  MarkedPresheaf.hom_ext (grayTensorBifunctor_map_grayTensorSnd _ _)

noncomputable def markedFaceNerveTensorComparison (X Y : MarkedDiagSet.{u}) :
    markedFaceNerve.obj (markedGrayTensor X Y) ⟶ markedFaceNerve.obj X ⊗ markedFaceNerve.obj Y :=
  lift (markedFaceNerve.map (markedTensorFst false X Y))
    (markedFaceNerve.map (markedTensorSnd false X Y))

@[reassoc] theorem markedFaceNerveTensorComparison_naturality {X Y X' Y' : MarkedDiagSet.{u}}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    markedFaceNerve.map (markedTensorMap false f g) ≫ markedFaceNerveTensorComparison X' Y' =
      markedFaceNerveTensorComparison X Y ≫ (markedFaceNerve.map f ⊗ₘ markedFaceNerve.map g) :=
  CartesianMonoidalCategory.hom_ext _ _
    (by simp only [markedFaceNerveTensorComparison, Category.assoc, lift_fst, tensorHom_fst,
      lift_fst_assoc, ← Functor.map_comp, markedTensorMap_markedTensorFst])
    (by simp only [markedFaceNerveTensorComparison, Category.assoc, lift_snd, tensorHom_snd,
      lift_snd_assoc, ← Functor.map_comp, markedTensorMap_markedTensorSnd])

private instance isIso_lift_prod_fst_prod_snd (A B : MarkedSSet.{u}) :
    IsIso (lift prod.fst prod.snd : A ⨯ B ⟶ A ⊗ B) :=
  ⟨prod.lift (fst A B) (snd A B),
    prod.hom_ext
      (by simp only [Category.assoc, prod.lift_fst, lift_fst, Category.id_comp])
      (by simp only [Category.assoc, prod.lift_snd, lift_snd, Category.id_comp]),
    CartesianMonoidalCategory.hom_ext _ _
      (by simp only [Category.assoc, prod.lift_fst, lift_fst, Category.id_comp])
      (by simp only [Category.assoc, prod.lift_snd, lift_snd, Category.id_comp])⟩

instance isIso_markedFaceNerveTensorComparison_flat (A B : DiagSet.{u}) :
    IsIso (markedFaceNerveTensorComparison ((MarkedPresheaf.flat atomMarking).obj A)
      ((MarkedPresheaf.flat atomMarking).obj B)) := by
  have h : markedFaceNerve.map (markedTensorFlatIso A B).inv ≫
      markedFaceNerveTensorComparison _ _ =
        prod.lift (faceNerve.map (grayTensorFst A B)) (faceNerve.map (grayTensorSnd A B)) ≫
          lift prod.fst prod.snd := by
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · refine ((Category.assoc _ _ _).trans ((congrArg _ (lift_fst _ _)).trans
        ((markedFaceNerve.map_comp _ _).symm.trans ?_))).trans ((Category.assoc _ _ _).trans
          ((congrArg _ (lift_fst _ _)).trans (prod.lift_fst _ _))).symm
      exact congrArg markedFaceNerve.map (MarkedPresheaf.hom_ext
        ((MarkedPresheaf.forget.map_comp _ _).trans (Category.id_comp _)))
    · refine ((Category.assoc _ _ _).trans ((congrArg _ (lift_snd _ _)).trans
        ((markedFaceNerve.map_comp _ _).symm.trans ?_))).trans ((Category.assoc _ _ _).trans
          ((congrArg _ (lift_snd _ _)).trans (prod.lift_snd _ _))).symm
      exact congrArg markedFaceNerve.map (MarkedPresheaf.hom_ext
        ((MarkedPresheaf.forget.map_comp _ _).trans (Category.id_comp _)))
  have h₁ : IsIso (prod.lift (faceNerve.map (grayTensorFst A B))
      (faceNerve.map (grayTensorSnd A B))) := by
    rw [← faceNerveGrayTensorIso_hom_app]
    exact inferInstanceAs (IsIso (faceNerveGrayTensorIso.app (A, B)).hom)
  have h₂ := isIso_lift_prod_fst_prod_snd (faceNerve.obj A) (faceNerve.obj B)
  have : IsIso (markedFaceNerve.map (markedTensorFlatIso A B).inv ≫
      markedFaceNerveTensorComparison _ _) := by
    rw [h]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h₁ h₂
  exact IsIso.of_isIso_comp_left (markedFaceNerve.map (markedTensorFlatIso A B).inv) _

instance isIso_forget_map_markedFaceNerveTensorComparison (X Y : MarkedDiagSet.{u}) :
    IsIso (MarkedPresheaf.forget.map (markedFaceNerveTensorComparison X Y)) := by
  let ε := (MarkedPresheaf.flatForgetAdjunction atomMarking).counit
  have hε (Z : MarkedDiagSet.{u}) : IsIso (MarkedPresheaf.forget.map (ε.app Z)) :=
    inferInstanceAs (IsIso (𝟙 _))
  have h := congrArg MarkedPresheaf.forget.map
    (markedFaceNerveTensorComparison_naturality (ε.app X) (ε.app Y))
  rw [Functor.map_comp, Functor.map_comp] at h
  have : IsIso (MarkedPresheaf.forget.map (markedTensorMap false (ε.app X) (ε.app Y))) := by
    rw [forget_map_markedTensorMap]
    have := hε X
    have := hε Y
    have := (isIso_prod_iff (C := DiagSet.{u}) (D := DiagSet.{u})
      (f := (MarkedPresheaf.forget.map (ε.app X), MarkedPresheaf.forget.map (ε.app Y)))).2
      ⟨inferInstance, inferInstance⟩
    exact @Functor.map_isIso _ _ _ _ _ _ grayTensorBifunctor _ this
  have := isIso_forget_map_markedFaceNerve_map (markedTensorMap false (ε.app X) (ε.app Y))
  have := hε X
  have := hε Y
  have := isIso_forget_map_markedFaceNerve_map (ε.app X)
  have := isIso_forget_map_markedFaceNerve_map (ε.app Y)
  have h₂ : IsIso (MarkedPresheaf.forget.map
      (markedFaceNerve.map (ε.app X) ⊗ₘ markedFaceNerve.map (ε.app Y))) :=
    inferInstanceAs (IsIso (MarkedPresheaf.forget.map (markedFaceNerve.map (ε.app X)) ⊗ₘ
      MarkedPresheaf.forget.map (markedFaceNerve.map (ε.app Y)) : _ ⟶ (_ : SSet.{u})))
  have := isIso_markedFaceNerveTensorComparison_flat (MarkedPresheaf.forget.obj X)
    (MarkedPresheaf.forget.obj Y)
  have h₁ := Functor.map_isIso MarkedPresheaf.forget (markedFaceNerveTensorComparison
    ((MarkedPresheaf.flat atomMarking).obj (MarkedPresheaf.forget.obj X))
    ((MarkedPresheaf.flat atomMarking).obj (MarkedPresheaf.forget.obj Y)))
  have h₃ := (congrArg IsIso h).mpr (@IsIso.comp_isIso _ _ _ _ _ _ _ h₁ h₂)
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ _ h₃

section Edges

open SSet

section Product

variable {C : SSet.{u}} (x : C _⦋1⦌)

private theorem δ₂_σ₁ : C.δ 2 (C.σ 1 x) = x := δ_comp_σ_succ_apply (i := 1) x
private theorem δ₂_σ₀ : C.δ 2 (C.σ 0 x) = C.σ 0 (C.δ 1 x) :=
  δ_comp_σ_of_gt_apply (i := 1) (j := 0) (by decide) x
private theorem δ₀_σ₁ : C.δ 0 (C.σ 1 x) = C.σ 0 (C.δ 0 x) :=
  δ_comp_σ_of_le_apply (i := 0) (j := 0) (by decide) x
private theorem δ₀_σ₀ : C.δ 0 (C.σ 0 x) = x := δ_comp_σ_self_apply (i := 0) x
private theorem δ₁_σ₁ : C.δ 1 (C.σ 1 x) = x := δ_comp_σ_self_apply (i := 1) x
private theorem δ₁_σ₀ : C.δ 1 (C.σ 0 x) = x := δ_comp_σ_succ_apply (i := 0) x

variable {C₁ C₂ F : SSet.{u}} (g : C₁ ⊗ C₂ ⟶ F)

private def InvAt (z : (C₁ ⊗ C₂ : SSet.{u}) _⦋1⦌) : Prop :=
  Nonempty (Edge.mk' (g.app _ z)).InvStruct

private theorem δ_app_pair (i : Fin 3) (x : C₁ _⦋2⦌) (y : C₂ _⦋2⦌) :
    F.δ i (g.app _ ((x, y) : (C₁ ⊗ C₂ : SSet.{u}) _⦋2⦌)) =
      g.app _ ((C₁.δ i x, C₂.δ i y) : (C₁ ⊗ C₂ : SSet.{u}) _⦋1⦌) :=
  (δ_naturality_apply g i _).symm

private theorem invAt_pair [F.Quasicategory] (e₁ : C₁ _⦋1⦌) (e₂ : C₂ _⦋1⦌)
    (h₁ : InvAt g (e₁, C₂.σ 0 (C₂.δ 1 e₂))) (h₂ : InvAt g (C₁.σ 0 (C₁.δ 0 e₁), e₂)) :
    InvAt g (e₁, e₂) := by
  have h := nonempty_invStruct_δ_one (g.app _ ((C₁.σ 1 e₁, C₂.σ 0 e₂) :
    (C₁ ⊗ C₂ : SSet.{u}) _⦋2⦌))
  rw [δ_app_pair, δ_app_pair, δ_app_pair, δ₂_σ₁, δ₂_σ₀, δ₀_σ₁, δ₀_σ₀, δ₁_σ₁, δ₁_σ₀] at h
  exact h h₁ h₂

private theorem invAt_left [F.Quasicategory] (e : C₁ _⦋1⦌) (β : C₂ _⦋1⦌)
    (h₁ : InvAt g (C₁.σ 0 (C₁.δ 1 e), β)) (h₂ : InvAt g (C₁.σ 0 (C₁.δ 0 e), β))
    (h₃ : InvAt g (e, C₂.σ 0 (C₂.δ 1 β))) : InvAt g (e, C₂.σ 0 (C₂.δ 0 β)) := by
  have hA := nonempty_invStruct_δ_one (g.app _ ((C₁.σ 1 e, C₂.σ 0 β) :
    (C₁ ⊗ C₂ : SSet.{u}) _⦋2⦌))
  have hB := nonempty_invStruct_δ_zero (g.app _ ((C₁.σ 0 e, C₂.σ 1 β) :
    (C₁ ⊗ C₂ : SSet.{u}) _⦋2⦌))
  rw [δ_app_pair, δ_app_pair, δ_app_pair, δ₂_σ₁, δ₂_σ₀, δ₀_σ₁, δ₀_σ₀, δ₁_σ₁, δ₁_σ₀] at hA
  rw [δ_app_pair, δ_app_pair, δ_app_pair, δ₂_σ₁, δ₂_σ₀, δ₀_σ₁, δ₀_σ₀, δ₁_σ₁, δ₁_σ₀] at hB
  exact hB h₁ (hA h₃ h₂)

private theorem invAt_right [F.Quasicategory] (e : C₂ _⦋1⦌) (β : C₁ _⦋1⦌)
    (h₁ : InvAt g (β, C₂.σ 0 (C₂.δ 1 e))) (h₂ : InvAt g (β, C₂.σ 0 (C₂.δ 0 e)))
    (h₃ : InvAt g (C₁.σ 0 (C₁.δ 1 β), e)) : InvAt g (C₁.σ 0 (C₁.δ 0 β), e) :=
  invAt_left ((β_ C₂ C₁).hom ≫ g) e β h₁ h₂ h₃

end Product

end Edges

private theorem exists_vertex_markedFaceNerve (X : MarkedDiagSet.{u})
    (b : (MarkedPresheaf.forget.obj (markedFaceNerve.obj X)).obj (op ⦋0⦌)) :
    ∃ (W : Atom) (t : ball.{u} W ⟶ MarkedPresheaf.forget.obj X)
      (x : (MarkedPresheaf.forget.obj (rdcFaceNerve.{u}.obj (atomToRDCpx.obj W))).obj (op ⦋0⦌)),
      (MarkedPresheaf.forget.map (yonedaCompFaceNerveIso.inv.app W ≫ faceNerve.map t ≫
        markedFaceNerve.map ((MarkedPresheaf.flatForgetAdjunction atomMarking).counit.app X))).app
          _ x = b := by
  have hc := isColimitOfPreserves markedFaceNerve ((MarkedPresheaf.yoneda atomMarking).denseAt X)
  obtain ⟨j, x, rfl⟩ := MarkedPresheaf.exists_forget_map_eq_of_isColimit hc b
  have h : MarkedPresheaf.forget.map
      ((MarkedPresheaf.yonedaCompExtendIso markedFaceNerveSite).hom.app j.left) ≫
        MarkedPresheaf.forget.map (markedFaceNerveCell (uliftYonedaEquiv j.hom.hom)) =
      MarkedPresheaf.forget.map (markedFaceNerve.map j.hom) := by
    rw [markedFaceNerveCell, ← Functor.map_comp]
    refine congrArg MarkedPresheaf.forget.map ((Iso.hom_inv_id_app_assoc
      (MarkedPresheaf.yonedaCompExtendIso markedFaceNerveSite) j.left _).trans ?_)
    exact congrArg markedFaceNerve.map (ObjectProperty.hom_ext _
      (uliftYonedaEquiv.symm_apply_apply j.hom.hom))
  let c : (MarkedPresheaf.underlying X).obj (op j.left.obj) :=
    X.obj.map (MarkedSite.toSelf j.left).op (uliftYonedaEquiv j.hom.hom)
  refine ⟨j.left.obj, uliftYonedaEquiv.symm c, (MarkedPresheaf.forget.map
    ((MarkedPresheaf.yonedaCompExtendIso markedFaceNerveSite).hom.app j.left)).app _ x, ?_⟩
  have h₂ := congrArg (fun f : markedFaceNerveSite.obj
      ((MarkedSite.unmarked atomMarking).obj j.left.obj) ⟶ markedFaceNerve.obj X =>
        (MarkedPresheaf.forget.map f).app (op ⦋0⦌)
    ((MarkedPresheaf.forget.map
      ((MarkedPresheaf.yonedaCompExtendIso markedFaceNerveSite).hom.app j.left)).app _ x))
    ((markedFaceNerveCell_map (MarkedSite.toSelf j.left) (uliftYonedaEquiv j.hom.hom)).symm.trans
      (markedFaceNerveCell_unmarked c))
  refine Eq.trans ?_ ((congrArg (fun f => f.app (op ⦋0⦌) x) h).trans rfl)
  exact h₂.symm

private noncomputable def atomVertexHom (W : Atom) (v : W.ogp) (hv : grade ℕ v = 0) :
    atomPoint ⟶ W :=
  have : IsIso (toAtomPoint (Atom.ofClosure W v)) :=
    isIso_toAtomPoint_of_dimension_eq_zero (by rw [Atom.dimension_ofClosure]; exact hv)
  inv (toAtomPoint _) ≫ Atom.closureIncl W v

private theorem eq_top_of_dimension_eq_zero {W : Atom} (hW : W.dimension = 0) (w : W.ogp) :
    w = W.top :=
  GradeOrder.eq_of_le_of_grade_le (W.le_top w) (by rw [← W.dimension_eq, hW]; omega)

private theorem atomVertexHom_apply (W : Atom) (v : W.ogp) (hv : grade ℕ v = 0)
    (d : atomPoint.ogp) :
    atomVertexHom W v hv d = v := by
  rw [atomVertexHom, ConcreteCategory.comp_apply]
  have hW : (Atom.ofClosure W v).dimension = 0 := by rw [Atom.dimension_ofClosure]; exact hv
  exact (congrArg (Atom.closureIncl W v) (eq_top_of_dimension_eq_zero hW _)).trans
    (Atom.closureIncl_top _ _)

private theorem subsingleton_markedFaceNerve_unit (n : SimplexCategoryᵒᵖ) :
    Subsingleton ((MarkedPresheaf.forget.obj (markedFaceNerve.obj markedTensorUnit.{u})).obj n) :=
  ⟨fun a b => by
    let e := MarkedPresheaf.forget.mapIso (yonedaCompFaceNerveIso.{u}.app atomPoint)
    rw [← Iso.hom_inv_id_app_apply e n a, ← Iso.hom_inv_id_app_apply e n b]
    refine congrArg _ (nerve.ext_of_isThin (funext fun i => ULift.ext _ _ ?_))
    exact (eq_top_of_dimension_eq_zero dimension_atomPoint _).trans
      (eq_top_of_dimension_eq_zero dimension_atomPoint _).symm⟩

private theorem exists_edge_markedFaceNerve (X : MarkedDiagSet.{u})
    (b : (MarkedPresheaf.forget.obj (markedFaceNerve.obj X)).obj (op ⦋0⦌)) :
    ∃ (φ : markedTensorUnit ⟶ X)
      (p : (MarkedPresheaf.forget.obj (markedFaceNerve.obj markedTensorUnit.{u})).obj (op ⦋0⦌))
      (β : (MarkedPresheaf.forget.obj (markedFaceNerve.obj
        ((MarkedPresheaf.flat atomMarking).obj (MarkedPresheaf.forget.obj X)))).obj (op ⦋1⦌)),
      β ∈ (markedFaceNerve.obj
        ((MarkedPresheaf.flat atomMarking).obj (MarkedPresheaf.forget.obj X))).marked ⦋1⦌ ∧
      SimplicialObject.δ (MarkedPresheaf.forget.obj (markedFaceNerve.obj X) : SSet.{u}) 1
        ((MarkedPresheaf.forget.map (markedFaceNerve.map
          ((MarkedPresheaf.flatForgetAdjunction atomMarking).counit.app X))).app _ β) =
          (MarkedPresheaf.forget.map (markedFaceNerve.map φ)).app _ p ∧
      SimplicialObject.δ (MarkedPresheaf.forget.obj (markedFaceNerve.obj X) : SSet.{u}) 0
        ((MarkedPresheaf.forget.map (markedFaceNerve.map
          ((MarkedPresheaf.flatForgetAdjunction atomMarking).counit.app X))).app _ β) = b := by
  let ε := (MarkedPresheaf.flatForgetAdjunction atomMarking).counit.app X
  obtain ⟨W, t, x, rfl⟩ := exists_vertex_markedFaceNerve X b
  let w := (x.obj 0).down
  obtain ⟨v, hvmin, hbd⟩ :=
    Molecule.OGP.exists_boundary_zero_eq_Iic (P := W.ogp) (U := .Iic w) (W.isRDC w) true
  have hv : grade ℕ v = 0 := grade_eq_zero_iff.2 hvmin
  have hvw : v ≤ w := by
    have hm : v ∈ W.ogp.boundary (.Iic w) 0 true := by
      rw [hbd]
      exact LowerSet.mem_Iic_iff.2 le_rfl
    exact LowerSet.mem_Iic_iff.1 (Molecule.OGP.boundary_le _ 0 true hm)
  let κ := atomVertexHom W v hv
  let ι := yonedaCompFaceNerveIso.{u}.inv
  let E : (nerve (ULift.{u} W.ogp)) _⦋1⦌ :=
    ComposableArrows.mk₁ (homOfLE (show (ULift.up v : ULift.{u} W.ogp) ≤ ULift.up w from hvw))
  have hE : E ∈ (rdcFaceNerve.{u}.obj (atomToRDCpx.obj W)).marked ⦋1⦌ :=
    (MarkedPresheaf.mem_marked_ofMarking _ _ _ _).2
      ⟨rfl, Or.inl ((Molecule.OGP.boundary_Iic_of_isMin hvmin 0 true).trans hbd.symm)⟩
  refine ⟨(MarkedPresheaf.flat atomMarking).map (uliftYoneda.map κ ≫ t) ≫ ε,
    (MarkedPresheaf.forget.map (ι.app atomPoint)).app _
      (ComposableArrows.mk₀ (ULift.up atomPoint.top)),
    (MarkedPresheaf.forget.map (ι.app W ≫ faceNerve.map t)).app _ E,
    MarkedPresheaf.map_mem_marked _ hE, ?_, ?_⟩
  · have hδ : (nerve (ULift.{u} W.ogp)).δ 1 E = ComposableArrows.mk₀ (ULift.up v) :=
      ComposableArrows.ext₀ rfl
    have hm : (MarkedPresheaf.forget.map ((atomToRDCpx ⋙ rdcFaceNerve.{u}).map κ)).app (op ⦋0⦌)
        (ComposableArrows.mk₀ (ULift.up atomPoint.top)) = ComposableArrows.mk₀ (ULift.up v) :=
      (nerveMap_app_mk₀ _ _).trans (congrArg _ (ULift.ext _ _ (atomVertexHom_apply W v hv _)))
    have hκ := (congrArg (fun f : (atomToRDCpx ⋙ rdcFaceNerve.{u}).obj atomPoint ⟶
        (uliftYoneda ⋙ faceNerve).obj W => (MarkedPresheaf.forget.map f).app (op ⦋0⦌)
          (ComposableArrows.mk₀ (ULift.up atomPoint.top))) (ι.naturality κ)).symm.trans
      (congrArg ((MarkedPresheaf.forget.map (ι.app W)).app (op ⦋0⦌)) hm)
    have hφ : markedFaceNerve.map ((MarkedPresheaf.flat atomMarking).map (uliftYoneda.map κ ≫ t) ≫
        ε) = (faceNerve.map (uliftYoneda.map κ) ≫ faceNerve.map t) ≫ markedFaceNerve.map ε :=
      (markedFaceNerve.map_comp _ _).trans (congrArg (· ≫ _) (faceNerve.map_comp _ _))
    refine (SSet.δ_naturality_apply _ 1 _).symm.trans ?_
    refine (congrArg _ (SSet.δ_naturality_apply (MarkedPresheaf.forget.map
      (ι.app W ≫ faceNerve.map t)) 1 E).symm).trans ?_
    refine (congrArg (fun z => (MarkedPresheaf.forget.map (markedFaceNerve.map ε)).app _
      ((MarkedPresheaf.forget.map (ι.app W ≫ faceNerve.map t)).app _ z)) hδ).trans ?_
    refine (congrArg (fun z => (MarkedPresheaf.forget.map (markedFaceNerve.map ε)).app _
      ((MarkedPresheaf.forget.map (faceNerve.map t)).app _ z)) hκ.symm).trans ?_
    exact (congrArg (fun f => (MarkedPresheaf.forget.map f).app (op ⦋0⦌)
      ((MarkedPresheaf.forget.map (ι.app atomPoint)).app (op ⦋0⦌)
        (ComposableArrows.mk₀ (ULift.up atomPoint.top)))) hφ).symm
  · refine (SSet.δ_naturality_apply _ 0 _).symm.trans ?_
    refine (congrArg _ (SSet.δ_naturality_apply (MarkedPresheaf.forget.map
      (ι.app W ≫ faceNerve.map t)) 0 E).symm).trans ?_
    exact congrArg (fun z => (MarkedPresheaf.forget.map (ι.app W ≫ faceNerve.map t ≫
      markedFaceNerve.map ε)).app _ z) (ComposableArrows.ext₀ rfl)

private theorem markedTensorRightUnitor_inv_fst (X : MarkedDiagSet.{u}) :
    (markedTensorRightUnitor false X).inv ≫ markedTensorFst false X markedTensorUnit = 𝟙 X := by
  refine MarkedPresheaf.hom_ext ?_
  refine (MarkedPresheaf.forget.map_comp _ _).trans ?_
  refine Eq.trans ?_ (MarkedPresheaf.forget.map_id X).symm
  rw [forget_map_markedTensorRightUnitor_inv]
  refine Eq.trans ?_ (GrayDiagSet.rightUnitor (MarkedPresheaf.forget.obj X)).inv_hom_id
  have h : MarkedPresheaf.forget.map (markedTensorFst false X markedTensorUnit) =
      grayTensorFst _ _ := rfl
  have hf : isTerminalBallAtomPoint.from (MarkedPresheaf.forget.obj markedTensorUnit.{u}) =
      𝟙 (ball atomPoint) := isTerminalBallAtomPoint.hom_ext _ _
  rw [h, grayTensorFst]
  exact congrArg _ ((congrArg (fun f => grayTensorBifunctor.map (𝟙 _, f) ≫ _) hf).trans
    ((congrArg (· ≫ _) (grayTensorBifunctor.map_id (_, _))).trans (Category.id_comp _)))

private theorem markedTensorLeftUnitor_inv_snd (Y : MarkedDiagSet.{u}) :
    (markedTensorLeftUnitor false Y).inv ≫ markedTensorSnd false markedTensorUnit Y = 𝟙 Y := by
  refine MarkedPresheaf.hom_ext ?_
  refine (MarkedPresheaf.forget.map_comp _ _).trans ?_
  refine Eq.trans ?_ (MarkedPresheaf.forget.map_id Y).symm
  rw [forget_map_markedTensorLeftUnitor_inv]
  refine Eq.trans ?_ (GrayDiagSet.leftUnitor (MarkedPresheaf.forget.obj Y)).inv_hom_id
  have h : MarkedPresheaf.forget.map (markedTensorSnd false markedTensorUnit Y) =
      grayTensorSnd _ _ := rfl
  have hf : isTerminalBallAtomPoint.from (MarkedPresheaf.forget.obj markedTensorUnit.{u}) =
      𝟙 (ball atomPoint) := isTerminalBallAtomPoint.hom_ext _ _
  rw [h, grayTensorSnd]
  exact congrArg _ ((congrArg (fun f => grayTensorBifunctor.map (f, 𝟙 _) ≫ _) hf).trans
    ((congrArg (· ≫ _) (grayTensorBifunctor.map_id (_, _))).trans (Category.id_comp _)))

section Inverting

variable {X Y : MarkedDiagSet.{u}} {F : SSet.{u}}
  (g : MarkedPresheaf.forget.obj (markedFaceNerve.obj X ⊗ markedFaceNerve.obj Y) ⟶ F)

private abbrev Inv (z : (MarkedPresheaf.forget.obj (markedFaceNerve.obj X) ⊗
    MarkedPresheaf.forget.obj (markedFaceNerve.obj Y) : SSet.{u}) _⦋1⦌) : Prop :=
  InvAt (C₁ := MarkedPresheaf.forget.obj (markedFaceNerve.obj X))
    (C₂ := MarkedPresheaf.forget.obj (markedFaceNerve.obj Y)) g z

private def InvertsMarked : Prop :=
  ∀ e ∈ (markedFaceNerve.obj (markedGrayTensor X Y)).marked ⦋1⦌,
    Inv g ((MarkedPresheaf.forget.map (markedFaceNerveTensorComparison X Y)).app _ e)

private noncomputable abbrev ε (Z : MarkedDiagSet.{u}) :
    (MarkedPresheaf.flat atomMarking).obj (MarkedPresheaf.forget.obj Z) ⟶ Z :=
  (MarkedPresheaf.flatForgetAdjunction atomMarking).counit.app Z

private theorem inv_flat (hg : InvertsMarked g) (e₁ e₂)
    (he₁ : e₁ ∈ (faceNerve.obj (MarkedPresheaf.forget.obj X)).marked ⦋1⦌)
    (he₂ : e₂ ∈ (faceNerve.obj (MarkedPresheaf.forget.obj Y)).marked ⦋1⦌) :
    Inv g ((MarkedPresheaf.forget.map (markedFaceNerve.map (ε X))).app _ e₁,
      (MarkedPresheaf.forget.map (markedFaceNerve.map (ε Y))).app _ e₂) := by
  let c := markedFaceNerveTensorComparison ((MarkedPresheaf.flat atomMarking).obj
    (MarkedPresheaf.forget.obj X)) ((MarkedPresheaf.flat atomMarking).obj
      (MarkedPresheaf.forget.obj Y))
  have hp : ((e₁, e₂) : (MarkedPresheaf.forget.obj (faceNerve.obj (MarkedPresheaf.forget.obj X) ⊗
      faceNerve.obj (MarkedPresheaf.forget.obj Y))).obj (op ⦋1⦌)) ∈
        (faceNerve.obj (MarkedPresheaf.forget.obj X) ⊗
          faceNerve.obj (MarkedPresheaf.forget.obj Y)).marked ⦋1⦌ :=
    (MarkedSSet.mem_marked_tensor_iff _ _ _).2 ⟨he₁, he₂⟩
  refine (congrArg (Inv g) ?_).mp (hg _ (MarkedPresheaf.map_mem_marked
    (markedFaceNerve.map (markedTensorMap false (ε X) (ε Y)))
      (MarkedPresheaf.map_mem_marked (inv c) hp)))
  refine (congrArg (fun f => (MarkedPresheaf.forget.map f).app (op ⦋1⦌)
    ((MarkedPresheaf.forget.map (inv c)).app _ (e₁, e₂)))
    (markedFaceNerveTensorComparison_naturality (ε X) (ε Y))).trans ?_
  exact congrArg ((MarkedPresheaf.forget.map (markedFaceNerve.map (ε X) ⊗ₘ
    markedFaceNerve.map (ε Y))).app _) (congrArg (fun f : faceNerve.obj
      (MarkedPresheaf.forget.obj X) ⊗ faceNerve.obj (MarkedPresheaf.forget.obj Y) ⟶ _ =>
        (MarkedPresheaf.forget.map f).app (op ⦋1⦌) ((e₁, e₂) : (MarkedPresheaf.forget.obj
          (faceNerve.obj (MarkedPresheaf.forget.obj X) ⊗
            faceNerve.obj (MarkedPresheaf.forget.obj Y))).obj (op ⦋1⦌))) (IsIso.inv_hom_id c))

private theorem inv_unit_left (hg : InvertsMarked g) (e)
    (he : e ∈ (markedFaceNerve.obj X).marked ⦋1⦌) (φ : markedTensorUnit ⟶ Y) (p) :
    Inv g (e, SimplicialObject.σ (MarkedPresheaf.forget.obj (markedFaceNerve.obj Y) : SSet.{u}) 0
      ((MarkedPresheaf.forget.map (markedFaceNerve.map φ)).app (op ⦋0⦌) p)) := by
  let l := (markedTensorRightUnitor false X).inv ≫ markedTensorMap false (𝟙 X) φ
  refine (congrArg (Inv g) (Prod.ext ?_ ?_)).mp (hg _ (MarkedPresheaf.map_mem_marked
    (markedFaceNerve.map l) he))
  · have h : l ≫ markedTensorFst false X Y = 𝟙 X :=
      (Category.assoc _ _ _).trans ((congrArg _ (markedTensorMap_markedTensorFst _ _)).trans
        ((Category.assoc _ _ _).symm.trans ((Category.comp_id _).trans
          (markedTensorRightUnitor_inv_fst X))))
    exact congrArg (fun f => (MarkedPresheaf.forget.map f).app (op ⦋1⦌) e)
      ((markedFaceNerve.map_comp _ _).symm.trans ((congrArg _ h).trans
        (markedFaceNerve.map_id _)))
  · have h : l ≫ markedTensorSnd false X Y =
        ((markedTensorRightUnitor false X).inv ≫ markedTensorSnd false X _) ≫ φ :=
      (Category.assoc _ _ _).trans ((congrArg _ (markedTensorMap_markedTensorSnd _ _)).trans
        (Category.assoc _ _ _).symm)
    refine (congrArg (fun f => (MarkedPresheaf.forget.map f).app (op ⦋1⦌) e)
      ((markedFaceNerve.map_comp _ _).symm.trans ((congrArg _ h).trans
        (markedFaceNerve.map_comp _ _)))).trans ?_
    refine Eq.trans ?_ (SSet.σ_naturality_apply _ 0 p)
    exact congrArg _ ((subsingleton_markedFaceNerve_unit _).elim _ _)

private theorem inv_unit_right (hg : InvertsMarked g) (e)
    (he : e ∈ (markedFaceNerve.obj Y).marked ⦋1⦌) (φ : markedTensorUnit ⟶ X) (p) :
    Inv g (SimplicialObject.σ (MarkedPresheaf.forget.obj (markedFaceNerve.obj X) : SSet.{u}) 0
      ((MarkedPresheaf.forget.map (markedFaceNerve.map φ)).app (op ⦋0⦌) p), e) := by
  let l := (markedTensorLeftUnitor false Y).inv ≫ markedTensorMap false φ (𝟙 Y)
  refine (congrArg (Inv g) (Prod.ext ?_ ?_)).mp (hg _ (MarkedPresheaf.map_mem_marked
    (markedFaceNerve.map l) he))
  · have h : l ≫ markedTensorFst false X Y =
        ((markedTensorLeftUnitor false Y).inv ≫ markedTensorFst false _ Y) ≫ φ :=
      (Category.assoc _ _ _).trans ((congrArg _ (markedTensorMap_markedTensorFst _ _)).trans
        (Category.assoc _ _ _).symm)
    refine (congrArg (fun f => (MarkedPresheaf.forget.map f).app (op ⦋1⦌) e)
      ((markedFaceNerve.map_comp _ _).symm.trans ((congrArg _ h).trans
        (markedFaceNerve.map_comp _ _)))).trans ?_
    refine Eq.trans ?_ (SSet.σ_naturality_apply _ 0 p)
    exact congrArg _ ((subsingleton_markedFaceNerve_unit _).elim _ _)
  · have h : l ≫ markedTensorSnd false X Y = 𝟙 Y :=
      (Category.assoc _ _ _).trans ((congrArg _ (markedTensorMap_markedTensorSnd _ _)).trans
        ((Category.assoc _ _ _).symm.trans ((Category.comp_id _).trans
          (markedTensorLeftUnitor_inv_snd Y))))
    exact congrArg (fun f => (MarkedPresheaf.forget.map f).app (op ⦋1⦌) e)
      ((markedFaceNerve.map_comp _ _).symm.trans ((congrArg _ h).trans
        (markedFaceNerve.map_id _)))

private theorem exists_counit_apply_eq (Z : MarkedDiagSet.{u}) (n : SimplexCategoryᵒᵖ)
    (z : (MarkedPresheaf.forget.obj (markedFaceNerve.obj Z)).obj n) :
    ∃ z', (MarkedPresheaf.forget.map (markedFaceNerve.map (ε Z))).app n z' = z := by
  have : IsIso (MarkedPresheaf.forget.map (ε Z)) := inferInstanceAs (IsIso (𝟙 _))
  have := isIso_forget_map_markedFaceNerve_map (ε Z)
  exact ⟨(inv (MarkedPresheaf.forget.map (markedFaceNerve.map (ε Z)))).app n z,
    congrArg (fun f : MarkedPresheaf.forget.obj (markedFaceNerve.obj Z) ⟶
      MarkedPresheaf.forget.obj (markedFaceNerve.obj Z) => f.app n z) (IsIso.inv_hom_id _)⟩

private theorem inv_of_mem_marked [F.Quasicategory] (hg : InvertsMarked g) (e)
    (he : e ∈ (markedFaceNerve.obj X ⊗ markedFaceNerve.obj Y).marked ⦋1⦌) : Inv g e := by
  have hl (a) (β) (hβ : β ∈ (faceNerve.obj (MarkedPresheaf.forget.obj Y)).marked ⦋1⦌) :
      Inv g (SimplicialObject.σ (MarkedPresheaf.forget.obj (markedFaceNerve.obj X) : SSet.{u}) 0 a,
        (MarkedPresheaf.forget.map (markedFaceNerve.map (ε Y))).app _ β) := by
    obtain ⟨a', rfl⟩ := exists_counit_apply_eq X _ a
    exact (congrArg (fun z => Inv g (z, (MarkedPresheaf.forget.map
      (markedFaceNerve.map (ε Y))).app _ β)) (SSet.σ_naturality_apply
        (MarkedPresheaf.forget.map (markedFaceNerve.map (ε X))) 0 a')).mp
      (inv_flat g hg (SimplicialObject.σ (MarkedPresheaf.forget.obj
        (faceNerve.obj (MarkedPresheaf.forget.obj X)) : SSet.{u}) 0 a') β
          (MarkedSSet.map_σ_mem_marked _ a') hβ)
  have hr (β) (hβ : β ∈ (faceNerve.obj (MarkedPresheaf.forget.obj X)).marked ⦋1⦌) (b) :
      Inv g ((MarkedPresheaf.forget.map (markedFaceNerve.map (ε X))).app _ β,
        SimplicialObject.σ (MarkedPresheaf.forget.obj (markedFaceNerve.obj Y) : SSet.{u}) 0 b) := by
    obtain ⟨b', rfl⟩ := exists_counit_apply_eq Y _ b
    exact (congrArg (fun z => Inv g ((MarkedPresheaf.forget.map
      (markedFaceNerve.map (ε X))).app _ β, z)) (SSet.σ_naturality_apply
        (MarkedPresheaf.forget.map (markedFaceNerve.map (ε Y))) 0 b')).mp
      (inv_flat g hg β (SimplicialObject.σ (MarkedPresheaf.forget.obj
        (faceNerve.obj (MarkedPresheaf.forget.obj Y)) : SSet.{u}) 0 b') hβ
          (MarkedSSet.map_σ_mem_marked _ b'))
  obtain ⟨e₁, e₂⟩ := e
  obtain ⟨he₁, he₂⟩ := (MarkedSSet.mem_marked_tensor_iff _ _ _).1 he
  refine invAt_pair (C₁ := MarkedPresheaf.forget.obj (markedFaceNerve.obj X))
    (C₂ := MarkedPresheaf.forget.obj (markedFaceNerve.obj Y)) g e₁ e₂ ?_ ?_
  · obtain ⟨φ, p, β, hβ, h₁, h₂⟩ := exists_edge_markedFaceNerve Y
      (SimplicialObject.δ (MarkedPresheaf.forget.obj (markedFaceNerve.obj Y) : SSet.{u}) 1 e₂)
    have := invAt_left (C₁ := MarkedPresheaf.forget.obj (markedFaceNerve.obj X))
      (C₂ := MarkedPresheaf.forget.obj (markedFaceNerve.obj Y)) g e₁ _ (hl _ β hβ) (hl _ β hβ)
      (by rw [h₁]; exact inv_unit_left g hg e₁ he₁ φ p)
    rwa [h₂] at this
  · obtain ⟨φ, p, β, hβ, h₁, h₂⟩ := exists_edge_markedFaceNerve X
      (SimplicialObject.δ (MarkedPresheaf.forget.obj (markedFaceNerve.obj X) : SSet.{u}) 0 e₁)
    have := invAt_right (C₁ := MarkedPresheaf.forget.obj (markedFaceNerve.obj X))
      (C₂ := MarkedPresheaf.forget.obj (markedFaceNerve.obj Y)) g e₂ _ (hr β hβ _) (hr β hβ _)
      (by rw [h₁]; exact inv_unit_right g hg e₂ he₂ φ p)
    rwa [h₂] at this

end Inverting

open MarkedSSet.modelCategoryCartesian in
theorem weakEquivalence_markedFaceNerveTensorComparison (X Y : MarkedDiagSet.{u}) :
    WeakEquivalence (markedFaceNerveTensorComparison X Y) :=
  Atoms.Homotopical.weakEquivalence_of_isIso_forget_map _ fun _ _ g hg =>
    inv_of_mem_marked g hg

open MarkedSSet.modelCategoryCartesian SSet.modelCategoryJoyal in
theorem MarkedDiagSet.Coinductive.isQuillenEquivalence_markedFaceNerveAdjunction :
    MarkedDiagSet.Coinductive.markedFaceNerveAdjunction.{u}.IsQuillenEquivalence :=
  isQuillen_markedFaceNerveAdjunction.isQuillenEquivalence_of_comp
    (isQuillenEquivalence_flatForgetAdjunction 1) isQuillenEquivalence_faceNerveAdjunction

open MarkedSSet.modelCategoryCartesian in
theorem weakEquivalence_markedFaceNerve_map_pushoutProduct {X₁ Y₁ X₂ Y₂ : MarkedDiagSet.{u}}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) [Mono f₁] [Mono f₂]
    (h : WeakEquivalence (markedFaceNerve.map f₁) ∨ WeakEquivalence (markedFaceNerve.map f₂)) :
    WeakEquivalence (markedFaceNerve.map (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} false)) f₁ f₂).ι) := by
  let sq := Functor.PushoutObjObj.ofHasPushout
    (Functor.curry.obj (markedTensorBifunctor.{u} false)) f₁ f₂
  let sq' := Functor.PushoutObjObj.ofHasPushout (curriedTensor MarkedSSet.{u})
    (markedFaceNerve.map f₁) (markedFaceNerve.map f₂)
  let N := markedFaceNerve.{u}
  let c := markedFaceNerveTensorComparison.{u}
  have hN : IsPushout (N.map (markedTensorMap false f₁ (𝟙 X₂)))
      (N.map (markedTensorMap false (𝟙 X₁) f₂)) (N.map sq.inl) (N.map sq.inr) :=
    sq.isPushout.map N
  have h₁ : N.map (markedTensorMap false f₁ (𝟙 X₂)) ≫ c Y₁ X₂ =
      c X₁ X₂ ≫ (N.map f₁ ⊗ₘ 𝟙 (N.obj X₂)) :=
    (markedFaceNerveTensorComparison_naturality f₁ (𝟙 X₂)).trans
      (congrArg (fun g => c X₁ X₂ ≫ (N.map f₁ ⊗ₘ g)) (N.map_id X₂))
  have h₂ : N.map (markedTensorMap false (𝟙 X₁) f₂) ≫ c X₁ Y₂ =
      c X₁ X₂ ≫ (𝟙 (N.obj X₁) ⊗ₘ N.map f₂) :=
    (markedFaceNerveTensorComparison_naturality (𝟙 X₁) f₂).trans
      (congrArg (fun g => c X₁ X₂ ≫ (g ⊗ₘ N.map f₂)) (N.map_id X₁))
  have hc (X Y : MarkedDiagSet.{u}) : weakEquivalences MarkedSSet.{u} (c X Y) :=
    (weakEquivalence_iff _).1 (weakEquivalence_markedFaceNerveTensorComparison X Y)
  let χ : N.obj sq.pt ⟶ sq'.pt :=
    hN.desc (c Y₁ X₂ ≫ sq'.inl) (c X₁ Y₂ ≫ sq'.inr) (by
      rw [reassoc_of% h₁, reassoc_of% h₂]
      exact congrArg (c X₁ X₂ ≫ ·) sq'.isPushout.w)
  have : Mono (N.map (markedTensorMap false (𝟙 X₁) f₂)) := N.map_mono _
  have : Mono (𝟙 (N.obj X₁) ⊗ₘ N.map f₂) := inferInstanceAs (Mono (N.obj X₁ ◁ N.map f₂))
  have hχ : weakEquivalences MarkedSSet.{u} χ :=
    cartesianCylinder.{u}.weakEquivalences_of_isPushout_of_mono
      cartesianGenerators_le_monomorphisms hN.flip sq'.isPushout.flip
      (c X₁ X₂) (c X₁ Y₂) (c Y₁ X₂) χ h₂ h₁ (hN.inr_desc _ _ _) (hN.inl_desc _ _ _)
      (hc _ _) (hc _ _) (hc _ _)
  have hsq : N.map sq.ι ≫ c Y₁ Y₂ = χ ≫ sq'.ι := by
    refine hN.hom_ext ?_ ?_
    · refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ c Y₁ Y₂)
        ((N.map_comp _ _).symm.trans (congrArg N.map sq.inl_ι))).trans ?_)
      refine ((markedFaceNerveTensorComparison_naturality (𝟙 Y₁) f₂).trans
        (congrArg (fun g => c Y₁ X₂ ≫ (g ⊗ₘ N.map f₂)) (N.map_id Y₁))).trans ?_
      exact Eq.symm ((congrArg (· ≫ sq'.ι) (hN.inl_desc _ _ _)).trans
        ((Category.assoc _ _ _).trans (congrArg _ sq'.inl_ι)))
    · refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ c Y₁ Y₂)
        ((N.map_comp _ _).symm.trans (congrArg N.map sq.inr_ι))).trans ?_)
      refine ((markedFaceNerveTensorComparison_naturality f₁ (𝟙 Y₂)).trans
        (congrArg (fun g => c X₁ Y₂ ≫ (N.map f₁ ⊗ₘ g)) (N.map_id Y₂))).trans ?_
      exact Eq.symm ((congrArg (· ≫ sq'.ι) (hN.inr_desc _ _ _)).trans
        ((Category.assoc _ _ _).trans (congrArg _ sq'.inr_ι)))
  have : Mono (Arrow.mk (N.map f₁)).hom := N.map_mono f₁
  have : Mono (Arrow.mk (N.map f₂)).hom := N.map_mono f₂
  have hbox := (weakEquivalence_iff _).1
    (MarkedSSet.weakEquivalence_pushoutProduct (Arrow.mk (N.map f₁)) (Arrow.mk (N.map f₂)) h)
  rw [weakEquivalence_iff]
  exact (weakEquivalences MarkedSSet.{u}).of_postcomp _ (c Y₁ Y₂) (hc _ _)
    (hsq ▸ (weakEquivalences MarkedSSet.{u}).comp_mem _ _ hχ hbox)

open MarkedSSet.modelCategoryCartesian in
private theorem weakEquivalence_markedFaceNerve_map {A B : MarkedDiagSet.{u}} (f : A ⟶ B) [Mono f]
    (hf : WeakEquivalence ((MarkedDiagSet.toCoinductive 1).map f)) :
    WeakEquivalence (markedFaceNerve.map f) :=
  (weakEquivalence_iff _).2 (isQuillen_markedFaceNerveAdjunction.trivialCofibrations_le
    ((MarkedDiagSet.toCoinductive 1).map f)
    ⟨MorphismProperty.monomorphisms.infer_property f, (weakEquivalence_iff _).1 hf⟩).2

open MarkedSSet.modelCategoryCartesian in
theorem MarkedDiagSet.Coinductive.weakEquivalence_toCoinductive_one_pushoutProduct
    {X₁ Y₁ X₂ Y₂ : MarkedDiagSet.{u}} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) [Mono f₁] [Mono f₂]
    (h : WeakEquivalence ((MarkedDiagSet.toCoinductive 1).map f₁) ∨
      WeakEquivalence ((MarkedDiagSet.toCoinductive 1).map f₂)) :
    WeakEquivalence ((MarkedDiagSet.toCoinductive 1).map (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} false)) f₁ f₂).ι) :=
  ((isQuillen_markedFaceNerveAdjunction.isQuillenEquivalence_iff_of_isCofibrant).1
    MarkedDiagSet.Coinductive.isQuillenEquivalence_markedFaceNerveAdjunction).1 _
    (weakEquivalence_markedFaceNerve_map_pushoutProduct f₁ f₂
      (h.imp (weakEquivalence_markedFaceNerve_map f₁) (weakEquivalence_markedFaceNerve_map f₂)))

theorem MarkedDiagSet.Coinductive.weakEquivalence_toCoinductive_one_pseudoPushoutProduct
    {X₁ Y₁ X₂ Y₂ : MarkedDiagSet.{u}} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) [Mono f₁] [Mono f₂]
    (h : WeakEquivalence ((MarkedDiagSet.toCoinductive 1).map f₁) ∨
      WeakEquivalence ((MarkedDiagSet.toCoinductive 1).map f₂)) :
    WeakEquivalence ((MarkedDiagSet.toCoinductive 1).map (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} true)) f₁ f₂).ι) :=
  (weakEquivalence_pseudoPushoutProduct_iff 1 le_rfl f₁ f₂).2
    (weakEquivalence_toCoinductive_one_pushoutProduct f₁ f₂ h)

private theorem hasLiftingProperty_markedHomRight_pullbackObjObj
    {K L A B X Y : MarkedDiagSet.{u}} (j : K ⟶ L) (i : A ⟶ B) (p : X ⟶ Y)
    (h : HasLiftingProperty (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} false)) j i).ι p) :
    HasLiftingProperty j
      (Functor.PullbackObjObj.ofHasPullback markedHomRightBifunctor.{u} i p).π :=
  (markedTensorRightParametrizedAdjunction.hasLiftingProperty_iff
    (Functor.PushoutObjObj.ofHasPushout _ j i).flip _).1 h

theorem fibration_toCoinductive_one_markedHomRight_pullbackObjObj {A B X Y : MarkedDiagSet.{u}}
    (i : A ⟶ B) [Mono i] (p : X ⟶ Y) [Fibration ((MarkedDiagSet.toCoinductive 1).map p)] :
    Fibration ((MarkedDiagSet.toCoinductive 1).map
      (Functor.PullbackObjObj.ofHasPullback markedHomRightBifunctor.{u} i p).π) := by
  rw [fibration_iff, ← trivialCofibrations_rlp]
  intro K L j hj
  have : @Mono MarkedDiagSet.{u} _ K L j := hj.1
  have hp := (fibration_iff ((MarkedDiagSet.toCoinductive 1).map p)).1 inferInstance
  rw [← trivialCofibrations_rlp] at hp
  exact hasLiftingProperty_markedHomRight_pullbackObjObj j i p (hp _
    ⟨mono_markedPushoutProduct j i, (weakEquivalence_iff _).1
      (MarkedDiagSet.Coinductive.weakEquivalence_toCoinductive_one_pushoutProduct j i
        (Or.inl ((weakEquivalence_iff _).2 hj.2)))⟩)

private noncomputable def isTerminalMarkedHomRight (K : MarkedDiagSet.{u}) :
    IsTerminal ((markedHomRight false K).obj (⊤_ MarkedDiagSet.{u})) :=
  have := (tensorRightAdjunction false K).rightAdjoint_preservesLimits
  terminalIsTerminal.isTerminalObj (markedHomRight false K) _

theorem fibration_toCoinductive_one_markedHomRestrict {A B : MarkedDiagSet.{u}} (i : A ⟶ B)
    [Mono i] {X : MarkedDiagSet.{u}} (hX : IsFibrant ((MarkedDiagSet.toCoinductive 1).obj X)) :
    Fibration ((MarkedDiagSet.toCoinductive 1).map ((markedHomRestrict i).app X)) := by
  have : Fibration ((MarkedDiagSet.toCoinductive 1).map (terminal.from X)) :=
    (isFibrant_iff_of_isTerminal _ terminalIsTerminal).1 hX
  let sq := Functor.PullbackObjObj.ofHasPullback markedHomRightBifunctor.{u} i (terminal.from X)
  have : IsIso sq.fst := sq.isPullback.isIso_fst_of_isIso
    (isIso_of_isTerminal (isTerminalMarkedHomRight B) (isTerminalMarkedHomRight A) _)
  have : Fibration ((MarkedDiagSet.toCoinductive 1).map sq.π) :=
    fibration_toCoinductive_one_markedHomRight_pullbackObjObj i (terminal.from X)
  have h : (MarkedDiagSet.toCoinductive 1).map ((markedHomRestrict i).app X) =
      (MarkedDiagSet.toCoinductive 1).map sq.π ≫ (MarkedDiagSet.toCoinductive 1).map sq.fst :=
    (congrArg _ sq.π_fst.symm).trans (Functor.map_comp _ _ _)
  have hfst : Fibration ((MarkedDiagSet.toCoinductive 1).map sq.fst) := inferInstance
  rw [h]
  exact (fibration_iff _).2 ((fibrations (MarkedDiagSet.Coinductive.{u} 1)).comp_mem _ _
    ((fibration_iff _).1 ‹_›) ((fibration_iff _).1 hfst))

end Atoms.Diagrammatic
