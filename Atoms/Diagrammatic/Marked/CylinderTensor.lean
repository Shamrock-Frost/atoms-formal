import Atoms.Diagrammatic.Marked.Cylinder
import Atoms.Diagrammatic.Marked.GrayTensorMonoidal
import Atoms.Diagrammatic.GrayCylinder.Tensor

open CategoryTheory Limits Opposite MonoidalCategory Atoms.Homotopical Atoms.Molecule
open Atoms.Molecule.OGP Atoms.Shape

universe u

namespace Atoms.Diagrammatic

attribute [local irreducible] grayTensorBifunctor GrayDiagSet.leftUnitor

theorem markable_atomGlobe_one : atomMarking.markable (atomGlobe 1) := by
  change 0 < (atomGlobe 1).dimension
  rw [dimension_atomGlobe]
  exact Nat.one_pos

noncomputable def markedInterval : MarkedDiagSet.{u} :=
  (MarkedPresheaf.yoneda atomMarking).obj (MarkedSite.marked (atomGlobe 1) markable_atomGlobe_one)

noncomputable def intervalBallIso :
    ball.{u} (atomGlobe 1) ≅ markedInterval.{u}.underlying :=
  ballIsoForgetYoneda (MarkedSite.marked (atomGlobe 1) markable_atomGlobe_one)

private noncomputable def intervalCell {A : Atom} (k : A ⟶ atomGlobe 1) :
    diagram markedInterval.{u}.underlying A :=
  intervalBallIso.hom.app (op A) (ULift.up k)

private theorem map_intervalCell {A A' : Atom} (f : A ⟶ A') (k : A' ⟶ atomGlobe 1) :
    markedInterval.{u}.underlying.map f.op (intervalCell k) = intervalCell (f ≫ k) :=
  (NatTrans.naturality_apply intervalBallIso.{u}.hom f.op
    (ULift.up.{u} k : ULift.{u} (A' ⟶ _))).symm

theorem intervalBallIso_top_mem_marked :
    intervalBallIso.{u}.hom.app (op (atomGlobe 1)) ⟨𝟙 (atomGlobe 1)⟩ ∈
      markedInterval.{u}.marked (atomGlobe 1) :=
  (mem_marked_yoneda_obj_iff _ _ _).2
    ⟨markable_atomGlobe_one, Or.inl ⟨rfl, inferInstanceAs (IsIso (𝟙 (atomGlobe 1)))⟩⟩

noncomputable def markedIntervalVertex (ε : Bool) : markedTensorUnit.{u} ⟶ markedInterval.{u} :=
  MarkedPresheaf.homMk (uliftYoneda.map (atomGlobeVertex ε) ≫ intervalBallIso.hom) fun V x hx =>
    MarkedDiagSet.mem_marked_of_isDegenerate _ (isDegenerate_app _
      ((MarkedDiagSet.mem_marked_flat_iff_isDegenerate _ V x).1 hx))

@[simp] theorem forget_map_markedIntervalVertex (ε : Bool) :
    MarkedPresheaf.forget.map (markedIntervalVertex.{u} ε) =
      uliftYoneda.map (atomGlobeVertex ε) ≫ intervalBallIso.hom := rfl

private noncomputable def markedCylinderForgetTensorIso :
    markedCylinder.{u} ⋙ MarkedPresheaf.forget ≅
      MarkedPresheaf.forget ⋙
        (Functor.curry.obj grayTensorBifunctor.{u}).obj markedInterval.{u}.underlying :=
  markedCylinderForgetIso ≪≫
    Functor.isoWhiskerLeft MarkedPresheaf.forget grayCylinderFunctorIsoGrayTensor ≪≫
      Functor.isoWhiskerLeft MarkedPresheaf.forget
        ((Functor.curry.obj grayTensorBifunctor).mapIso intervalBallIso)

private noncomputable def cylTensorIso (X : MarkedDiagSet.{u}) :
    (markedCylinder.obj X).underlying ≅ grayTensor markedInterval.underlying X.underlying :=
  markedCylinderForgetTensorIso.app X

private theorem cylTensorIso_hom_app_unitCell (X : MarkedDiagSet.{u}) {U : Atom}
    (y : diagram X.underlying U) :
    (cylTensorIso X).hom.app _ (markedCylinderUnitCell X y) =
      (grayTensor markedInterval.underlying X.underlying).map (cylAtomGrayTensorIso U).hom.op
        (grayTensorCell (intervalCell (𝟙 (atomGlobe 1))) y) := by
  change (grayTensorBifunctor.map (X := (ball (atomGlobe 1), X.underlying))
      (Y := (markedInterval.underlying, X.underlying)) (intervalBallIso.hom, 𝟙 X.underlying)).app _
        ((grayCylinderFunctorIsoGrayTensor.hom.app X.underlying).app _
          ((markedCylinderForgetIso.hom.app X).app _ (markedCylinderUnitCell X y))) = _
  rw [markedCylinderForgetIso_hom_app_unitCell,
    grayCylinderFunctorIsoGrayTensor_hom_app_grayCylinderUnit_app, NatTrans.naturality_apply]
  exact congrArg _ (grayTensorCell_naturality _ _ _ _)

private theorem forget_map_endpoint_comp_hom (pseudo ε : Bool) (X : MarkedDiagSet.{u}) :
    MarkedPresheaf.forget.map ((markedExactCylinder.endpoint ε).app X) ≫ (cylTensorIso X).hom =
      MarkedPresheaf.forget.map ((markedTensorLeftUnitor pseudo X).inv ≫
        markedTensorMap pseudo (markedIntervalVertex ε) (𝟙 X)) := by
  have h₁ : MarkedPresheaf.forget.map ((markedExactCylinder.endpoint ε).app X) ≫
      markedCylinderForgetIso.hom.app X = (grayCylinderEndpoint ε).app X.underlying :=
    NatTrans.congr_app (whiskerRight_endpoint_forget_comp_markedCylinderForgetIso_hom ε) X
  have h₃ : ((GrayDiagSet.leftUnitor X.underlying).inv ≫
      grayTensorBifunctor.map (X := (ball atomPoint, X.underlying))
        (Y := (ball (atomGlobe 1), X.underlying)) (uliftYoneda.map (atomGlobeVertex ε), 𝟙 _)) ≫
      grayTensorBifunctor.map (X := (ball (atomGlobe 1), X.underlying))
        (Y := (markedInterval.underlying, X.underlying)) (intervalBallIso.hom, 𝟙 X.underlying) =
      MarkedPresheaf.forget.map ((markedTensorLeftUnitor pseudo X).inv ≫
        markedTensorMap pseudo (markedIntervalVertex ε) (𝟙 X)) := by
    rw [Functor.map_comp, forget_map_markedTensorLeftUnitor_inv, forget_map_markedTensorMap,
      Category.assoc, ← Functor.map_comp, prod_comp, Category.comp_id,
      CategoryTheory.Functor.map_id]
    rfl
  exact (Category.assoc _ _ _).symm.trans ((h₁ =≫ _).trans ((Category.assoc _ _ _).symm.trans
    ((grayCylinderEndpoint_app_comp_grayCylinderFunctorIsoGrayTensor_hom_app ε X.underlying =≫
      _).trans h₃)))

private theorem cylTensorIso_hom_app_endpoint (pseudo ε : Bool) (X : MarkedDiagSet.{u}) {U : Atom}
    (m : diagram X.underlying U) :
    (cylTensorIso X).hom.app (op U)
        ((MarkedPresheaf.forget.map ((markedExactCylinder.endpoint ε).app X)).app (op U) m) =
      (MarkedPresheaf.forget.map ((markedTensorLeftUnitor pseudo X).inv ≫
        markedTensorMap pseudo (markedIntervalVertex ε) (𝟙 X))).app (op U) m :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (forget_map_endpoint_comp_hom pseudo ε X) (op U)) m

private theorem hom_app_mem_marked (pseudo : Bool) (X : MarkedDiagSet.{u}) {V : Atom}
    {c : (markedCylinder.obj X).underlying.obj (op V)} (hc : c ∈ (markedCylinder.obj X).marked V) :
    (cylTensorIso X).hom.app (op V) c ∈ (markedTensor pseudo markedInterval X).marked V := by
  rcases mem_marked_markedCylinder_obj_cases X hc with hd | ⟨U, y, e, rfl⟩ |
    ⟨ε, U, m, hm, e, rfl⟩
  · exact MarkedDiagSet.mem_marked_of_isDegenerate _ (isDegenerate_app _ hd)
  · have h : (cylTensorIso X).hom.app (op V)
        ((markedCylinder.obj X).underlying.map e.hom.op (markedCylinderUnitCell X y)) =
        (grayTensor markedInterval.underlying X.underlying).map
          (e ≪≫ cylAtomGrayTensorIso U).hom.op
            (grayTensorCell (intervalCell (𝟙 (atomGlobe 1))) y) := by
      rw [NatTrans.naturality_apply, cylTensorIso_hom_app_unitCell, ← Functor.map_comp_apply,
        ← op_comp]
      rfl
    exact (congrArg (· ∈ _) h).mpr ((mem_marked_markedTensor _ _ _ _ _).2 (Or.inr
      ⟨atomGlobe 1, U, _, y, e ≪≫ cylAtomGrayTensorIso U, Or.inl intervalBallIso_top_mem_marked,
        rfl⟩))
  · have h : (cylTensorIso X).hom.app (op V) ((markedCylinder.obj X).underlying.map e.hom.op
        ((MarkedPresheaf.forget.map ((markedExactCylinder.endpoint ε).app X)).app (op U) m)) =
        (grayTensor markedInterval.underlying X.underlying).map e.hom.op
          ((MarkedPresheaf.forget.map ((markedTensorLeftUnitor pseudo X).inv ≫
            markedTensorMap pseudo (markedIntervalVertex ε) (𝟙 X))).app (op U) m) :=
      (NatTrans.naturality_apply (cylTensorIso X).hom e.hom.op _).trans
        (congrArg _ (cylTensorIso_hom_app_endpoint pseudo ε X m))
    exact (congrArg (· ∈ _) h).mpr (((markedTensor pseudo markedInterval X).transport e _).1
      (MarkedPresheaf.map_mem_marked _ hm))

private theorem cylTensorIso_inv_app_grayTensorCell_top (X : MarkedDiagSet.{u}) {U : Atom}
    (y : diagram X.underlying U) :
    (cylTensorIso X).inv.app _
        (grayTensorCell (intervalCell (𝟙 (atomGlobe 1))) y) =
      (markedCylinder.obj X).underlying.map (cylAtomGrayTensorIso U).inv.op
        (markedCylinderUnitCell X y) := by
  refine Eq.trans ?_ (Iso.hom_inv_id_app_apply (cylTensorIso X) _ _)
  refine congrArg _ (Eq.symm ((NatTrans.naturality_apply (cylTensorIso X).hom _ _).trans
    ((congrArg _ (cylTensorIso_hom_app_unitCell X y)).trans ?_)))
  rw [← Functor.map_comp_apply, ← op_comp, Iso.inv_hom_id, op_id, Functor.map_id_apply]

private theorem cylTensorIso_inv_app_grayTensorCell_vertex (ε : Bool) (X : MarkedDiagSet.{u})
    {U : Atom} (y : diagram X.underlying U) :
    (cylTensorIso X).inv.app _
        (grayTensorCell (intervalCell (atomGlobeVertex ε)) y) =
      (markedCylinder.obj X).underlying.map (Atom.grayTensorLeftUnitor U).hom.op
        ((MarkedPresheaf.forget.map ((markedExactCylinder.endpoint ε).app X)).app (op U) y) := by
  refine Eq.trans ?_ (Iso.hom_inv_id_app_apply (cylTensorIso X) _ _)
  refine congrArg _ ?_
  let p : diagram (ball.{u} atomPoint) atomPoint := ULift.up (𝟙 atomPoint)
  have hp : grayTensorCell p y = (grayTensor (ball atomPoint) X.underlying).map
      (Atom.grayTensorLeftUnitor U).hom.op ((GrayDiagSet.leftUnitor X.underlying).inv.app _ y) := by
    have h0 := GrayDiagSet.leftUnitor_hom_app_grayTensorCell (X := X.underlying) p y
    rw [isTerminalAtomPoint.hom_ext (toAtomPoint atomPoint) (𝟙 _), Atom.grayTensorMap_id,
      Category.id_comp] at h0
    rw [← NatTrans.naturality_apply, ← h0, Iso.hom_inv_id_app_apply]
  refine Eq.trans ?_ ((NatTrans.naturality_apply (cylTensorIso X).hom _ _).trans
    (congrArg _ (cylTensorIso_hom_app_endpoint false ε X y))).symm
  refine Eq.trans ?_ (NatTrans.naturality_apply (grayTensorBifunctor.map
    (X := (ball atomPoint, X.underlying)) (Y := (markedInterval.underlying, X.underlying))
      (uliftYoneda.map (atomGlobeVertex ε) ≫ intervalBallIso.hom, 𝟙 X.underlying)) _ _)
  refine Eq.trans ?_ (congrArg _ hp)
  have hv : (uliftYoneda.map (atomGlobeVertex ε) ≫ intervalBallIso.hom).app (op atomPoint) p =
      intervalCell.{u} (atomGlobeVertex ε) :=
    congrArg intervalCell (Category.id_comp (atomGlobeVertex ε))
  exact ((grayTensorCell_naturality (uliftYoneda.map (atomGlobeVertex ε) ≫ intervalBallIso.hom)
    (𝟙 X.underlying) p y).trans (congrArg₂ grayTensorCell hv rfl)).symm

theorem exists_eq_atomGlobeVertex (j : atomPoint ⟶ atomGlobe 1) :
    ∃ ε : Bool, j = atomGlobeVertex ε := by
  have hg : grade ℕ (j atomPoint.top) = 0 := by
    have := (Atom.isMap j).grade_le atomPoint.top
    rw [← Atom.dimension_eq, dimension_atomPoint] at this
    omega
  rcases hw : (FiniteOGP.ofOGPIso (globe 1)).inv (j atomPoint.top) with ε | ⟨⟨⟩⟩
  · refine ⟨ε, Atom.hom_ext fun t => ?_⟩
    rw [atomGlobeVertex_apply, Subsingleton.elim t atomPoint.top, ← hw]
    exact (Iso.inv_hom_id_apply (FiniteOGP.ofOGPIso (globe 1)) (j atomPoint.top)).symm
  · have h := (isMorphism (FiniteOGP.ofOGPIso (globe 1)).inv).grade_eq (j atomPoint.top)
    rw [hw] at h
    exact absurd ((SuspCarrier.grade_susp _).symm.trans (h.trans hg)) (Nat.succ_ne_zero _)

private theorem inv_app_mem_marked (pseudo : Bool) (X : MarkedDiagSet.{u}) {V : Atom}
    {z : diagram (grayTensor markedInterval.underlying X.underlying) V}
    (hz : z ∈ (markedTensor pseudo markedInterval X).marked V) :
    (cylTensorIso X).inv.app (op V) z ∈ (markedCylinder.obj X).marked V := by
  rcases (mem_marked_markedTensor _ _ _ _ _).1 hz with hd | ⟨A, B, x, y, e, hm, rfl⟩
  · exact MarkedDiagSet.mem_marked_of_isDegenerate _ (isDegenerate_app _ hd)
  refine (congrArg (· ∈ _) (NatTrans.naturality_apply (cylTensorIso X).inv e.hom.op _)).mpr
    (((markedCylinder.obj X).transport e _).1 ?_)
  obtain ⟨k, rfl⟩ : ∃ k : A ⟶ atomGlobe 1, intervalCell.{u} k = x := ⟨x.down.1, rfl⟩
  have hrestrict : ∀ {A' : Atom} (f : A ⟶ A') (k' : A' ⟶ atomGlobe 1), f ≫ k' = k →
      (cylTensorIso X).inv.app _ (grayTensorCell (intervalCell.{u} k) y) =
        (markedCylinder.obj X).underlying.map (Atom.grayTensorMap f (𝟙 B)).op
          ((cylTensorIso X).inv.app _ (grayTensorCell (intervalCell k') y)) := by
    intro A' f k' hfk
    refine Eq.trans (congrArg _ ?_) (NatTrans.naturality_apply (cylTensorIso X).inv _ _)
    refine Eq.trans ?_ (grayTensorCell_restrict f (𝟙 B) (intervalCell k') y)
    rw [map_intervalCell, hfk, op_id, Functor.map_id_apply]
  by_cases hdeg : grade ℕ (k A.top) < A.dimension
  · exact MarkedDiagSet.mem_marked_of_isDegenerate _ (isDegenerate_app _
      (isDegenerate_grayTensorCell (Or.inl (isDegenerate_app intervalBallIso.hom
        (isDegenerate_ball_of_degenerate (degenerate_of_grade_lt k hdeg))))))
  have hge : grade ℕ (k A.top) = A.dimension :=
    le_antisymm (grade_apply_top_le k) (not_lt.1 hdeg)
  have hg1 : grade ℕ (atomGlobe 1).top = 1 := by
    rw [← Atom.dimension_eq, dimension_atomGlobe]
  have hle : grade ℕ (k A.top) ≤ 1 := by
    have := grade_mono (𝕆 := ℕ) ((atomGlobe 1).le_top (k A.top))
    omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (hge ▸ hle) with h0 | h1
  · have hy : y ∈ X.marked B := by
      rcases hm with hx | hy | ⟨-, hA, -⟩
      · exact absurd (markedInterval.markable A _ hx) (by change ¬ 0 < A.dimension; omega)
      · exact hy
      · omega
    have := isIso_toAtomPoint_of_dimension_eq_zero h0
    obtain ⟨ε, hε⟩ := exists_eq_atomGlobeVertex (inv (toAtomPoint A) ≫ k)
    rw [hrestrict (toAtomPoint A) (atomGlobeVertex ε) (by rw [← hε, IsIso.hom_inv_id_assoc]),
      cylTensorIso_inv_app_grayTensorCell_vertex ε]
    exact ((markedCylinder.obj X).transport (whiskerRightIso (asIso (toAtomPoint A)) B) _).1
      (((markedCylinder.obj X).transport (Atom.grayTensorLeftUnitor B) _).1
        (MarkedPresheaf.map_mem_marked _ hy))
  · have htop : k A.top = (atomGlobe 1).top := by
      refine ((atomGlobe 1).le_top _).eq_or_lt.resolve_right fun hlt => ?_
      have := grade_strictMono (𝕆 := ℕ) hlt
      omega
    have := isIso_of_isCollapseHom_of_dimension_eq k (isCollapseHom_of_apply_eq_top k htop)
      (h1.trans (dimension_atomGlobe 1).symm)
    rw [hrestrict k (𝟙 _) (Category.comp_id k), cylTensorIso_inv_app_grayTensorCell_top]
    exact ((markedCylinder.obj X).transport (whiskerRightIso (asIso k) B) _).1
      (((markedCylinder.obj X).transport (cylAtomGrayTensorIso B).symm _).1
        (mem_marked_markedCylinderUnitCell X y))

private noncomputable def markedCylinderTensorIsoApp (pseudo : Bool) (X : MarkedDiagSet.{u}) :
    markedCylinder.obj X ≅ markedTensor pseudo markedInterval X where
  hom := MarkedPresheaf.homMk (cylTensorIso X).hom fun _ _ hc => hom_app_mem_marked pseudo X hc
  inv := MarkedPresheaf.homMk (cylTensorIso X).inv fun _ _ hz => inv_app_mem_marked pseudo X hz
  hom_inv_id := MarkedPresheaf.hom_ext (cylTensorIso X).hom_inv_id
  inv_hom_id := MarkedPresheaf.hom_ext (cylTensorIso X).inv_hom_id

noncomputable def markedCylinderIsoTensorLeft (pseudo : Bool) :
    markedCylinder.{u} ≅ tensorLeft pseudo markedInterval.{u} :=
  NatIso.ofComponents (markedCylinderTensorIsoApp pseudo) fun {X Y} f => by
    have h : MarkedPresheaf.forget.map (markedCylinder.map f) ≫ (cylTensorIso Y).hom =
        (cylTensorIso X).hom ≫ grayTensorBifunctor.map
          (X := (markedInterval.underlying, X.underlying))
          (Y := (markedInterval.underlying, Y.underlying)) (𝟙 _, MarkedPresheaf.forget.map f) :=
      markedCylinderForgetTensorIso.{u}.hom.naturality f
    refine MarkedPresheaf.hom_ext (((Functor.map_comp _ _ _).trans h).trans
      (Eq.trans ?_ (Functor.map_comp _ _ _).symm))
    exact congrArg (fun a => (cylTensorIso X).hom ≫ grayTensorBifunctor.map
      (X := (markedInterval.underlying, X.underlying))
        (Y := (markedInterval.underlying, Y.underlying)) (a, MarkedPresheaf.forget.map f))
      (MarkedPresheaf.forget.map_id markedInterval).symm

theorem markedExactCylinder_endpoint_app_comp_markedCylinderIsoTensorLeft_hom_app
    (pseudo ε : Bool) (X : MarkedDiagSet.{u}) :
    (markedExactCylinder.endpoint ε).app X ≫ (markedCylinderIsoTensorLeft pseudo).hom.app X =
      (markedTensorLeftUnitor pseudo X).inv ≫
        markedTensorMap pseudo (markedIntervalVertex ε) (𝟙 X) :=
  MarkedPresheaf.hom_ext ((Functor.map_comp _ _ _).trans (forget_map_endpoint_comp_hom pseudo ε X))

theorem markedCylinderIsoTensorLeft_inv_app_comp_contraction_app (pseudo : Bool)
    (X : MarkedDiagSet.{u}) :
    (markedCylinderIsoTensorLeft pseudo).inv.app X ≫ markedExactCylinder.contraction.app X =
      markedTensorSnd pseudo markedInterval X := by
  have hc : markedCylinderForgetIso.hom.app X ≫ grayCylinderContraction.app X.underlying =
      MarkedPresheaf.forget.map (markedExactCylinder.contraction.app X) :=
    NatTrans.congr_app markedCylinderForgetIso_hom_comp_whiskerLeft_contraction X
  have h₂ : markedCylinderForgetIso.inv.app X ≫
      MarkedPresheaf.forget.map (markedExactCylinder.contraction.app X) =
        grayCylinderContraction.app X.underlying :=
    (congrArg (markedCylinderForgetIso.inv.app X ≫ ·) hc).symm.trans
      (Iso.inv_hom_id_app_assoc markedCylinderForgetIso X _)
  have h₃ : grayTensorBifunctor.map (X := (markedInterval.underlying, X.underlying))
      (Y := (ball (atomGlobe 1), X.underlying)) (intervalBallIso.inv, 𝟙 X.underlying) ≫
        grayCylinderFunctorIsoGrayTensor.inv.app X.underlying ≫
          grayCylinderContraction.app X.underlying =
      grayTensorSnd markedInterval.underlying X.underlying := by
    rw [grayCylinderFunctorIsoGrayTensor_inv_app_comp_grayCylinderContraction_app, grayTensorSnd,
      grayTensorSnd, ← Category.assoc, ← Functor.map_comp, prod_comp, Category.comp_id,
      isTerminalBallAtomPoint.hom_ext (intervalBallIso.inv ≫ isTerminalBallAtomPoint.from _)
        (isTerminalBallAtomPoint.from _)]
  refine MarkedPresheaf.hom_ext ((Functor.map_comp _ _ _).trans ?_)
  exact (Category.assoc _ _ _).trans ((congrArg (grayTensorBifunctor.map
    (X := (markedInterval.underlying, X.underlying)) (Y := (ball (atomGlobe 1), X.underlying))
      (intervalBallIso.inv, 𝟙 X.underlying) ≫ ·) ((Category.assoc _ _ _).trans
        (congrArg (grayCylinderFunctorIsoGrayTensor.inv.app X.underlying ≫ ·) h₂))).trans h₃)

end Atoms.Diagrammatic
