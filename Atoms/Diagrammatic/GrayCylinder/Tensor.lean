import Atoms.Diagrammatic.GrayCylinder.Exact
import Atoms.Diagrammatic.GrayTensor.Monoidal
import Atoms.Shape.GrayCylinderTensor

open CategoryTheory Limits Opposite MonoidalCategory Atoms.Shape

universe u

namespace Atoms.Diagrammatic

attribute [local irreducible] grayTensorBifunctor GrayDiagSet.leftUnitor

private theorem grayTensorBifunctor_map_id_comp {A A' B B' : DiagSet.{u}} (a : A ⟶ A')
    (b : B ⟶ B') :
    grayTensorBifunctor.map (X := (A, B)) (Y := (A', B)) (a, 𝟙 B) ≫
        grayTensorBifunctor.map (X := (A', B)) (Y := (A', B')) (𝟙 A', b) =
      grayTensorBifunctor.map (X := (A, B)) (Y := (A', B')) (a, b) :=
  by rw [← Functor.map_comp, prod_comp, Category.comp_id, Category.id_comp]

private theorem grayTensorBifunctor_id_map_comp {A A' B B' : DiagSet.{u}} (a : A ⟶ A')
    (b : B ⟶ B') :
    grayTensorBifunctor.map (X := (A, B)) (Y := (A, B')) (𝟙 A, b) ≫
        grayTensorBifunctor.map (X := (A, B')) (Y := (A', B')) (a, 𝟙 B') =
      grayTensorBifunctor.map (X := (A, B)) (Y := (A', B')) (a, b) :=
  by rw [← Functor.map_comp, prod_comp, Category.comp_id, Category.id_comp]

private noncomputable def grayTensorLeftBallIso :
    uliftYoneda.{u} ⋙ (Functor.curry.obj grayTensorBifunctor.{u}).obj (ball (atomGlobe 1)) ≅
      MonoidalCategory.tensorLeft (atomGlobe 1) ⋙ uliftYoneda.{u} :=
  NatIso.ofComponents (fun U => grayTensorBallIso (atomGlobe 1) U) fun {U V} f => by
    have h := grayTensorYonedaIso.{u}.hom.naturality (X := (atomGlobe 1, U))
      (Y := (atomGlobe 1, V)) (𝟙 (atomGlobe 1), f)
    simp only [Functor.comp_map, Functor.prod_map, CategoryTheory.Functor.map_id] at h
    exact h

private noncomputable def grayCylinderFunctorBallTensorIso :
    uliftYoneda.{u} ⋙ grayCylinderFunctor.{u} ≅
      uliftYoneda.{u} ⋙ (Functor.curry.obj grayTensorBifunctor.{u}).obj (ball (atomGlobe 1)) :=
  grayCylinderFunctorYonedaIso ≪≫ Functor.isoWhiskerRight grayCylinderIsoTensorLeft uliftYoneda ≪≫
    grayTensorLeftBallIso.symm

noncomputable def grayCylinderFunctorIsoGrayTensor :
    grayCylinderFunctor.{u} ≅
      (Functor.curry.obj grayTensorBifunctor.{u}).obj (ball (atomGlobe 1)) :=
  have := Presheaf.isLeftKanExtension_of_preservesColimits grayCylinderFunctor.{u} (Iso.refl _)
  have := Presheaf.isLeftKanExtension_of_preservesColimits
    ((Functor.curry.obj grayTensorBifunctor.{u}).obj (ball (atomGlobe 1))) (Iso.refl _)
  Functor.leftKanExtensionUniqueOfIso _ (Iso.refl _).hom grayCylinderFunctorBallTensorIso _
    (Iso.refl _).hom

private theorem grayCylinderFunctorIsoGrayTensor_hom_app_ball (U : Atom) :
    grayCylinderFunctorIsoGrayTensor.{u}.hom.app (ball U) =
      (grayCylinderFunctorBallIso U).hom ≫ uliftYoneda.map (cylAtomGrayTensorIso U).hom ≫
        (grayTensorBallIso (atomGlobe 1) U).inv := by
  have := Presheaf.isLeftKanExtension_of_preservesColimits grayCylinderFunctor.{u} (Iso.refl _)
  have h := grayCylinderFunctor.{u}.descOfIsLeftKanExtension_fac_app (Iso.refl _).hom
    ((Functor.curry.obj grayTensorBifunctor.{u}).obj (ball (atomGlobe 1)))
    (grayCylinderFunctorBallTensorIso.hom ≫ (Iso.refl _).hom) U
  refine Eq.trans ?_ (h.trans ?_)
  · simp [grayCylinderFunctorIsoGrayTensor]
  · simp [grayCylinderFunctorBallTensorIso, grayTensorLeftBallIso, grayCylinderIsoTensorLeft]
    rfl

theorem grayCylinderFunctorIsoGrayTensor_hom_app_grayCylinderUnit_app (X : DiagSet.{u}) {U : Atom}
    (x : diagram X U) :
    (grayCylinderFunctorIsoGrayTensor.hom.app X).app (op (grayCylinder.obj U))
        ((grayCylinderUnit X).app (op U) x) =
      (grayTensor (ball (atomGlobe 1)) X).map (cylAtomGrayTensorIso U).hom.op
        (grayTensorCell (X := ball (atomGlobe 1)) (ULift.up (𝟙 (atomGlobe 1))) x) := by
  let φ : ball U ⟶ X := uliftYonedaEquiv.symm x
  have hx : φ.app (op U) ⟨𝟙 U⟩ = x := by
    rw [uliftYonedaEquiv_symm_apply_app]
    exact Functor.map_id_apply X _ x
  have h₁ : (grayCylinderFunctor.map φ).app (op (grayCylinder.obj U))
      ((grayCylinderUnit (ball U)).app (op U) ⟨𝟙 U⟩) = (grayCylinderUnit X).app (op U) x :=
    ((ConcreteCategory.congr_hom (NatTrans.congr_app (grayCylinderUnit_naturality φ) (op U))
      ⟨𝟙 U⟩).symm.trans (congrArg ((grayCylinderUnit X).app (op U)) hx) :)
  rw [← h₁]
  have hb : (grayCylinderFunctorBallIso.{u} U).hom.app (op (grayCylinder.obj U))
      ((grayCylinderUnit (ball U)).app (op U) ⟨𝟙 U⟩) = ⟨𝟙 (grayCylinder.obj U)⟩ :=
    (ConcreteCategory.congr_hom (NatTrans.congr_app
      (grayCylinderUnit_comp_grayCylinderFunctorBallIso_hom U) (op U)) ⟨𝟙 U⟩).trans
        (congrArg ULift.up (grayCylinder.map_id U))
  have h₂ := ConcreteCategory.congr_hom (NatTrans.congr_app
    (grayCylinderFunctorIsoGrayTensor.{u}.hom.naturality φ) (op (grayCylinder.obj U)))
    ((grayCylinderUnit (ball U)).app (op U) ⟨𝟙 U⟩)
  refine h₂.trans ?_
  change (grayTensorBifunctor.map (X := (ball (atomGlobe 1), ball U)) (Y := (ball (atomGlobe 1), X))
      (𝟙 _, φ)).app _ ((grayCylinderFunctorIsoGrayTensor.hom.app (ball U)).app _
        ((grayCylinderUnit (ball U)).app (op U) ⟨𝟙 U⟩)) = _
  rw [grayCylinderFunctorIsoGrayTensor_hom_app_ball, NatTrans.comp_app_apply,
    NatTrans.comp_app_apply]
  simp only [Functor.op_obj, Opposite.unop_op]
  rw [hb]
  change (grayTensorBifunctor.map (X := (ball (atomGlobe 1), ball U)) (Y := (ball (atomGlobe 1), X))
      (𝟙 _, φ)).app _ ((grayTensor (ball (atomGlobe 1)) (ball U)).map
        (𝟙 _ ≫ (cylAtomGrayTensorIso U).hom).op
          (grayTensorCell (X := ball (atomGlobe 1)) (Y := ball U) ⟨𝟙 _⟩ ⟨𝟙 U⟩)) = _
  rw [Category.id_comp, NatTrans.naturality_apply]
  exact congrArg _ ((grayTensorCell_naturality (𝟙 (ball (atomGlobe 1))) φ ⟨𝟙 (atomGlobe 1)⟩
    ⟨𝟙 U⟩).trans (congrArg (grayTensorCell _) hx))

private noncomputable def grayTensorVertex (ε : Bool) :
    𝟭 DiagSet.{u} ⟶ (Functor.curry.obj grayTensorBifunctor.{u}).obj (ball (atomGlobe 1)) where
  app X := (GrayDiagSet.leftUnitor X).inv ≫
    grayTensorBifunctor.map (X := (ball atomPoint, X)) (Y := (ball (atomGlobe 1), X))
      (uliftYoneda.map (atomGlobeVertex ε), 𝟙 X)
  naturality X Y f := by
    change f ≫ (GrayDiagSet.leftUnitor Y).inv ≫
        grayTensorBifunctor.map (X := (ball atomPoint, Y)) (Y := (ball (atomGlobe 1), Y))
          (uliftYoneda.map (atomGlobeVertex ε), 𝟙 Y) =
      ((GrayDiagSet.leftUnitor X).inv ≫
        grayTensorBifunctor.map (X := (ball atomPoint, X)) (Y := (ball (atomGlobe 1), X))
          (uliftYoneda.map (atomGlobeVertex ε), 𝟙 X)) ≫
        grayTensorBifunctor.map (X := (ball (atomGlobe 1), X)) (Y := (ball (atomGlobe 1), Y))
          (𝟙 _, f)
    have h₁ : f ≫ (GrayDiagSet.leftUnitor Y).inv =
        (GrayDiagSet.leftUnitor X).inv ≫ grayTensorBifunctor.map (X := (ball atomPoint, X))
          (Y := (ball atomPoint, Y)) (𝟙 (ball atomPoint), f) := by
      rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]
      exact (GrayDiagSet.leftUnitor_naturality f).symm
    rw [← Category.assoc, h₁, Category.assoc, Category.assoc, grayTensorBifunctor_id_map_comp,
      grayTensorBifunctor_map_id_comp]

private theorem grayCylinderEndpoint_comp_hom_ball (ε : Bool) (U : Atom) :
    (grayCylinderEndpoint ε).app (ball U) ≫ grayCylinderFunctorIsoGrayTensor.{u}.hom.app (ball U) =
      (grayTensorVertex ε).app (ball U) := by
  change _ = (GrayDiagSet.leftUnitor (ball U)).inv ≫
    grayTensorBifunctor.map (X := (ball atomPoint, ball U)) (Y := (ball (atomGlobe 1), ball U))
      (uliftYoneda.map (atomGlobeVertex ε), 𝟙 (ball U))
  have hv : grayTensorBifunctor.map (X := (ball atomPoint, ball U))
      (Y := (ball (atomGlobe 1), ball U)) (uliftYoneda.map (atomGlobeVertex ε), 𝟙 (ball.{u} U)) =
      (grayTensorBallIso atomPoint U).hom ≫
        uliftYoneda.map (Atom.grayTensorMap (atomGlobeVertex ε) (𝟙 U)) ≫
          (grayTensorBallIso (atomGlobe 1) U).inv := by
    have h := grayTensorYonedaIso.{u}.hom.naturality (X := (atomPoint, U))
      (Y := (atomGlobe 1, U)) (atomGlobeVertex ε, 𝟙 U)
    simp only [Functor.comp_map, Functor.prod_map, CategoryTheory.Functor.map_id] at h
    rw [← Category.assoc, Iso.eq_comp_inv]
    exact h
  have hl : (GrayDiagSet.leftUnitor (ball.{u} U)).inv =
      uliftYoneda.map (Atom.grayTensorLeftUnitor U).inv ≫ (grayTensorBallIso atomPoint U).inv := by
    refine (cancel_epi (GrayDiagSet.leftUnitor (ball.{u} U)).hom).1 ?_
    rw [Iso.hom_inv_id, grayTensorBallIso_left_unitality, Category.assoc, ← Functor.map_comp_assoc,
      Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id]
  have hb : (grayCylinderEndpoint ε).app (ball U) ≫ (grayCylinderFunctorBallIso.{u} U).hom =
      uliftYoneda.map ((grayEndpoint ε).app U) :=
    grayCylinderEndpoint_app_ball ε U
  have he : (grayEndpoint ε).app U ≫ (cylAtomGrayTensorIso U).hom =
      (Atom.grayTensorLeftUnitor U).inv ≫ Atom.grayTensorMap (atomGlobeVertex ε) (𝟙 U) :=
    NatTrans.congr_app (grayEndpoint_comp_grayCylinderIsoTensorLeft_hom ε) U
  rw [grayCylinderFunctorIsoGrayTensor_hom_app_ball, ← Category.assoc, ← Category.assoc, hb,
    ← Functor.map_comp, he, hl, hv, Category.assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp_assoc]

theorem grayCylinderEndpoint_app_comp_grayCylinderFunctorIsoGrayTensor_hom_app (ε : Bool)
    (X : DiagSet.{u}) :
    (grayCylinderEndpoint ε).app X ≫ grayCylinderFunctorIsoGrayTensor.hom.app X =
      (GrayDiagSet.leftUnitor X).inv ≫
        grayTensorBifunctor.map (X := (ball atomPoint, X)) (Y := (ball (atomGlobe 1), X))
          (uliftYoneda.map (atomGlobeVertex ε), 𝟙 X) :=
  NatTrans.congr_app (hom_ext_of_preservesColimits (α := grayCylinderEndpoint ε ≫
    grayCylinderFunctorIsoGrayTensor.hom) (β := grayTensorVertex ε)
    (grayCylinderEndpoint_comp_hom_ball ε)) X

private noncomputable def grayTensorSndNatTrans :
    (Functor.curry.obj grayTensorBifunctor.{u}).obj (ball (atomGlobe 1)) ⟶ 𝟭 DiagSet.{u} where
  app X := grayTensorSnd (ball (atomGlobe 1)) X
  naturality X Y f := by
    change grayTensorBifunctor.map (X := (ball (atomGlobe 1), X)) (Y := (ball (atomGlobe 1), Y))
        (𝟙 _, f) ≫ grayTensorBifunctor.map (X := (ball (atomGlobe 1), Y))
          (Y := (ball atomPoint, Y)) (isTerminalBallAtomPoint.from _, 𝟙 Y) ≫
          (GrayDiagSet.leftUnitor Y).hom =
      (grayTensorBifunctor.map (X := (ball (atomGlobe 1), X)) (Y := (ball atomPoint, X))
        (isTerminalBallAtomPoint.from _, 𝟙 X) ≫ (GrayDiagSet.leftUnitor X).hom) ≫ f
    rw [Category.assoc, ← GrayDiagSet.leftUnitor_naturality, ← Category.assoc, ← Category.assoc,
      grayTensorBifunctor_id_map_comp, grayTensorBifunctor_map_id_comp]

private theorem hom_comp_grayTensorSnd_ball (U : Atom) :
    grayCylinderFunctorIsoGrayTensor.{u}.hom.app (ball U) ≫ grayTensorSndNatTrans.app (ball U) =
      grayCylinderContraction.app (ball U) := by
  change _ ≫ grayTensorSnd (ball (atomGlobe 1)) (ball U) = _
  have hs : grayTensorSnd (ball.{u} (atomGlobe 1)) (ball U) =
      (grayTensorBallIso (atomGlobe 1) U).hom ≫
        uliftYoneda.map (Atom.grayTensorSnd (atomGlobe 1) U) := by
    refine grayTensor_hom_ext fun A B a b => ULift.ext _ _ ?_
    have hab : ((grayTensorBallIso (atomGlobe 1) U).hom.app (op (Atom.grayTensor A B))
        (grayTensorCell a b)).down = Atom.grayTensorMap a.down b.down :=
      congrArg ULift.down (grayTensorBallIso_hom_app_grayTensorCell a.down b.down)
    rw [grayTensorSnd_app_grayTensorCell, NatTrans.comp_app_apply]
    simp only [uliftYoneda_map_app, uliftYoneda_obj_map, TypeCat.ofHom_apply, ULift.down_up,
      Quiver.Hom.unop_op, hab]
    have e : Atom.grayTensorMap a.down b.down ≫
        Atom.grayTensorMap (toAtomPoint (atomGlobe 1)) (𝟙 U) =
        Atom.grayTensorMap (toAtomPoint A) (𝟙 B) ≫ Atom.grayTensorMap (𝟙 atomPoint) b.down := by
      rw [Atom.grayTensorMap_comp, Atom.grayTensorMap_comp, Category.comp_id, Category.id_comp,
        isTerminalAtomPoint.hom_ext (a.down ≫ toAtomPoint (atomGlobe 1)) (toAtomPoint A),
        Category.comp_id]
    rw [Atom.grayTensorSnd, reassoc_of% e, Atom.grayTensorLeftUnitor_naturality, Category.assoc]
  have hc : (cylAtomGrayTensorIso U).inv ≫ grayContraction.app U =
      Atom.grayTensorSnd (atomGlobe 1) U :=
    NatTrans.congr_app grayCylinderIsoTensorLeft_inv_comp_grayContraction U
  have hk : grayCylinderContraction.app (ball U) = (grayCylinderFunctorBallIso.{u} U).hom ≫
      uliftYoneda.map (grayContraction.app U) :=
    grayCylinderContraction_app_ball U
  rw [hs, grayCylinderFunctorIsoGrayTensor_hom_app_ball, hk, Category.assoc, Category.assoc,
    Iso.inv_hom_id_assoc, ← Functor.map_comp, ← hc, Iso.hom_inv_id_assoc]

theorem grayCylinderFunctorIsoGrayTensor_inv_app_comp_grayCylinderContraction_app
    (X : DiagSet.{u}) :
    grayCylinderFunctorIsoGrayTensor.inv.app X ≫ grayCylinderContraction.app X =
      grayTensorSnd (ball (atomGlobe 1)) X := by
  have h := hom_ext_of_preservesColimits (α := grayCylinderFunctorIsoGrayTensor.{u}.hom ≫
    grayTensorSndNatTrans) (β := grayCylinderContraction) hom_comp_grayTensorSnd_ball
  rw [← h, NatTrans.comp_app, Iso.inv_hom_id_app_assoc]
  rfl

end Atoms.Diagrammatic
