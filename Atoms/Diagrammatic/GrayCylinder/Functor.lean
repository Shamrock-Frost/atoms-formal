import Atoms.Diagrammatic.DiagrammaticSet
import Atoms.Shape.GrayCylinder

open CategoryTheory Limits Opposite Atoms.Shape

universe w w' u

namespace Atoms.Diagrammatic

noncomputable def grayCylinderFunctor : DiagSet.{u} ⥤ DiagSet.{u} := grayCylinder.op.lan

instance preservesColimitsOfSize_grayCylinderFunctor :
    PreservesColimitsOfSize.{w, w'} grayCylinderFunctor.{u} :=
  (grayCylinder.op.lanAdjunction (Type u)).leftAdjoint_preservesColimits

noncomputable def grayCylinderUnit (X : DiagSet.{u}) :
    X ⟶ grayCylinder.op ⋙ grayCylinderFunctor.obj X :=
  grayCylinder.op.lanUnit.app X

instance isLeftKanExtension_grayCylinderFunctor_obj (X : DiagSet.{u}) :
    (grayCylinderFunctor.obj X).IsLeftKanExtension (grayCylinderUnit X) :=
  inferInstanceAs ((grayCylinder.op.lan.obj X).IsLeftKanExtension (grayCylinder.op.lanUnit.app X))

theorem grayCylinderUnit_naturality {X Y : DiagSet.{u}} (f : X ⟶ Y) :
    f ≫ grayCylinderUnit Y =
      grayCylinderUnit X ≫ Functor.whiskerLeft grayCylinder.op (grayCylinderFunctor.map f) :=
  grayCylinder.op.lanUnit.naturality f

noncomputable def grayCylinderFunctorBallIso (U : Atom) :
    grayCylinderFunctor.obj (uliftYoneda.{u}.obj U) ≅ uliftYoneda.{u}.obj (grayCylinder.obj U) :=
  have (F : Atom ⥤ Atom) :
      (uliftYoneda.{u}.obj (F.obj U)).IsLeftKanExtension (uliftYonedaMap.{u} F U) :=
    inferInstance
  haveI := this grayCylinder
  Functor.leftKanExtensionUnique _ (grayCylinderUnit (uliftYoneda.{u}.obj U)) _
    (uliftYonedaMap.{u} grayCylinder U)

theorem grayCylinderUnit_comp_grayCylinderFunctorBallIso_hom (U : Atom) :
    grayCylinderUnit (uliftYoneda.{u}.obj U) ≫
        Functor.whiskerLeft grayCylinder.op (grayCylinderFunctorBallIso U).hom =
      uliftYonedaMap.{u} grayCylinder U := by
  have (F : Atom ⥤ Atom) :
      (uliftYoneda.{u}.obj (F.obj U)).IsLeftKanExtension (uliftYonedaMap.{u} F U) :=
    inferInstance
  have := this grayCylinder
  simp [grayCylinderFunctorBallIso]

noncomputable def grayCylinderFunctorYonedaIso :
    uliftYoneda.{u} ⋙ grayCylinderFunctor ≅ grayCylinder ⋙ uliftYoneda.{u} :=
  NatIso.ofComponents grayCylinderFunctorBallIso fun {U V} f => by
    apply (grayCylinderFunctor.obj (uliftYoneda.{u}.obj U)).hom_ext_of_isLeftKanExtension
      (grayCylinderUnit (uliftYoneda.{u}.obj U))
    dsimp only [Functor.comp_map]
    rw [Functor.whiskerLeft_comp, ← Category.assoc, ← grayCylinderUnit_naturality,
      Category.assoc, grayCylinderUnit_comp_grayCylinderFunctorBallIso_hom,
      Functor.whiskerLeft_comp, ← Category.assoc,
      grayCylinderUnit_comp_grayCylinderFunctorBallIso_hom]
    ext W ⟨g⟩
    exact congrArg ULift.up (grayCylinder.map_comp g f)

def grayContractionRestrict (X : DiagSet.{u}) : X ⟶ grayCylinder.op ⋙ X :=
  Functor.whiskerRight (NatTrans.op grayContraction) X

theorem grayContractionRestrict_app (X : DiagSet.{u}) (V : Atomᵒᵖ) :
    (grayContractionRestrict X).app V = (X.map (grayContraction.app V.unop).op :
      X.obj V ⟶ X.obj (op (grayCylinder.obj (unop V)))) := rfl

def grayEndpointRestrict (ε : Bool) (X : DiagSet.{u}) : grayCylinder.op ⋙ X ⟶ X :=
  Functor.whiskerRight (NatTrans.op (grayEndpoint ε)) X

theorem grayEndpointRestrict_app (ε : Bool) (X : DiagSet.{u}) (V : Atomᵒᵖ) :
    (grayEndpointRestrict ε X).app V = (X.map ((grayEndpoint ε).app V.unop).op :
      X.obj (op (grayCylinder.obj (unop V))) ⟶ X.obj V) := rfl

theorem grayEndpointRestrict_naturality (ε : Bool) {X Y : DiagSet.{u}} (f : X ⟶ Y) :
    grayEndpointRestrict ε X ≫ f =
      Functor.whiskerLeft grayCylinder.op f ≫ grayEndpointRestrict ε Y := by
  refine NatTrans.ext (funext fun V => ?_)
  rw [NatTrans.comp_app, NatTrans.comp_app, grayEndpointRestrict_app, grayEndpointRestrict_app,
    Functor.whiskerLeft_app]
  exact f.naturality ((grayEndpoint ε).app V.unop).op

theorem grayContractionRestrict_comp_grayEndpointRestrict (ε : Bool) (X : DiagSet.{u}) :
    grayContractionRestrict X ≫ grayEndpointRestrict ε X = 𝟙 X := by
  refine NatTrans.ext (funext fun V => ?_)
  rw [NatTrans.comp_app, grayContractionRestrict_app, grayEndpointRestrict_app, ← X.map_comp,
    ← op_comp, grayEndpoint_grayContraction]
  exact X.map_id V

noncomputable def grayCylinderEndpoint (ε : Bool) : 𝟭 DiagSet.{u} ⟶ grayCylinderFunctor where
  app X := grayCylinderUnit X ≫ grayEndpointRestrict ε (grayCylinderFunctor.obj X)
  naturality X Y f := by
    change (f ≫ grayCylinderUnit Y) ≫ grayEndpointRestrict ε (grayCylinderFunctor.obj Y) =
      (grayCylinderUnit X ≫ grayEndpointRestrict ε (grayCylinderFunctor.obj X)) ≫
        grayCylinderFunctor.map f
    rw [grayCylinderUnit_naturality, Category.assoc, Category.assoc,
      ← grayEndpointRestrict_naturality]

noncomputable def grayCylinderContractionApp (X : DiagSet.{u}) : grayCylinderFunctor.obj X ⟶ X :=
  (grayCylinderFunctor.obj X).descOfIsLeftKanExtension (grayCylinderUnit X) X
    (grayContractionRestrict X)

theorem grayCylinderUnit_comp_grayCylinderContractionApp (X : DiagSet.{u}) :
    grayCylinderUnit X ≫ Functor.whiskerLeft grayCylinder.op (grayCylinderContractionApp X) =
      grayContractionRestrict X :=
  Functor.descOfIsLeftKanExtension_fac _ _ _ _

noncomputable def grayCylinderContraction : grayCylinderFunctor ⟶ 𝟭 DiagSet.{u} where
  app X := grayCylinderContractionApp X
  naturality X Y f := by
    change grayCylinderFunctor.map f ≫ grayCylinderContractionApp Y =
      grayCylinderContractionApp X ≫ f
    apply (grayCylinderFunctor.obj X).hom_ext_of_isLeftKanExtension (grayCylinderUnit X)
    rw [Functor.whiskerLeft_comp, ← Category.assoc, ← grayCylinderUnit_naturality,
      Category.assoc, grayCylinderUnit_comp_grayCylinderContractionApp, Functor.whiskerLeft_comp,
      ← Category.assoc, grayCylinderUnit_comp_grayCylinderContractionApp]
    refine NatTrans.ext (funext fun V => ?_)
    rw [NatTrans.comp_app, NatTrans.comp_app, grayContractionRestrict_app,
      grayContractionRestrict_app, Functor.whiskerLeft_app]
    exact (f.naturality (grayContraction.app V.unop).op).symm

theorem grayCylinderEndpoint_app_ball (ε : Bool) (U : Atom) :
    (grayCylinderEndpoint ε).app (ball U) ≫ grayCylinderFunctorYonedaIso.hom.app U =
      (uliftYoneda.{u}.map ((grayEndpoint ε).app U) : ball U ⟶ ball (grayCylinder.obj U)) := by
  change (grayCylinderUnit (uliftYoneda.{u}.obj U) ≫
      grayEndpointRestrict ε (grayCylinderFunctor.obj (uliftYoneda.{u}.obj U))) ≫
        (grayCylinderFunctorBallIso U).hom = _
  rw [Category.assoc, grayEndpointRestrict_naturality, ← Category.assoc,
    grayCylinderUnit_comp_grayCylinderFunctorBallIso_hom]
  refine NatTrans.ext (funext fun V => ?_)
  rw [NatTrans.comp_app, grayEndpointRestrict_app]
  ext ⟨g⟩
  exact congrArg ULift.up ((grayEndpoint ε).naturality g).symm

theorem grayCylinderContraction_app_ball (U : Atom) :
    grayCylinderContraction.app (ball U) =
      grayCylinderFunctorYonedaIso.hom.app U ≫
        (uliftYoneda.{u}.map (grayContraction.app U) : ball (grayCylinder.obj U) ⟶ ball U) := by
  change grayCylinderContractionApp (uliftYoneda.{u}.obj U) =
    (grayCylinderFunctorBallIso U).hom ≫ uliftYoneda.{u}.map (grayContraction.app U)
  apply (grayCylinderFunctor.obj (uliftYoneda.{u}.obj U)).hom_ext_of_isLeftKanExtension
    (grayCylinderUnit (uliftYoneda.{u}.obj U))
  rw [grayCylinderUnit_comp_grayCylinderContractionApp, Functor.whiskerLeft_comp,
    ← Category.assoc, grayCylinderUnit_comp_grayCylinderFunctorBallIso_hom]
  refine NatTrans.ext (funext fun V => ?_)
  rw [grayContractionRestrict_app]
  ext ⟨g⟩
  exact congrArg ULift.up (grayContraction.naturality g).symm

theorem grayCylinderEndpoint_grayCylinderContraction (ε : Bool) :
    grayCylinderEndpoint ε ≫ grayCylinderContraction = 𝟙 (𝟭 DiagSet.{u}) := by
  refine NatTrans.ext (funext fun X => ?_)
  change (grayCylinderUnit X ≫ grayEndpointRestrict ε (grayCylinderFunctor.obj X)) ≫
    grayCylinderContractionApp X = 𝟙 X
  rw [Category.assoc, grayEndpointRestrict_naturality, ← Category.assoc,
    grayCylinderUnit_comp_grayCylinderContractionApp]
  exact grayContractionRestrict_comp_grayEndpointRestrict ε X

end Atoms.Diagrammatic
