import Atoms.Diagrammatic.GrayTensor.Functor
import Atoms.Shape.GrayTensorMonoidal
import Mathlib.CategoryTheory.Monoidal.DayConvolution

open CategoryTheory Limits Opposite MonoidalCategory Atoms.Shape
open scoped MonoidalCategory.ExternalProduct MonoidalCategory.DayConvolution

universe w w' u

namespace Atoms.Diagrammatic

@[implicit_reducible] def GrayDiagSet : Type (u + 1) := Atomᵒᵖ ⥤ Type u

namespace GrayDiagSet

instance : Category.{u} GrayDiagSet.{u} := inferInstanceAs (Category DiagSet.{u})

def toGray : DiagSet.{u} ⥤ GrayDiagSet.{u} := 𝟭 DiagSet.{u}

def ofGray : GrayDiagSet.{u} ⥤ DiagSet.{u} := 𝟭 DiagSet.{u}

@[simp] theorem ofGray_obj_toGray_obj (X : DiagSet.{u}) : ofGray.obj (toGray.obj X) = X :=
  rfl

@[simp] theorem ofGray_map_toGray_map {X Y : DiagSet.{u}} (f : X ⟶ Y) :
    ofGray.map (toGray.map f) = f :=
  rfl

@[simp] theorem toGray_obj_ofGray_obj (X : GrayDiagSet.{u}) : toGray.obj (ofGray.obj X) = X :=
  rfl

@[simp] theorem toGray_map_ofGray_map {X Y : GrayDiagSet.{u}} (f : X ⟶ Y) :
    toGray.map (ofGray.map f) = f :=
  rfl

def equivalence : GrayDiagSet.{u} ≌ DiagSet.{u} where
  functor := ofGray
  inverse := toGray
  unitIso := Iso.refl _
  counitIso := Iso.refl _

instance : ofGray.{u}.IsEquivalence := equivalence.isEquivalence_functor

end GrayDiagSet

@[instance_reducible]
noncomputable def grayTensorDayConvolution (X Y : DiagSet.{u}) : DayConvolution X Y where
  convolution := grayTensor X Y
  unit := grayTensorUnit X Y
  isPointwiseLeftKanExtensionUnit :=
    Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension _ (grayTensorUnit X Y)

@[instance_reducible]
def ballAtomPointDayConvolutionUnit : DayConvolutionUnit (ball.{u} atomPoint) where
  can := ↾fun _ => uliftYonedaEquiv (𝟙 (ball.{u} atomPoint))
  isPointwiseLeftKanExtensionCan d :=
    have hj (j : CostructuredArrow (Functor.fromPUnit.{0} (op atomPoint)) d) :
        j = CostructuredArrow.mk (Y := (⟨⟨⟩⟩ : Discrete PUnit)) (toAtomPoint d.unop).op := by
      obtain ⟨⟨⟨⟨⟩⟩⟩, ⟨⟨⟩⟩, f⟩ := j
      exact congrArg _ (Quiver.Hom.unop_inj (isTerminalAtomPoint.hom_ext _ _))
    { desc s := ↾fun _ => s.ι.app (CostructuredArrow.mk
        (Y := (⟨⟨⟩⟩ : Discrete PUnit)) (toAtomPoint d.unop).op) PUnit.unit
      fac s j := by
        obtain rfl := hj j
        rfl
      uniq s m hm := by
        ext x
        obtain rfl : x = ULift.up (toAtomPoint d.unop ≫ 𝟙 atomPoint) :=
          ULift.ext _ _ (isTerminalAtomPoint.hom_ext _ _)
        exact ConcreteCategory.congr_hom (hm (CostructuredArrow.mk
          (Y := (⟨⟨⟩⟩ : Discrete PUnit)) (toAtomPoint d.unop).op)) PUnit.unit }

attribute [local instance] grayTensorDayConvolution ballAtomPointDayConvolutionUnit

private theorem grayTensorBifunctor_map_eq_map {X Y X' Y' : DiagSet.{u}} (f : X ⟶ X')
    (g : Y ⟶ Y') : grayTensorBifunctor.map (f, g) = DayConvolution.map f g := by
  refine grayTensor_hom_ext fun U V x y => ?_
  rw [grayTensorCell_naturality]
  exact (ConcreteCategory.congr_hom (DayConvolution.unit_app_map_app f g (op U) (op V))
    ((x, y) : X.obj (op U) × Y.obj (op V))).symm

namespace GrayDiagSet

noncomputable def associator (X Y Z : DiagSet.{u}) :
    grayTensor (grayTensor X Y) Z ≅ grayTensor X (grayTensor Y Z) :=
  DayConvolution.associator X Y Z

noncomputable def leftUnitor (X : DiagSet.{u}) : grayTensor (ball atomPoint) X ≅ X :=
  DayConvolutionUnit.leftUnitor _ X

noncomputable def rightUnitor (X : DiagSet.{u}) : grayTensor X (ball atomPoint) ≅ X :=
  DayConvolutionUnit.rightUnitor _ X

theorem associator_hom_app_grayTensorCell {X Y Z : DiagSet.{u}} {U V W : Atom}
    (x : diagram X U) (y : diagram Y V) (z : diagram Z W) :
    (GrayDiagSet.associator X Y Z).hom.app _ (grayTensorCell (grayTensorCell x y) z) =
      (grayTensor X (grayTensor Y Z)).map (Atom.grayTensorAssoc U V W).hom.op
        (grayTensorCell x (grayTensorCell y z)) :=
  ConcreteCategory.congr_hom
    (DayConvolution.associator_hom_unit_unit X Y Z (op U) (op V) (op W))
    (((x, y), z) : (X.obj (op U) × Y.obj (op V)) × Z.obj (op W))

theorem associator_inv_app_grayTensorCell {X Y Z : DiagSet.{u}} {U V W : Atom}
    (x : diagram X U) (y : diagram Y V) (z : diagram Z W) :
    (GrayDiagSet.associator X Y Z).inv.app _ (grayTensorCell x (grayTensorCell y z)) =
      (grayTensor (grayTensor X Y) Z).map (Atom.grayTensorAssoc U V W).inv.op
        (grayTensorCell (grayTensorCell x y) z) := by
  conv_rhs => rw [← Iso.hom_inv_id_app_apply (GrayDiagSet.associator X Y Z) _
    (grayTensorCell (grayTensorCell x y) z), GrayDiagSet.associator_hom_app_grayTensorCell,
    ← NatTrans.naturality_apply, ← Functor.map_comp_apply, ← op_comp, Iso.inv_hom_id, op_id,
    Functor.map_id_apply]

private theorem leftUnitor_hom_app_grayTensorCell_id {X : DiagSet.{u}} {U : Atom}
    (x : diagram X U) :
    (GrayDiagSet.leftUnitor X).hom.app _
        (grayTensorCell (uliftYonedaEquiv (𝟙 (ball.{u} atomPoint))) x) =
      X.map (Atom.grayTensorLeftUnitor U).hom.op x :=
  ConcreteCategory.congr_hom
    (DayConvolutionUnit.leftUnitor_hom_unit_app (ball atomPoint) X (op U))
    ((PUnit.unit, x) : PUnit × X.obj (op U))

private theorem rightUnitor_hom_app_grayTensorCell_id {X : DiagSet.{u}} {U : Atom}
    (x : diagram X U) :
    (GrayDiagSet.rightUnitor X).hom.app _
        (grayTensorCell x (uliftYonedaEquiv (𝟙 (ball.{u} atomPoint)))) =
      X.map (Atom.grayTensorRightUnitor U).hom.op x :=
  ConcreteCategory.congr_hom
    (DayConvolutionUnit.rightUnitor_hom_unit_app (ball atomPoint) X (op U))
    ((x, PUnit.unit) : X.obj (op U) × PUnit)

theorem leftUnitor_hom_app_grayTensorCell {X : DiagSet.{u}} {A U : Atom}
    (p : diagram (ball.{u} atomPoint) A) (x : diagram X U) :
    (GrayDiagSet.leftUnitor X).hom.app (op (Atom.grayTensor A U)) (grayTensorCell p x) =
      X.map (Atom.grayTensorMap (toAtomPoint A) (𝟙 U) ≫ (Atom.grayTensorLeftUnitor U).hom).op
        x := by
  have e : grayTensorCell p x = (grayTensor (ball atomPoint) X).map
      (Atom.grayTensorMap (toAtomPoint A) (𝟙 U)).op
        (grayTensorCell (uliftYonedaEquiv (𝟙 (ball.{u} atomPoint))) x) := by
    rw [← grayTensorCell_restrict, op_id, Functor.map_id_apply]
    exact congrArg (grayTensorCell · x) (ULift.ext _ _ (isTerminalAtomPoint.hom_ext _ _))
  rw [e, NatTrans.naturality_apply, GrayDiagSet.leftUnitor_hom_app_grayTensorCell_id,
    ← Functor.map_comp_apply, ← op_comp]

theorem rightUnitor_hom_app_grayTensorCell {X : DiagSet.{u}} {U A : Atom}
    (x : diagram X U) (p : diagram (ball.{u} atomPoint) A) :
    (GrayDiagSet.rightUnitor X).hom.app (op (Atom.grayTensor U A)) (grayTensorCell x p) =
      X.map (Atom.grayTensorMap (𝟙 U) (toAtomPoint A) ≫ (Atom.grayTensorRightUnitor U).hom).op
        x := by
  have e : grayTensorCell x p = (grayTensor X (ball atomPoint)).map
      (Atom.grayTensorMap (𝟙 U) (toAtomPoint A)).op
        (grayTensorCell x (uliftYonedaEquiv (𝟙 (ball.{u} atomPoint)))) := by
    rw [← grayTensorCell_restrict, op_id, Functor.map_id_apply]
    exact congrArg (grayTensorCell x) (ULift.ext _ _ (isTerminalAtomPoint.hom_ext _ _))
  rw [e, NatTrans.naturality_apply, GrayDiagSet.rightUnitor_hom_app_grayTensorCell_id,
    ← Functor.map_comp_apply, ← op_comp]

@[reassoc] theorem associator_naturality {X Y Z X' Y' Z' : DiagSet.{u}}
    (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    grayTensorBifunctor.map (grayTensorBifunctor.map (f, g), h) ≫
        (GrayDiagSet.associator X' Y' Z').hom =
      (GrayDiagSet.associator X Y Z).hom ≫
        grayTensorBifunctor.map (f, grayTensorBifunctor.map (g, h)) :=
  DayConvolution.associator_naturality f g h

@[reassoc] theorem leftUnitor_naturality {X Y : DiagSet.{u}} (f : X ⟶ Y) :
    grayTensorBifunctor.map (𝟙 (ball atomPoint), f) ≫ (GrayDiagSet.leftUnitor Y).hom =
      (GrayDiagSet.leftUnitor X).hom ≫ f := by
  rw [grayTensorBifunctor_map_eq_map]
  exact DayConvolutionUnit.leftUnitor_naturality _ f

@[reassoc] theorem rightUnitor_naturality {X Y : DiagSet.{u}} (f : X ⟶ Y) :
    grayTensorBifunctor.map (f, 𝟙 (ball atomPoint)) ≫ (GrayDiagSet.rightUnitor Y).hom =
      (GrayDiagSet.rightUnitor X).hom ≫ f := by
  rw [grayTensorBifunctor_map_eq_map]
  exact DayConvolutionUnit.rightUnitor_naturality _ f

@[reassoc] theorem leftUnitor_inv_naturality {X Y : DiagSet.{u}} (f : X ⟶ Y) :
    (GrayDiagSet.leftUnitor X).inv ≫ grayTensorBifunctor.map (𝟙 (ball atomPoint), f) =
      f ≫ (GrayDiagSet.leftUnitor Y).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv,
    GrayDiagSet.leftUnitor_naturality]

@[reassoc] theorem rightUnitor_inv_naturality {X Y : DiagSet.{u}} (f : X ⟶ Y) :
    (GrayDiagSet.rightUnitor X).inv ≫ grayTensorBifunctor.map (f, 𝟙 (ball atomPoint)) =
      f ≫ (GrayDiagSet.rightUnitor Y).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv,
    GrayDiagSet.rightUnitor_naturality]

theorem pentagon (X Y Z W : DiagSet.{u}) :
    grayTensorBifunctor.map ((GrayDiagSet.associator X Y Z).hom, 𝟙 W) ≫
        (GrayDiagSet.associator X (grayTensor Y Z) W).hom ≫
          grayTensorBifunctor.map (𝟙 X, (GrayDiagSet.associator Y Z W).hom) =
      (GrayDiagSet.associator (grayTensor X Y) Z W).hom ≫
        (GrayDiagSet.associator X Y (grayTensor Z W)).hom :=
  DayConvolution.pentagon X Y Z W

theorem triangle (X Y : DiagSet.{u}) :
    (GrayDiagSet.associator X (ball atomPoint) Y).hom ≫
        grayTensorBifunctor.map (𝟙 X, (GrayDiagSet.leftUnitor Y).hom) =
      grayTensorBifunctor.map
        (((GrayDiagSet.rightUnitor X).hom, 𝟙 Y) : (grayTensor X (ball atomPoint), Y) ⟶ (X, Y)) :=
  DayConvolution.triangle X Y (ball atomPoint)

noncomputable instance instMonoidalCategory : MonoidalCategory GrayDiagSet.{u} :=
  letI : MonoidalCategoryStruct GrayDiagSet.{u} :=
    { tensorObj := fun X Y => toGray.obj (grayTensor (ofGray.obj X) (ofGray.obj Y))
      whiskerLeft := fun X _ _ g =>
        toGray.map (grayTensorBifunctor.map (𝟙 (ofGray.obj X), ofGray.map g))
      whiskerRight := fun f Y =>
        toGray.map (grayTensorBifunctor.map (ofGray.map f, 𝟙 (ofGray.obj Y)))
      tensorHom := fun f g => toGray.map (grayTensorBifunctor.map (ofGray.map f, ofGray.map g))
      tensorUnit := toGray.obj (ball atomPoint)
      associator := fun X Y Z =>
        toGray.mapIso (GrayDiagSet.associator (ofGray.obj X) (ofGray.obj Y) (ofGray.obj Z))
      leftUnitor := fun X => toGray.mapIso (GrayDiagSet.leftUnitor (ofGray.obj X))
      rightUnitor := fun X => toGray.mapIso (GrayDiagSet.rightUnitor (ofGray.obj X)) }
  .ofTensorHom
    (id_tensorHom_id := fun X Y => grayTensorBifunctor.map_id (X, Y))
    (id_tensorHom := fun _ _ _ _ => rfl)
    (tensorHom_id := fun _ _ => rfl)
    (tensorHom_comp_tensorHom := fun f₁ f₂ g₁ g₂ =>
      (grayTensorBifunctor.map_comp (X := (_, _)) (Y := (_, _)) (Z := (_, _))
        (f₁, f₂) (g₁, g₂)).symm)
    (associator_naturality := GrayDiagSet.associator_naturality)
    (leftUnitor_naturality := GrayDiagSet.leftUnitor_naturality)
    (rightUnitor_naturality := GrayDiagSet.rightUnitor_naturality)
    (pentagon := GrayDiagSet.pentagon)
    (triangle := GrayDiagSet.triangle)

@[simp] theorem ofGray_obj_tensorObj (X Y : GrayDiagSet.{u}) :
    ofGray.obj (X ⊗ Y) = grayTensor (ofGray.obj X) (ofGray.obj Y) :=
  rfl

@[simp] theorem ofGray_obj_tensorUnit : ofGray.obj (𝟙_ GrayDiagSet.{u}) = ball atomPoint :=
  rfl

@[simp] theorem ofGray_map_tensorHom {X Y X' Y' : GrayDiagSet.{u}} (f : X ⟶ X') (g : Y ⟶ Y') :
    ofGray.map (f ⊗ₘ g) = grayTensorBifunctor.map (ofGray.map f, ofGray.map g) :=
  rfl

@[simp] theorem ofGray_map_whiskerLeft (X : GrayDiagSet.{u}) {Y Y' : GrayDiagSet.{u}}
    (g : Y ⟶ Y') :
    ofGray.map (X ◁ g) = grayTensorBifunctor.map (𝟙 (ofGray.obj X), ofGray.map g) :=
  rfl

@[simp] theorem ofGray_map_whiskerRight {X X' : GrayDiagSet.{u}} (f : X ⟶ X')
    (Y : GrayDiagSet.{u}) :
    ofGray.map (f ▷ Y) = grayTensorBifunctor.map (ofGray.map f, 𝟙 (ofGray.obj Y)) :=
  rfl

@[simp] theorem ofGray_map_associator_hom (X Y Z : GrayDiagSet.{u}) :
    ofGray.map (α_ X Y Z).hom =
      (GrayDiagSet.associator (ofGray.obj X) (ofGray.obj Y) (ofGray.obj Z)).hom :=
  rfl

@[simp] theorem ofGray_map_associator_inv (X Y Z : GrayDiagSet.{u}) :
    ofGray.map (α_ X Y Z).inv =
      (GrayDiagSet.associator (ofGray.obj X) (ofGray.obj Y) (ofGray.obj Z)).inv :=
  rfl

@[simp] theorem ofGray_map_leftUnitor_hom (X : GrayDiagSet.{u}) :
    ofGray.map (λ_ X).hom = (GrayDiagSet.leftUnitor (ofGray.obj X)).hom :=
  rfl

@[simp] theorem ofGray_map_leftUnitor_inv (X : GrayDiagSet.{u}) :
    ofGray.map (λ_ X).inv = (GrayDiagSet.leftUnitor (ofGray.obj X)).inv :=
  rfl

@[simp] theorem ofGray_map_rightUnitor_hom (X : GrayDiagSet.{u}) :
    ofGray.map (ρ_ X).hom = (GrayDiagSet.rightUnitor (ofGray.obj X)).hom :=
  rfl

@[simp] theorem ofGray_map_rightUnitor_inv (X : GrayDiagSet.{u}) :
    ofGray.map (ρ_ X).inv = (GrayDiagSet.rightUnitor (ofGray.obj X)).inv :=
  rfl

end GrayDiagSet

@[reassoc] theorem grayTensor_leftSide_map {A B C D : DiagSet.{u}}
    (a : ball.{u} atomPoint ⟶ A) (f : A ⟶ C) (g : B ⟶ D) :
    (GrayDiagSet.leftUnitor B).inv ≫
        grayTensorBifunctor.map (X := (ball atomPoint, B)) (Y := (A, B)) (a, 𝟙 B) ≫
        grayTensorBifunctor.map (X := (A, B)) (Y := (C, D)) (f, g) =
      g ≫ (GrayDiagSet.leftUnitor D).inv ≫
        grayTensorBifunctor.map (X := (ball atomPoint, D)) (Y := (C, D)) (a ≫ f, 𝟙 D) := by
  have hm : grayTensorBifunctor.map (X := (ball atomPoint, B)) (Y := (A, B)) (a, 𝟙 B) ≫
    grayTensorBifunctor.map (X := (A, B)) (Y := (C, D)) (f, g) =
      grayTensorBifunctor.map (X := (ball atomPoint, B)) (Y := (ball atomPoint, D)) (𝟙 _, g) ≫
        grayTensorBifunctor.map (X := (ball atomPoint, D)) (Y := (C, D)) (a ≫ f, 𝟙 D) := by
    rw [← grayTensorBifunctor.map_comp, ← grayTensorBifunctor.map_comp]
    simp only [CategoryTheory.prod_comp, Category.id_comp, Category.comp_id]
  rw [hm, ← Category.assoc, GrayDiagSet.leftUnitor_inv_naturality, Category.assoc]

@[reassoc] theorem grayTensor_rightSide_map {A B C D : DiagSet.{u}}
    (a : ball.{u} atomPoint ⟶ B) (f : A ⟶ C) (g : B ⟶ D) :
    (GrayDiagSet.rightUnitor A).inv ≫
        grayTensorBifunctor.map (X := (A, ball atomPoint)) (Y := (A, B)) (𝟙 A, a) ≫
        grayTensorBifunctor.map (X := (A, B)) (Y := (C, D)) (f, g) =
      f ≫ (GrayDiagSet.rightUnitor C).inv ≫
        grayTensorBifunctor.map (X := (C, ball atomPoint)) (Y := (C, D)) (𝟙 C, a ≫ g) := by
  have hm : grayTensorBifunctor.map (X := (A, ball atomPoint)) (Y := (A, B)) (𝟙 A, a) ≫
    grayTensorBifunctor.map (X := (A, B)) (Y := (C, D)) (f, g) =
      grayTensorBifunctor.map (X := (A, ball atomPoint)) (Y := (C, ball atomPoint)) (f, 𝟙 _) ≫
        grayTensorBifunctor.map (X := (C, ball atomPoint)) (Y := (C, D)) (𝟙 C, a ≫ g) := by
    rw [← grayTensorBifunctor.map_comp, ← grayTensorBifunctor.map_comp]
    simp only [CategoryTheory.prod_comp, Category.id_comp, Category.comp_id]
  rw [hm, ← Category.assoc, GrayDiagSet.rightUnitor_inv_naturality, Category.assoc]

private theorem grayTensor_grayTensor_hom_ext {X Y Z T : DiagSet.{u}}
    {f g : grayTensor (grayTensor X Y) Z ⟶ T}
    (h : ∀ (U V W : Atom) (x : diagram X U) (y : diagram Y V) (z : diagram Z W),
      f.app _ (grayTensorCell (grayTensorCell x y) z) =
        g.app _ (grayTensorCell (grayTensorCell x y) z)) : f = g := by
  refine grayTensor_hom_ext fun A W w z => ?_
  obtain ⟨U, V, x, y, e, rfl⟩ := exists_eq_map_grayTensorCell w
  rw [← Functor.map_id_apply Z (op W) z, ← op_id, grayTensorCell_restrict,
    NatTrans.naturality_apply, NatTrans.naturality_apply, h]

private theorem grayTensorBallIso_hom_app_grayTensorCell_down {U V A B : Atom}
    (x : diagram (ball.{u} U) A) (y : diagram (ball.{u} V) B) :
    ((grayTensorBallIso.{u} U V).hom.app (op (Atom.grayTensor A B)) (grayTensorCell x y)).down =
      Atom.grayTensorMap x.down y.down :=
  congrArg ULift.down (grayTensorBallIso_hom_app_grayTensorCell x.down y.down)

theorem grayTensorBallIso_associativity (U V W : Atom) :
    grayTensorBifunctor.map ((grayTensorBallIso.{u} U V).hom, 𝟙 (ball W)) ≫
        (grayTensorBallIso (Atom.grayTensor U V) W).hom ≫
          uliftYoneda.map (Atom.grayTensorAssoc U V W).hom =
      (GrayDiagSet.associator (ball U) (ball V) (ball W)).hom ≫
        grayTensorBifunctor.map (𝟙 (ball U), (grayTensorBallIso V W).hom) ≫
          (grayTensorBallIso U (Atom.grayTensor V W)).hom := by
  refine grayTensor_grayTensor_hom_ext fun A B C a b c => ULift.ext _ _ ?_
  rw [NatTrans.comp_app_apply, NatTrans.comp_app_apply, NatTrans.comp_app_apply,
    NatTrans.comp_app_apply, grayTensorCell_naturality,
    GrayDiagSet.associator_hom_app_grayTensorCell, NatTrans.naturality_apply,
    grayTensorCell_naturality, NatTrans.naturality_apply]
  simp only [uliftYoneda_map_app, uliftYoneda_obj_map, NatTrans.id_app, types_id_apply,
    TypeCat.ofHom_apply, ULift.down_up, Quiver.Hom.unop_op,
    grayTensorBallIso_hom_app_grayTensorCell_down]
  exact Atom.grayTensorAssoc_naturality _ _ _

theorem grayTensorBallIso_left_unitality (U : Atom) :
    (GrayDiagSet.leftUnitor (ball.{u} U)).hom =
      (grayTensorBallIso atomPoint U).hom ≫ uliftYoneda.map (Atom.grayTensorLeftUnitor U).hom := by
  refine grayTensor_hom_ext fun A B a b => ULift.ext _ _ ?_
  rw [GrayDiagSet.leftUnitor_hom_app_grayTensorCell, NatTrans.comp_app_apply]
  simp only [uliftYoneda_map_app, uliftYoneda_obj_map, TypeCat.ofHom_apply, ULift.down_up,
    Quiver.Hom.unop_op, grayTensorBallIso_hom_app_grayTensorCell_down]
  rw [isTerminalAtomPoint.hom_ext a.down (toAtomPoint A), Category.assoc,
    ← Atom.grayTensorLeftUnitor_naturality, Atom.grayTensorMap_comp_assoc, Category.id_comp,
    Category.comp_id]

theorem grayTensorBallIso_right_unitality (U : Atom) :
    (GrayDiagSet.rightUnitor (ball.{u} U)).hom =
      (grayTensorBallIso U atomPoint).hom ≫ uliftYoneda.map (Atom.grayTensorRightUnitor U).hom := by
  refine grayTensor_hom_ext fun A B a b => ULift.ext _ _ ?_
  rw [GrayDiagSet.rightUnitor_hom_app_grayTensorCell, NatTrans.comp_app_apply]
  simp only [uliftYoneda_map_app, uliftYoneda_obj_map, TypeCat.ofHom_apply, ULift.down_up,
    Quiver.Hom.unop_op, grayTensorBallIso_hom_app_grayTensorCell_down]
  rw [isTerminalAtomPoint.hom_ext b.down (toAtomPoint B), Category.assoc,
    ← Atom.grayTensorRightUnitor_naturality, Atom.grayTensorMap_comp_assoc, Category.id_comp,
    Category.comp_id]

noncomputable def grayTensorFst (X Y : DiagSet.{u}) : grayTensor X Y ⟶ X :=
  grayTensorBifunctor.map (𝟙 X, isTerminalBallAtomPoint.from Y) ≫ (GrayDiagSet.rightUnitor X).hom

noncomputable def grayTensorSnd (X Y : DiagSet.{u}) : grayTensor X Y ⟶ Y :=
  grayTensorBifunctor.map (isTerminalBallAtomPoint.from X, 𝟙 Y) ≫ (GrayDiagSet.leftUnitor Y).hom

theorem grayTensorFst_app_grayTensorCell {X Y : DiagSet.{u}} {U V : Atom}
    (x : diagram X U) (y : diagram Y V) :
    (grayTensorFst X Y).app (op (Atom.grayTensor U V)) (grayTensorCell x y) =
      X.map (Atom.grayTensorMap (𝟙 U) (toAtomPoint V) ≫ (Atom.grayTensorRightUnitor U).hom).op
        x := by
  rw [grayTensorFst, NatTrans.comp_app_apply, grayTensorCell_naturality, NatTrans.id_app,
    types_id_apply, GrayDiagSet.rightUnitor_hom_app_grayTensorCell]

theorem grayTensorSnd_app_grayTensorCell {X Y : DiagSet.{u}} {U V : Atom}
    (x : diagram X U) (y : diagram Y V) :
    (grayTensorSnd X Y).app (op (Atom.grayTensor U V)) (grayTensorCell x y) =
      Y.map (Atom.grayTensorMap (toAtomPoint U) (𝟙 V) ≫ (Atom.grayTensorLeftUnitor V).hom).op
        y := by
  rw [grayTensorSnd, NatTrans.comp_app_apply, grayTensorCell_naturality, NatTrans.id_app,
    types_id_apply, GrayDiagSet.leftUnitor_hom_app_grayTensorCell]

@[reassoc]
theorem grayTensorBifunctor_map_grayTensorFst {X Y X' Y' : DiagSet.{u}} (f : X ⟶ X')
    (g : Y ⟶ Y') :
    grayTensorBifunctor.map (f, g) ≫ grayTensorFst X' Y' = grayTensorFst X Y ≫ f :=
  grayTensor_hom_ext fun U V x y => by
    rw [NatTrans.comp_app_apply, NatTrans.comp_app_apply, grayTensorCell_naturality,
      grayTensorFst_app_grayTensorCell, grayTensorFst_app_grayTensorCell, NatTrans.naturality_apply]

@[reassoc]
theorem grayTensorBifunctor_map_grayTensorSnd {X Y X' Y' : DiagSet.{u}} (f : X ⟶ X')
    (g : Y ⟶ Y') :
    grayTensorBifunctor.map (f, g) ≫ grayTensorSnd X' Y' = grayTensorSnd X Y ≫ g :=
  grayTensor_hom_ext fun U V x y => by
    rw [NatTrans.comp_app_apply, NatTrans.comp_app_apply, grayTensorCell_naturality,
      grayTensorSnd_app_grayTensorCell, grayTensorSnd_app_grayTensorCell, NatTrans.naturality_apply]

theorem grayTensorFst_point (X : DiagSet.{u}) :
    grayTensorFst X (ball.{u} atomPoint) = (GrayDiagSet.rightUnitor X).hom := by
  rw [grayTensorFst, isTerminalBallAtomPoint.hom_ext
    (isTerminalBallAtomPoint.from (ball.{u} atomPoint)) (𝟙 _)]
  have hid : (𝟙 X, 𝟙 (ball.{u} atomPoint)) = 𝟙 (X, ball.{u} atomPoint) := rfl
  rw [hid, grayTensorBifunctor.map_id, Category.id_comp]

theorem grayTensorSnd_unit (X : DiagSet.{u}) :
    grayTensorSnd (ball.{u} atomPoint) X = (GrayDiagSet.leftUnitor X).hom := by
  rw [grayTensorSnd, isTerminalBallAtomPoint.hom_ext
    (isTerminalBallAtomPoint.from (ball.{u} atomPoint)) (𝟙 _)]
  have hid : (𝟙 (ball.{u} atomPoint), 𝟙 X) = 𝟙 (ball.{u} atomPoint, X) := rfl
  rw [hid, grayTensorBifunctor.map_id, Category.id_comp]

noncomputable def grayTensorToProd (X Y : DiagSet.{u}) : grayTensor X Y ⟶ X ⨯ Y :=
  prod.lift (grayTensorFst X Y) (grayTensorSnd X Y)

theorem grayTensorFst_ball (U V : Atom) :
    grayTensorFst (ball.{u} U) (ball.{u} V) = (grayTensorBallIso U V).hom ≫
      uliftYoneda.map (Atom.grayTensorMap (𝟙 U) (toAtomPoint V) ≫
        (Atom.grayTensorRightUnitor U).hom) := by
  refine grayTensor_hom_ext fun A B a b => ULift.ext _ _ ?_
  rw [grayTensorFst_app_grayTensorCell, NatTrans.comp_app_apply]
  simp only [uliftYoneda_map_app, uliftYoneda_obj_map, TypeCat.ofHom_apply, ULift.down_up,
    Quiver.Hom.unop_op, grayTensorBallIso_hom_app_grayTensorCell_down]
  have e : Atom.grayTensorMap a.down b.down ≫ Atom.grayTensorMap (𝟙 U) (toAtomPoint V) =
      Atom.grayTensorMap (𝟙 A) (toAtomPoint B) ≫ Atom.grayTensorMap a.down (𝟙 atomPoint) := by
    rw [Atom.grayTensorMap_comp, Atom.grayTensorMap_comp]
    simp only [Category.comp_id, Category.id_comp]
    rw [isTerminalAtomPoint.hom_ext (b.down ≫ toAtomPoint V) (toAtomPoint B)]
  rw [Category.assoc, ← Atom.grayTensorRightUnitor_naturality, reassoc_of% e]

theorem grayTensorSnd_ball (U V : Atom) :
    grayTensorSnd (ball.{u} U) (ball.{u} V) = (grayTensorBallIso U V).hom ≫
      uliftYoneda.map (Atom.grayTensorMap (toAtomPoint U) (𝟙 V) ≫
        (Atom.grayTensorLeftUnitor V).hom) := by
  refine grayTensor_hom_ext fun A B a b => ULift.ext _ _ ?_
  rw [grayTensorSnd_app_grayTensorCell, NatTrans.comp_app_apply]
  simp only [uliftYoneda_map_app, uliftYoneda_obj_map, TypeCat.ofHom_apply, ULift.down_up,
    Quiver.Hom.unop_op, grayTensorBallIso_hom_app_grayTensorCell_down]
  have e : Atom.grayTensorMap a.down b.down ≫ Atom.grayTensorMap (toAtomPoint U) (𝟙 V) =
      Atom.grayTensorMap (toAtomPoint A) (𝟙 B) ≫ Atom.grayTensorMap (𝟙 atomPoint) b.down := by
    rw [Atom.grayTensorMap_comp, Atom.grayTensorMap_comp]
    simp only [Category.comp_id, Category.id_comp]
    rw [isTerminalAtomPoint.hom_ext (a.down ≫ toAtomPoint U) (toAtomPoint A)]
  rw [Category.assoc, ← Atom.grayTensorLeftUnitor_naturality, reassoc_of% e]

instance mono_grayTensorToProd_ball (U V : Atom) :
    Mono (grayTensorToProd (ball.{u} U) (ball.{u} V)) := by
  refine ⟨fun {Z} g h e => ?_⟩
  have e1 := congrArg (· ≫ prod.fst) e
  have e2 := congrArg (· ≫ prod.snd) e
  simp only [Category.assoc, grayTensorToProd, prod.lift_fst, prod.lift_snd, grayTensorFst_ball,
    grayTensorSnd_ball] at e1 e2
  rw [← cancel_mono (grayTensorBallIso.{u} U V).hom]
  refine NatTrans.ext (funext fun T => ConcreteCategory.hom_ext (C := Type u) _ _ fun z =>
    ULift.ext _ _ ?_)
  have h1 := ConcreteCategory.congr_hom (congr_app e1 T) z
  have h2 := ConcreteCategory.congr_hom (congr_app e2 T) z
  simp only [NatTrans.comp_app_apply, uliftYoneda_map_app, TypeCat.ofHom_apply] at h1 h2
  rw [NatTrans.comp_app_apply, NatTrans.comp_app_apply]
  exact Atom.grayTensor.hom_ext (congrArg ULift.down h1) (congrArg ULift.down h2)

namespace GrayDiagSet

noncomputable instance : SemiCartesianMonoidalCategory GrayDiagSet.{u} :=
  { instMonoidalCategory with
    isTerminalTensorUnit := isTerminalBallAtomPoint
    fst := fun X Y => toGray.map (grayTensorFst (ofGray.obj X) (ofGray.obj Y))
    snd := fun X Y => toGray.map (grayTensorSnd (ofGray.obj X) (ofGray.obj Y))
    fst_def := fun _ _ => rfl
    snd_def := fun _ _ => rfl }

@[simp] theorem ofGray_map_fst (X Y : GrayDiagSet.{u}) :
    ofGray.map (SemiCartesianMonoidalCategory.fst X Y) =
      grayTensorFst (ofGray.obj X) (ofGray.obj Y) :=
  rfl

@[simp] theorem ofGray_map_snd (X Y : GrayDiagSet.{u}) :
    ofGray.map (SemiCartesianMonoidalCategory.snd X Y) =
      grayTensorSnd (ofGray.obj X) (ofGray.obj Y) :=
  rfl

instance : HasColimits GrayDiagSet.{u} :=
  inferInstanceAs (HasColimits DiagSet.{u})

instance (X : GrayDiagSet.{u}) :
    PreservesColimitsOfSize.{w, w'} (MonoidalCategory.tensorLeft X) :=
  inferInstanceAs (PreservesColimitsOfSize.{w, w'} (grayTensorLeft (ofGray.obj X)))

instance (X : GrayDiagSet.{u}) :
    PreservesColimitsOfSize.{w, w'} (MonoidalCategory.tensorRight X) :=
  inferInstanceAs (PreservesColimitsOfSize.{w, w'} (grayTensorRight (ofGray.obj X)))

noncomputable instance : MonoidalClosed GrayDiagSet.{u} where
  closed X :=
    { rightAdj := grayHomLeft (ofGray.obj X)
      adj := grayTensorLeftAdjunction (ofGray.obj X) }

end GrayDiagSet

end Atoms.Diagrammatic
