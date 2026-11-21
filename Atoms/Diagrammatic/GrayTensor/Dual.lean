import Atoms.Diagrammatic.GrayTensor.Pasting
import Atoms.Diagrammatic.Pasting.Dual

open CategoryTheory Opposite Atoms.Molecule Atoms.Molecule.OGP Atoms.Shape
open scoped MonoidalCategory.ExternalProduct

universe u

namespace Atoms.Diagrammatic

variable {X Y : DiagSet.{u}}

private abbrev dualCell (J : ℕ → Bool) {Z : DiagSet.{u}} {V : Atom} (z : diagram Z V) :
    diagram ((DiagSet.dual J).obj Z) (V.dual J) :=
  Z.map (Atom.dualDualIso J V).hom.op z

private theorem map_dualDualIso_map (J : ℕ → Bool) (Z : DiagSet.{u}) {V V' : Atom} (g : V ⟶ V')
    (z : diagram Z V') :
    Z.map (Atom.dualDualIso J V).hom.op (Z.map g.op z) =
      Z.map (Atom.dualMap J (Atom.dualMap J g)).op (Z.map (Atom.dualDualIso J V').hom.op z) := by
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp]
  exact congrArg (fun f => Z.map f.op z) ((Atom.dualFunctorCompIso J).hom.naturality g).symm

private theorem map_dualDualIso_inv_map (J : ℕ → Bool) (Z : DiagSet.{u}) {V : Atom}
    (z : diagram Z V) :
    Z.map (Atom.dualDualIso J V).inv.op (Z.map (Atom.dualDualIso J V).hom.op z) = z := by
  rw [← Functor.map_comp_apply, ← op_comp, Iso.inv_hom_id, op_id, Functor.map_id_apply]

private theorem dual_map_dualDualIso (J : ℕ → Bool) (Z : DiagSet.{u}) {V : Atom}
    (z : diagram ((DiagSet.dual J).obj Z) V) :
    ((DiagSet.dual J).obj Z).map (Atom.dualDualIso J V).hom.op z =
      dualCell J (Z := Z) (V := V.dual J) z := by
  rw [DiagSet.dual_obj_map, Quiver.Hom.unop_op, ← Atom.dualFunctor_map,
    Atom.dualFunctor_map_dualDualIso_hom]
  rfl

private noncomputable def toDualUnit (X Y : DiagSet.{u}) :
    X ⊠ Y ⟶ grayTensorIndex ⋙ (DiagSet.dual Nat.bodd).obj
      (grayTensor ((DiagSet.dual Nat.bodd).obj Y) ((DiagSet.dual Nat.bodd).obj X)) where
  app p := ↾fun xy => (grayTensor ((DiagSet.dual Nat.bodd).obj Y)
      ((DiagSet.dual Nat.bodd).obj X)).map (Atom.grayTensorDualIso p.1.unop p.2.unop).hom.op
    (grayTensorCell (Y.map (Atom.dualDualIso Nat.bodd p.2.unop).hom.op xy.2)
      (X.map (Atom.dualDualIso Nat.bodd p.1.unop).hom.op xy.1))
  naturality p q f := by
    ext ⟨x, y⟩
    change (grayTensor _ _).map (Atom.grayTensorDualIso q.1.unop q.2.unop).hom.op
      (grayTensorCell (X := (DiagSet.dual Nat.bodd).obj Y) (Y := (DiagSet.dual Nat.bodd).obj X)
        (Y.map (Atom.dualDualIso Nat.bodd q.2.unop).hom.op (Y.map f.2.unop.op y))
        (X.map (Atom.dualDualIso Nat.bodd q.1.unop).hom.op (X.map f.1.unop.op x))) =
      (grayTensor _ _).map (Atom.dualMap Nat.bodd (Atom.grayTensorMap f.1.unop f.2.unop)).op
        ((grayTensor _ _).map (Atom.grayTensorDualIso p.1.unop p.2.unop).hom.op
          (grayTensorCell (X := (DiagSet.dual Nat.bodd).obj Y) (Y := (DiagSet.dual Nat.bodd).obj X)
            (Y.map (Atom.dualDualIso Nat.bodd p.2.unop).hom.op y)
            (X.map (Atom.dualDualIso Nat.bodd p.1.unop).hom.op x)))
    rw [map_dualDualIso_map, map_dualDualIso_map]
    refine (congrArg _ (grayTensorCell_restrict (X := (DiagSet.dual Nat.bodd).obj Y)
      (Y := (DiagSet.dual Nat.bodd).obj X) (Atom.dualMap Nat.bodd f.2.unop)
      (Atom.dualMap Nat.bodd f.1.unop) _ _)).trans ?_
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp,
      Atom.grayTensorDualIso_hom_naturality]

private noncomputable def ofDualUnit (X Y : DiagSet.{u}) :
    (DiagSet.dual Nat.bodd).obj Y ⊠ (DiagSet.dual Nat.bodd).obj X ⟶
      grayTensorIndex ⋙ (DiagSet.dual Nat.bodd).obj (grayTensor X Y) where
  app p := ↾fun yx => (grayTensor X Y).map (Atom.grayTensorDualIso p.1.unop p.2.unop).hom.op
    (grayTensorCell yx.2 yx.1)
  naturality p q f := by
    ext ⟨y, x⟩
    change (grayTensor X Y).map (Atom.grayTensorDualIso q.1.unop q.2.unop).hom.op
      (grayTensorCell (X.map (Atom.dualMap Nat.bodd f.2.unop).op x)
        (Y.map (Atom.dualMap Nat.bodd f.1.unop).op y)) =
      (grayTensor X Y).map (Atom.dualMap Nat.bodd (Atom.grayTensorMap f.1.unop f.2.unop)).op
        ((grayTensor X Y).map (Atom.grayTensorDualIso p.1.unop p.2.unop).hom.op
          (grayTensorCell x y))
    refine (congrArg _ (grayTensorCell_restrict (X := X) (Y := Y) (Atom.dualMap Nat.bodd f.2.unop)
      (Atom.dualMap Nat.bodd f.1.unop) x y)).trans ?_
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp,
      Atom.grayTensorDualIso_hom_naturality]

private noncomputable def toDual (X Y : DiagSet.{u}) :
    grayTensor X Y ⟶ (DiagSet.dual Nat.bodd).obj
      (grayTensor ((DiagSet.dual Nat.bodd).obj Y) ((DiagSet.dual Nat.bodd).obj X)) :=
  (grayTensor X Y).descOfIsLeftKanExtension (grayTensorUnit X Y) _ (toDualUnit X Y)

private noncomputable def ofDual (X Y : DiagSet.{u}) :
    grayTensor ((DiagSet.dual Nat.bodd).obj Y) ((DiagSet.dual Nat.bodd).obj X) ⟶
      (DiagSet.dual Nat.bodd).obj (grayTensor X Y) :=
  (grayTensor _ _).descOfIsLeftKanExtension (grayTensorUnit _ _) _ (ofDualUnit X Y)

private theorem toDual_app_grayTensorCell {U V : Atom} (x : diagram X U) (y : diagram Y V) :
    (toDual X Y).app (op (Atom.grayTensor U V)) (grayTensorCell x y) =
      (grayTensor ((DiagSet.dual Nat.bodd).obj Y) ((DiagSet.dual Nat.bodd).obj X)).map
        (Atom.grayTensorDualIso U V).hom.op
        (grayTensorCell (dualCell Nat.bodd y) (dualCell Nat.bodd x)) :=
  ConcreteCategory.congr_hom
    ((grayTensor X Y).descOfIsLeftKanExtension_fac_app (grayTensorUnit X Y) _ (toDualUnit X Y)
      (op U, op V)) ((x, y) : X.obj (op U) × Y.obj (op V))

private theorem ofDual_app_grayTensorCell {U V : Atom}
    (y : diagram ((DiagSet.dual Nat.bodd).obj Y) U)
    (x : diagram ((DiagSet.dual Nat.bodd).obj X) V) :
    (ofDual X Y).app (op (Atom.grayTensor U V)) (grayTensorCell y x) =
      (grayTensor X Y).map (Atom.grayTensorDualIso U V).hom.op
        (grayTensorCell (X := X) (Y := Y) (U := V.dual Nat.bodd) (V := U.dual Nat.bodd) x y) :=
  ConcreteCategory.congr_hom
    ((grayTensor _ _).descOfIsLeftKanExtension_fac_app (grayTensorUnit _ _) _ (ofDualUnit X Y)
      (op U, op V)) ((y, x) : ((DiagSet.dual Nat.bodd).obj Y).obj (op U) ×
        ((DiagSet.dual Nat.bodd).obj X).obj (op V))

theorem dual_grayTensor_hom_ext (J : ℕ → Bool) {Z : DiagSet.{u}}
    {f g : (DiagSet.dual J).obj (grayTensor X Y) ⟶ Z}
    (h : ∀ (U V : Atom) (x : diagram X U) (y : diagram Y V),
      f.app (op ((Atom.grayTensor U V).dual J))
          ((grayTensor X Y).map (Atom.dualDualIso J (Atom.grayTensor U V)).hom.op
            (grayTensorCell x y)) =
        g.app (op ((Atom.grayTensor U V).dual J))
          ((grayTensor X Y).map (Atom.dualDualIso J (Atom.grayTensor U V)).hom.op
            (grayTensorCell x y))) : f = g := by
  apply (DiagSet.dualEquivalence.{u} J).functor.map_injective
  change (DiagSet.dual J).map f = (DiagSet.dual J).map g
  rw [← cancel_epi (DiagSet.dualDualIso J (grayTensor X Y)).inv]
  exact grayTensor_hom_ext fun U V x y => h U V x y

private noncomputable def dualHom (X Y : DiagSet.{u}) :
    (DiagSet.dual Nat.bodd).obj (grayTensor X Y) ⟶
      grayTensor ((DiagSet.dual Nat.bodd).obj Y) ((DiagSet.dual Nat.bodd).obj X) :=
  (DiagSet.dual Nat.bodd).map (toDual X Y) ≫ (DiagSet.dualDualIso Nat.bodd _).hom

private theorem dualHom_app_grayTensorCell {U V : Atom} (x : diagram X U) (y : diagram Y V) :
    (dualHom X Y).app (op ((Atom.grayTensor U V).dual Nat.bodd))
        ((grayTensor X Y).map (Atom.dualDualIso Nat.bodd (Atom.grayTensor U V)).hom.op
          (grayTensorCell x y)) =
      (grayTensor ((DiagSet.dual Nat.bodd).obj Y) ((DiagSet.dual Nat.bodd).obj X)).map
        (Atom.grayTensorDualIso U V).hom.op
        (grayTensorCell (dualCell Nat.bodd y) (dualCell Nat.bodd x)) := by
  change (grayTensor _ _).map
    (Atom.dualDualIso Nat.bodd ((Atom.grayTensor U V).dual Nat.bodd)).inv.op
    ((toDual X Y).app _ ((grayTensor X Y).map
      (Atom.dualDualIso Nat.bodd (Atom.grayTensor U V)).hom.op (grayTensorCell x y))) = _
  rw [NatTrans.naturality_apply, toDual_app_grayTensorCell]
  change (grayTensor _ _).map
    (Atom.dualDualIso Nat.bodd ((Atom.grayTensor U V).dual Nat.bodd)).inv.op
    ((grayTensor _ _).map (Atom.dualMap Nat.bodd (Atom.dualDualIso Nat.bodd _).hom).op _) = _
  rw [← Atom.dualFunctor_map, Atom.dualFunctor_map_dualDualIso_hom, map_dualDualIso_inv_map]

noncomputable def grayTensorDualIso (X Y : DiagSet.{u}) :
    (DiagSet.dual Nat.bodd).obj (grayTensor X Y) ≅
      grayTensor ((DiagSet.dual Nat.bodd).obj Y) ((DiagSet.dual Nat.bodd).obj X) where
  hom := dualHom X Y
  inv := ofDual X Y
  hom_inv_id := dual_grayTensor_hom_ext Nat.bodd fun U V x y => by
    change (ofDual X Y).app (op ((Atom.grayTensor U V).dual Nat.bodd))
      ((dualHom X Y).app (op ((Atom.grayTensor U V).dual Nat.bodd)) ((grayTensor X Y).map
      (Atom.dualDualIso Nat.bodd (Atom.grayTensor U V)).hom.op (grayTensorCell x y))) =
        (grayTensor X Y).map (Atom.dualDualIso Nat.bodd (Atom.grayTensor U V)).hom.op
          (grayTensorCell x y)
    rw [dualHom_app_grayTensorCell, NatTrans.naturality_apply,
      ofDual_app_grayTensorCell (dualCell Nat.bodd y) (dualCell Nat.bodd x)]
    refine (congrArg (fun c => (grayTensor X Y).map
      (Atom.dualMap Nat.bodd (Atom.grayTensorDualIso U V).hom).op ((grayTensor X Y).map
        (Atom.grayTensorDualIso (V.dual Nat.bodd) (U.dual Nat.bodd)).hom.op c))
      (grayTensorCell_restrict (X := X) (Y := Y) (Atom.dualDualIso Nat.bodd U).hom
        (Atom.dualDualIso Nat.bodd V).hom x y)).trans ?_
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp]
    simp only [Category.assoc]
    rw [Atom.dualMap_grayTensorDualIso_hom_comp]
  inv_hom_id := grayTensor_hom_ext fun U V y x => by
    change (dualHom X Y).app _ ((ofDual X Y).app _ (grayTensorCell y x)) = grayTensorCell y x
    rw [ofDual_app_grayTensorCell]
    change (grayTensor _ _).map (Atom.dualDualIso Nat.bodd (Atom.grayTensor U V)).inv.op
      ((toDual X Y).app (op ((Atom.grayTensor U V).dual Nat.bodd))
        ((grayTensor X Y).map (Atom.grayTensorDualIso U V).hom.op
        (grayTensorCell (X := X) (Y := Y) (U := V.dual Nat.bodd) (V := U.dual Nat.bodd) x y))) = _
    rw [NatTrans.naturality_apply, toDual_app_grayTensorCell (X := X) (Y := Y)
      (U := V.dual Nat.bodd) (V := U.dual Nat.bodd) x y]
    change (grayTensor _ _).map (Atom.dualDualIso Nat.bodd (Atom.grayTensor U V)).inv.op
      ((grayTensor _ _).map (Atom.dualMap Nat.bodd (Atom.grayTensorDualIso U V).hom).op
        ((grayTensor _ _).map (Atom.grayTensorDualIso _ _).hom.op
          (grayTensorCell (dualCell Nat.bodd y) (dualCell Nat.bodd x)))) = _
    rw [← dual_map_dualDualIso, ← dual_map_dualDualIso, grayTensorCell_restrict,
      ← Functor.map_comp_apply, ← Functor.map_comp_apply,
      ← Functor.map_comp_apply, ← op_comp, ← op_comp, ← op_comp]
    simp only [Category.assoc]
    rw [Atom.dualMap_grayTensorDualIso_hom_comp, Iso.inv_hom_id, op_id, Functor.map_id_apply]

theorem grayTensorDualIso_hom_app_grayTensorCell {U V : Atom} (x : diagram X U)
    (y : diagram Y V) :
    (grayTensorDualIso X Y).hom.app (op ((Atom.grayTensor U V).dual Nat.bodd))
        ((grayTensor X Y).map (Atom.dualDualIso Nat.bodd (Atom.grayTensor U V)).hom.op
          (grayTensorCell x y)) =
      (grayTensor ((DiagSet.dual Nat.bodd).obj Y) ((DiagSet.dual Nat.bodd).obj X)).map
        (Atom.grayTensorDualIso U V).hom.op
        (grayTensorCell (Y.map (Atom.dualDualIso Nat.bodd V).hom.op y)
          (X.map (Atom.dualDualIso Nat.bodd U).hom.op x)) :=
  dualHom_app_grayTensorCell x y

@[reassoc]
theorem grayTensorDualIso_hom_naturality {X' Y' : DiagSet.{u}} (f : X ⟶ X') (g : Y ⟶ Y') :
    (DiagSet.dual Nat.bodd).map (grayTensorBifunctor.map (f, g)) ≫
        (grayTensorDualIso X' Y').hom =
      (grayTensorDualIso X Y).hom ≫
        grayTensorBifunctor.map ((DiagSet.dual Nat.bodd).map g, (DiagSet.dual Nat.bodd).map f) :=
  dual_grayTensor_hom_ext Nat.bodd fun U V x y => by
    have h1 : (grayTensorBifunctor.map (f, g)).app
        (op (((Atom.grayTensor U V).dual Nat.bodd).dual Nat.bodd))
        ((grayTensor X Y).map (Atom.dualDualIso Nat.bodd (Atom.grayTensor U V)).hom.op
          (grayTensorCell x y)) =
        (grayTensor X' Y').map (Atom.dualDualIso Nat.bodd (Atom.grayTensor U V)).hom.op
          (grayTensorCell (f.app _ x) (g.app _ y)) := by
      rw [NatTrans.naturality_apply, grayTensorCell_naturality]
    refine (congrArg ((grayTensorDualIso X' Y').hom.app _) h1).trans
      ((grayTensorDualIso_hom_app_grayTensorCell (f.app _ x) (g.app _ y)).trans ?_)
    refine Eq.trans ?_ (congrArg ((grayTensorBifunctor.map _).app _)
      (grayTensorDualIso_hom_app_grayTensorCell x y)).symm
    rw [NatTrans.naturality_apply]
    refine Eq.trans ?_ (congrArg _ (grayTensorCell_naturality (X := (DiagSet.dual Nat.bodd).obj Y)
      (Y := (DiagSet.dual Nat.bodd).obj X) ((DiagSet.dual Nat.bodd).map g)
      ((DiagSet.dual Nat.bodd).map f) (dualCell Nat.bodd y) (dualCell Nat.bodd x))).symm
    exact congrArg _ (congrArg₂ grayTensorCell
      (NatTrans.naturality_apply g (Atom.dualDualIso Nat.bodd V).hom.op y).symm
      (NatTrans.naturality_apply f (Atom.dualDualIso Nat.bodd U).hom.op x).symm)

end Atoms.Diagrammatic

namespace Atoms.Molecule.MoleculeShape

def grayProductDualIso (P Q : MoleculeShape) :
    ((P.grayProduct Q).dual Nat.bodd).ogp ≅
      ((Q.dual Nat.bodd).grayProduct (P.dual Nat.bodd)).ogp :=
  ((P.grayProduct Q).dualIso Nat.bodd).symm ≪≫
    (OGP.dualFunctor Nat.bodd).mapIso (P.grayProductIso Q).symm ≪≫ grayProductSwap P.ogp Q.ogp ≪≫
    MonoidalCategory.tensorIso (Q.dualIso Nat.bodd) (P.dualIso Nat.bodd) ≪≫
      (Q.dual Nat.bodd).grayProductIso (P.dual Nat.bodd)

theorem grayProductDualIso_hom_apply (P Q : MoleculeShape)
    (z : ((P.grayProduct Q).dual Nat.bodd).ogp) :
    (grayProductDualIso P Q).hom z = ((Q.dual Nat.bodd).grayProductIso (P.dual Nat.bodd)).hom
      ((Q.dualIso Nat.bodd).hom
          ((P.grayProductIso Q).inv (((P.grayProduct Q).dualIso Nat.bodd).inv z)).2,
        (P.dualIso Nat.bodd).hom
          ((P.grayProductIso Q).inv (((P.grayProduct Q).dualIso Nat.bodd).inv z)).1) :=
  rfl

end Atoms.Molecule.MoleculeShape

namespace Atoms.Diagrammatic

variable {X Y : DiagSet.{u}}

private noncomputable def realizeShapeDualIso (J : ℕ → Bool) (S : MoleculeShape) :
    realize.{u}.obj (S.dual J).rdc ≅ (DiagSet.dual J).obj (realize.obj S.rdc) :=
  realize.mapIso (RDCpx.isoOfIso (P := (S.dual J).rdc) (Q := (RDCpx.dualFunctor J).obj S.rdc)
    (S.dualIso J).symm) ≪≫ realizeDualIso J S.rdc

private noncomputable def realizeShapeGrayIso (P Q : MoleculeShape) :
    realize.{u}.obj (P.grayProduct Q).rdc ≅ grayTensor (realize.obj P.rdc) (realize.obj Q.rdc) :=
  realize.mapIso (RDCpx.isoOfIso (P := (P.grayProduct Q).rdc) (Q := grayProductRDC P.rdc Q.rdc)
    (P.grayProductIso Q).symm) ≪≫ realizeGrayProductIso P.rdc Q.rdc

private def dualCellMap (J : ℕ → Bool) {B : Atom} {Q : MoleculeShape}
    (y : atomToRDCpx.obj B ⟶ Q.rdc) :
    atomToRDCpx.obj (B.dual J) ⟶ (Q.dual J).rdc :=
  (RDCpx.isoOfIso (P := (RDCpx.dualFunctor J).obj B.rdc) (Q := (B.dual J).rdc)
      (B.toMoleculeShape.dualIso J)).inv ≫ (RDCpx.dualFunctor J).map y ≫
    (RDCpx.isoOfIso (P := (RDCpx.dualFunctor J).obj Q.rdc) (Q := (Q.dual J).rdc)
      (Q.dualIso J)).hom

private theorem realizeShapeDualIso_hom_app_dualCellMap (J : ℕ → Bool) {B : Atom}
    {Q : MoleculeShape} (y : atomToRDCpx.obj B ⟶ Q.rdc) :
    (realizeShapeDualIso.{u} J Q).hom.app (op (B.dual J)) ⟨dualCellMap J y⟩ =
      (realize.{u}.obj Q.rdc).map (Atom.dualDualIso J B).hom.op ⟨y⟩ :=
  ULift.ext _ _ (WideSubcategory.hom_ext _ (ConcreteCategory.hom_ext _ _ fun _ =>
    (Q.dualIso J).hom_inv_id_apply _))

private theorem realizeGrayProductIso_hom_comp_app {P Q : RDCpx.{0}} {Z₁ Z₂ : DiagSet.{u}}
    (f₁ : realize.{u}.obj P ⟶ Z₁) (f₂ : realize.{u}.obj Q ⟶ Z₂) {T B A : Atom}
    (g : T ⟶ Atom.grayTensor B A) (a : atomToRDCpx.obj B ⟶ P) (b : atomToRDCpx.obj A ⟶ Q) :
    ((realizeGrayProductIso.{u} P Q).hom ≫ grayTensorBifunctor.map (f₁, f₂)).app (op T)
        ⟨atomToRDCpx.map g ≫ grayProductCellMap a b⟩ =
      (grayTensor Z₁ Z₂).map g.op (grayTensorCell (f₁.app _ ⟨a⟩) (f₂.app _ ⟨b⟩)) := by
  have h : (⟨atomToRDCpx.map g ≫ grayProductCellMap a b⟩ :
      (realize.{u}.obj (grayProductRDC P Q)).obj (op T)) =
      (realize.{u}.obj (grayProductRDC P Q)).map g.op
        ((realizeGrayProductIso.{u} P Q).inv.app _ (grayTensorCell (X := realize.{u}.obj P)
          (Y := realize.{u}.obj Q) ⟨a⟩ ⟨b⟩)) := by
    rw [realizeGrayProductIso_inv_app_grayTensorCell]
    rfl
  rw [h, NatTrans.comp_app, types_comp_apply, NatTrans.naturality_apply,
    Iso.inv_hom_id_app_apply, NatTrans.naturality_apply]
  exact congrArg ((grayTensor Z₁ Z₂).map g.op) (grayTensorCell_naturality f₁ f₂ _ _)

private theorem dualCellMap_grayProductCellMap {P Q : MoleculeShape} {A B : Atom}
    (x : atomToRDCpx.obj A ⟶ P.rdc) (y : atomToRDCpx.obj B ⟶ Q.rdc) :
    dualCellMap Nat.bodd (grayProductCellMap x y ≫ (RDCpx.isoOfIso (P := (P.grayProduct Q).rdc)
          (Q := grayProductRDC P.rdc Q.rdc) (P.grayProductIso Q).symm).inv) ≫
        (RDCpx.isoOfIso (P := ((P.grayProduct Q).dual Nat.bodd).rdc)
          (Q := ((Q.dual Nat.bodd).grayProduct (P.dual Nat.bodd)).rdc)
          (MoleculeShape.grayProductDualIso P Q)).hom ≫
        (RDCpx.isoOfIso (P := ((Q.dual Nat.bodd).grayProduct (P.dual Nat.bodd)).rdc)
          (Q := grayProductRDC (Q.dual Nat.bodd).rdc (P.dual Nat.bodd).rdc)
          ((Q.dual Nat.bodd).grayProductIso (P.dual Nat.bodd)).symm).hom =
      atomToRDCpx.map (Atom.grayTensorDualIso A B).hom ≫
        grayProductCellMap (dualCellMap Nat.bodd y) (dualCellMap Nat.bodd x) := by
  refine WideSubcategory.hom_ext _ (ConcreteCategory.hom_ext _ _ fun t => ?_)
  let p := (Atom.grayTensorIso A B).inv (((A.grayTensor B).toMoleculeShape.dualIso Nat.bodd).inv t)
  change ((Q.dual Nat.bodd).grayProductIso (P.dual Nat.bodd)).inv
      ((MoleculeShape.grayProductDualIso P Q).hom (((P.grayProduct Q).dualIso Nat.bodd).hom
        ((P.grayProductIso Q).hom
          (ConcreteCategory.hom x.hom p.1, ConcreteCategory.hom y.hom p.2)))) =
    (ConcreteCategory.hom (dualCellMap Nat.bodd y).hom
        ((Atom.grayTensorIso _ _).inv ((Atom.grayTensorDualIso A B).hom t)).1,
      ConcreteCategory.hom (dualCellMap Nat.bodd x).hom
        ((Atom.grayTensorIso _ _).inv ((Atom.grayTensorDualIso A B).hom t)).2)
  rw [MoleculeShape.grayProductDualIso_hom_apply, Atom.grayTensorDualIso_hom_apply]
  simp only [Iso.hom_inv_id_apply]
  exact Prod.ext (congrArg (fun w => ConcreteCategory.hom (Q.dualIso Nat.bodd).hom
      (ConcreteCategory.hom y.hom w))
      ((B.toMoleculeShape.dualIso Nat.bodd).hom_inv_id_apply _)).symm
    (congrArg (fun w => ConcreteCategory.hom (P.dualIso Nat.bodd).hom
      (ConcreteCategory.hom x.hom w))
      ((A.toMoleculeShape.dualIso Nat.bodd).hom_inv_id_apply _)).symm

private theorem realizeShapeDualIso_inv_app (J : ℕ → Bool) {T : Atom} {S : MoleculeShape}
    (k : atomToRDCpx.obj T ⟶ S.rdc) :
    (realizeShapeDualIso.{u} J S).inv.app (op (T.dual J))
        ((realize.{u}.obj S.rdc).map (Atom.dualDualIso J T).hom.op ⟨k⟩) = ⟨dualCellMap J k⟩ :=
  (congrArg ((realizeShapeDualIso.{u} J S).inv.app (op (T.dual J)))
    (realizeShapeDualIso_hom_app_dualCellMap J k).symm).trans
    (Iso.hom_inv_id_app_apply _ _ _)

private noncomputable def swapRealize (P Q : MoleculeShape) :
    realize.{u}.obj ((P.grayProduct Q).dual Nat.bodd).rdc ⟶
      grayTensor ((DiagSet.dual Nat.bodd).obj (realize.obj Q.rdc))
        ((DiagSet.dual Nat.bodd).obj (realize.obj P.rdc)) :=
  realize.map (RDCpx.isoOfIso (P := ((P.grayProduct Q).dual Nat.bodd).rdc)
        (Q := ((Q.dual Nat.bodd).grayProduct (P.dual Nat.bodd)).rdc)
        (MoleculeShape.grayProductDualIso P Q)).hom ≫
      (realizeShapeGrayIso.{u} (Q.dual Nat.bodd) (P.dual Nat.bodd)).hom ≫
        grayTensorBifunctor.map ((realizeShapeDualIso.{u} Nat.bodd Q).hom,
          (realizeShapeDualIso.{u} Nat.bodd P).hom)

private theorem swapRealize_app (P Q : MoleculeShape) {T : Atom}
    (c : atomToRDCpx.obj T ⟶ ((P.grayProduct Q).dual Nat.bodd).rdc) :
    (swapRealize.{u} P Q).app (op T) ⟨c⟩ =
      ((realizeGrayProductIso.{u} (Q.dual Nat.bodd).rdc (P.dual Nat.bodd).rdc).hom ≫
        grayTensorBifunctor.map ((realizeShapeDualIso.{u} Nat.bodd Q).hom,
          (realizeShapeDualIso.{u} Nat.bodd P).hom)).app (op T)
        ⟨c ≫ (RDCpx.isoOfIso (P := ((P.grayProduct Q).dual Nat.bodd).rdc)
          (Q := ((Q.dual Nat.bodd).grayProduct (P.dual Nat.bodd)).rdc)
          (MoleculeShape.grayProductDualIso P Q)).hom ≫
        (RDCpx.isoOfIso (P := ((Q.dual Nat.bodd).grayProduct (P.dual Nat.bodd)).rdc)
          (Q := grayProductRDC (Q.dual Nat.bodd).rdc (P.dual Nat.bodd).rdc)
          ((Q.dual Nat.bodd).grayProductIso (P.dual Nat.bodd)).symm).hom⟩ :=
  rfl

private theorem swapRealize_eq (P Q : MoleculeShape) :
    swapRealize.{u} P Q =
    (realizeShapeDualIso.{u} Nat.bodd (P.grayProduct Q)).hom ≫
      (DiagSet.dual Nat.bodd).map (realizeShapeGrayIso.{u} P Q).hom ≫
        (grayTensorDualIso _ _).hom := by
  rw [← Iso.inv_comp_eq, ← Functor.mapIso_hom (DiagSet.dual Nat.bodd), ← Iso.inv_comp_eq,
    Functor.mapIso_inv]
  refine dual_grayTensor_hom_ext Nat.bodd fun A B x y => ?_
  refine Eq.trans ?_ (grayTensorDualIso_hom_app_grayTensorCell x y).symm
  have e1 : ((DiagSet.dual Nat.bodd).map (realizeShapeGrayIso.{u} P Q).inv).app
      (op ((A.grayTensor B).dual Nat.bodd))
      ((grayTensor (realize.{u}.obj P.rdc) (realize.{u}.obj Q.rdc)).map
        (Atom.dualDualIso Nat.bodd (A.grayTensor B)).hom.op (grayTensorCell x y)) =
      (realize.{u}.obj (P.grayProduct Q).rdc).map
        (Atom.dualDualIso Nat.bodd (A.grayTensor B)).hom.op
        ⟨grayProductCellMap x.down y.down ≫ (RDCpx.isoOfIso (P := (P.grayProduct Q).rdc)
          (Q := grayProductRDC P.rdc Q.rdc) (P.grayProductIso Q).symm).inv⟩ := by
    refine (NatTrans.naturality_apply (realizeShapeGrayIso.{u} P Q).inv _ _).trans ?_
    have h := realizeGrayProductIso_inv_app_grayTensorCell.{u} x.down y.down
    change (realize.obj _).map _ ((realize.map _).app _
      ((realizeGrayProductIso.{u} P.rdc Q.rdc).inv.app _ (grayTensorCell x y))) = _
    exact congrArg (fun z => (realize.obj _).map _ ((realize.map _).app _ z)) h
  have e2 := (congrArg ((realizeShapeDualIso.{u} Nat.bodd (P.grayProduct Q)).inv.app _) e1).trans
    (realizeShapeDualIso_inv_app Nat.bodd _)
  refine (NatTrans.comp_app_apply _ _ _ _).trans ?_
  refine (NatTrans.comp_app_apply _ _ _ _).trans ?_
  refine (congrArg ((swapRealize.{u} P Q).app (op ((A.grayTensor B).dual Nat.bodd))) e2).trans ?_
  refine (swapRealize_app P Q _).trans ?_
  rw [dualCellMap_grayProductCellMap, realizeGrayProductIso_hom_comp_app]
  exact congrArg₂ (fun a b => (grayTensor _ _).map (Atom.grayTensorDualIso A B).hom.op
    (grayTensorCell a b)) (realizeShapeDualIso_hom_app_dualCellMap _ _)
    (realizeShapeDualIso_hom_app_dualCellMap _ _)

theorem PastingDiagram.equiv_dual_grayTensor (u : PastingDiagram X) (v : PastingDiagram Y) :
    (((u.grayTensor v).dual Nat.bodd).mapTo (grayTensorDualIso X Y).hom).Equiv
      ((v.dual Nat.bodd).grayTensor (u.dual Nat.bodd)) := by
  refine ⟨MoleculeShape.grayProductDualIso u.shape v.shape, ?_⟩
  have h := congrArg (· ≫ grayTensorBifunctor.map (X := (_, _))
    (Y := ((DiagSet.dual Nat.bodd).obj Y, (DiagSet.dual Nat.bodd).obj X))
    ((DiagSet.dual Nat.bodd).map v.map,
    (DiagSet.dual Nat.bodd).map u.map)) (swapRealize_eq.{u} u.shape v.shape)
  simp only [swapRealize, Category.assoc] at h
  rw [← grayTensorDualIso_hom_naturality, ← Functor.map_comp_assoc, ← Functor.map_comp,
    prod_comp] at h
  exact h

end Atoms.Diagrammatic
