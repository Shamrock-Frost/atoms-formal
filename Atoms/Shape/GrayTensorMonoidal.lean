import Atoms.Molecule.Construction.GrayProductMonoidal
import Atoms.Shape.GrayTensor
import Atoms.Shape.Standard

open CategoryTheory MonoidalCategory Atoms.Molecule Atoms.Molecule.OGP

namespace Atoms.Shape.Atom

def grayTensorAssoc (U V W : Atom) :
    grayTensor (grayTensor U V) W ≅ grayTensor U (grayTensor V W) :=
  Atom.isoOfIso ((grayTensorIso (grayTensor U V) W).symm ≪≫
    whiskerRightIso (grayTensorIso U V).symm W.ogp ≪≫ grayProductAssoc U.ogp V.ogp W.ogp ≪≫
    whiskerLeftIso U.ogp (grayTensorIso V W) ≪≫ grayTensorIso U (grayTensor V W))

@[simp] theorem grayTensorAssoc_hom_apply (U V W : Atom) (z : (grayTensor (grayTensor U V) W).ogp) :
    (grayTensorAssoc U V W).hom z =
      (grayTensorIso U (grayTensor V W)).hom
        (((grayTensorIso U V).inv ((grayTensorIso (grayTensor U V) W).inv z).1).1,
          (grayTensorIso V W).hom
            (((grayTensorIso U V).inv ((grayTensorIso (grayTensor U V) W).inv z).1).2,
              ((grayTensorIso (grayTensor U V) W).inv z).2)) :=
  rfl

@[simp] theorem grayTensorAssoc_inv_apply (U V W : Atom) (z : (grayTensor U (grayTensor V W)).ogp) :
    (grayTensorAssoc U V W).inv z =
      (grayTensorIso (grayTensor U V) W).hom
        ((grayTensorIso U V).hom (((grayTensorIso U (grayTensor V W)).inv z).1,
            ((grayTensorIso V W).inv ((grayTensorIso U (grayTensor V W)).inv z).2).1),
          ((grayTensorIso V W).inv ((grayTensorIso U (grayTensor V W)).inv z).2).2) :=
  rfl

def grayTensorLeftUnitor (U : Atom) : grayTensor atomPoint U ≅ U :=
  Atom.isoOfIso ((grayTensorIso atomPoint U).symm ≪≫
    whiskerRightIso (FiniteOGP.ofOGPIso point).symm U.ogp ≪≫ grayProductLeftUnitor U.ogp)

@[simp] theorem grayTensorLeftUnitor_hom_apply (U : Atom) (z : (grayTensor atomPoint U).ogp) :
    (grayTensorLeftUnitor U).hom z = ((grayTensorIso atomPoint U).inv z).2 :=
  rfl

@[simp] theorem grayTensorLeftUnitor_inv_apply (U : Atom) (x : U.ogp) :
    (grayTensorLeftUnitor U).inv x =
      (grayTensorIso atomPoint U).hom ((FiniteOGP.ofOGPIso point).hom ⊤, x) :=
  rfl

def grayTensorRightUnitor (U : Atom) : grayTensor U atomPoint ≅ U :=
  Atom.isoOfIso ((grayTensorIso U atomPoint).symm ≪≫
    whiskerLeftIso U.ogp (FiniteOGP.ofOGPIso point).symm ≪≫ grayProductRightUnitor U.ogp)

@[simp] theorem grayTensorRightUnitor_hom_apply (U : Atom) (z : (grayTensor U atomPoint).ogp) :
    (grayTensorRightUnitor U).hom z = ((grayTensorIso U atomPoint).inv z).1 :=
  rfl

@[simp] theorem grayTensorRightUnitor_inv_apply (U : Atom) (x : U.ogp) :
    (grayTensorRightUnitor U).inv x =
      (grayTensorIso U atomPoint).hom (x, (FiniteOGP.ofOGPIso point).hom ⊤) :=
  rfl

@[reassoc] theorem grayTensorAssoc_naturality {U V W U' V' W' : Atom}
    (f : U ⟶ U') (g : V ⟶ V') (h : W ⟶ W') :
    grayTensorMap (grayTensorMap f g) h ≫ (grayTensorAssoc U' V' W').hom =
      (grayTensorAssoc U V W).hom ≫ grayTensorMap f (grayTensorMap g h) := by
  ext z
  simp only [ConcreteCategory.comp_apply, grayTensorMap_apply, grayTensorAssoc_hom_apply,
    Iso.hom_inv_id_apply]

@[reassoc] theorem grayTensorLeftUnitor_naturality {U U' : Atom} (f : U ⟶ U') :
    grayTensorMap (𝟙 atomPoint) f ≫ (grayTensorLeftUnitor U').hom =
      (grayTensorLeftUnitor U).hom ≫ f := by
  ext z
  simp only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply,
    grayTensorMap_apply, grayTensorLeftUnitor_hom_apply,
    Iso.hom_inv_id_apply]

@[reassoc] theorem grayTensorRightUnitor_naturality {U U' : Atom} (f : U ⟶ U') :
    grayTensorMap f (𝟙 atomPoint) ≫ (grayTensorRightUnitor U').hom =
      (grayTensorRightUnitor U).hom ≫ f := by
  ext z
  simp only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply,
    grayTensorMap_apply, grayTensorRightUnitor_hom_apply,
    Iso.hom_inv_id_apply]

theorem grayTensor_pentagon (U V W T : Atom) :
    grayTensorMap (grayTensorAssoc U V W).hom (𝟙 T) ≫ (grayTensorAssoc U (grayTensor V W) T).hom ≫
        grayTensorMap (𝟙 U) (grayTensorAssoc V W T).hom =
      (grayTensorAssoc (grayTensor U V) W T).hom ≫ (grayTensorAssoc U V (grayTensor W T)).hom := by
  ext z
  simp only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply,
    grayTensorMap_apply, grayTensorAssoc_hom_apply,
    Iso.hom_inv_id_apply]

theorem grayTensor_triangle (U V : Atom) :
    (grayTensorAssoc U atomPoint V).hom ≫ grayTensorMap (𝟙 U) (grayTensorLeftUnitor V).hom =
      grayTensorMap (grayTensorRightUnitor U).hom (𝟙 V) := by
  ext z
  simp only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply,
    grayTensorMap_apply, grayTensorAssoc_hom_apply,
    grayTensorLeftUnitor_hom_apply, grayTensorRightUnitor_hom_apply, Iso.hom_inv_id_apply]

instance instMonoidalCategory : MonoidalCategory Atom :=
  letI : MonoidalCategoryStruct Atom :=
    { tensorObj := grayTensor
      whiskerLeft := fun U _ _ g => grayTensorMap (𝟙 U) g
      whiskerRight := fun f V => grayTensorMap f (𝟙 V)
      tensorHom := grayTensorMap
      tensorUnit := atomPoint
      associator := grayTensorAssoc
      leftUnitor := grayTensorLeftUnitor
      rightUnitor := grayTensorRightUnitor }
  .ofTensorHom
    (id_tensorHom_id := grayTensorMap_id)
    (id_tensorHom := fun _ _ _ _ => rfl)
    (tensorHom_id := fun _ _ => rfl)
    (tensorHom_comp_tensorHom := grayTensorMap_comp)
    (associator_naturality := grayTensorAssoc_naturality)
    (leftUnitor_naturality := grayTensorLeftUnitor_naturality)
    (rightUnitor_naturality := grayTensorRightUnitor_naturality)
    (pentagon := grayTensor_pentagon)
    (triangle := grayTensor_triangle)

theorem grayTensorMap_toAtomPoint_rightUnitor_apply (U V : Atom)
    (z : (grayTensor U V).ogp) :
    (grayTensorRightUnitor U).hom (grayTensorMap (𝟙 U) (toAtomPoint V) z) =
      ((grayTensorIso U V).inv z).1 := by
  simp only [grayTensorMap_apply, grayTensorRightUnitor_hom_apply, Iso.hom_inv_id_apply]
  rfl

theorem grayTensorMap_toAtomPoint_leftUnitor_apply (U V : Atom)
    (z : (grayTensor U V).ogp) :
    (grayTensorLeftUnitor V).hom (grayTensorMap (toAtomPoint U) (𝟙 V) z) =
      ((grayTensorIso U V).inv z).2 := by
  simp only [grayTensorMap_apply, grayTensorLeftUnitor_hom_apply, Iso.hom_inv_id_apply]
  rfl

def grayTensorFst (U V : Atom) : grayTensor U V ⟶ U :=
  grayTensorMap (𝟙 U) (toAtomPoint V) ≫ (grayTensorRightUnitor U).hom

theorem grayTensorFst_apply (U V : Atom) (z : (grayTensor U V).ogp) :
    grayTensorFst U V z = ((grayTensorIso U V).inv z).1 :=
  grayTensorMap_toAtomPoint_rightUnitor_apply U V z

def grayTensorSnd (U V : Atom) : grayTensor U V ⟶ V :=
  grayTensorMap (toAtomPoint U) (𝟙 V) ≫ (grayTensorLeftUnitor V).hom

theorem grayTensorSnd_apply (U V : Atom) (z : (grayTensor U V).ogp) :
    grayTensorSnd U V z = ((grayTensorIso U V).inv z).2 :=
  grayTensorMap_toAtomPoint_leftUnitor_apply U V z

@[reassoc] theorem grayTensorMap_comp_grayTensorFst {U V U' V' : Atom} (f : U ⟶ U') (g : V ⟶ V') :
    grayTensorMap f g ≫ grayTensorFst U' V' = grayTensorFst U V ≫ f := by
  ext z
  simp only [ConcreteCategory.comp_apply, grayTensorFst_apply, grayTensorMap_apply,
    Iso.hom_inv_id_apply]

@[reassoc] theorem grayTensorMap_comp_grayTensorSnd {U V U' V' : Atom} (f : U ⟶ U') (g : V ⟶ V') :
    grayTensorMap f g ≫ grayTensorSnd U' V' = grayTensorSnd U V ≫ g := by
  ext z
  simp only [ConcreteCategory.comp_apply, grayTensorSnd_apply, grayTensorMap_apply,
    Iso.hom_inv_id_apply]

theorem grayTensor.hom_ext {T U V : Atom} {h h' : T ⟶ grayTensor U V}
    (hfst : h ≫ grayTensorMap (𝟙 U) (toAtomPoint V) ≫ (grayTensorRightUnitor U).hom =
      h' ≫ grayTensorMap (𝟙 U) (toAtomPoint V) ≫ (grayTensorRightUnitor U).hom)
    (hsnd : h ≫ grayTensorMap (toAtomPoint U) (𝟙 V) ≫ (grayTensorLeftUnitor V).hom =
      h' ≫ grayTensorMap (toAtomPoint U) (𝟙 V) ≫ (grayTensorLeftUnitor V).hom) :
    h = h' := by
  ext z
  have e1 := ConcreteCategory.congr_hom hfst z
  have e2 := ConcreteCategory.congr_hom hsnd z
  simp only [ConcreteCategory.comp_apply, grayTensorMap_toAtomPoint_rightUnitor_apply,
    grayTensorMap_toAtomPoint_leftUnitor_apply] at e1 e2
  rw [← Iso.inv_hom_id_apply (grayTensorIso U V) (h z), Prod.ext e1 e2, Iso.inv_hom_id_apply]

end Atoms.Shape.Atom
