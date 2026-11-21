import Atoms.Molecule.Construction.GrayProductMolecule
import Atoms.Molecule.Construction.GrayProductMonoidal
import Atoms.Molecule.RegularComplex.Isomorphism
import Atoms.Molecule.RegularComplex.Morphism
import Mathlib.CategoryTheory.Monoidal.Widesubcategory

universe u

open CategoryTheory MonoidalCategory Set Topology

namespace Atoms.Molecule.OGP

namespace RDCpxDown

def grayProduct (P Q : RDCpxDown.{u}) : RDCpxDown.{u} :=
  ⟨OGP.grayProduct P.toOGP Q.toOGP, isRDC_grayProduct P.isRDC Q.isRDC⟩

def grayProductMap {P P' Q Q' : RDCpxDown.{u}} (f : P ⟶ P') (g : Q ⟶ Q') :
    grayProduct P Q ⟶ grayProduct P' Q' :=
  ConcreteCategory.ofHom (X := grayProduct P Q) (Y := grayProduct P' Q')
    ⟨fun p => (ConcreteCategory.hom f p.1, ConcreteCategory.hom g p.2),
      isMap_prodMap P.isRDC P'.isRDC Q.isRDC Q'.isRDC (ConcreteCategory.hom f).isMap
        (ConcreteCategory.hom g).isMap⟩

@[simp] theorem grayProductMap_apply {P P' Q Q' : RDCpxDown.{u}} (f : P ⟶ P') (g : Q ⟶ Q')
    (p : grayProduct P Q) :
    ConcreteCategory.hom (grayProductMap f g) p =
      (ConcreteCategory.hom f p.1, ConcreteCategory.hom g p.2) :=
  rfl

instance instMonoidalCategory : MonoidalCategory RDCpxDown.{u} :=
  letI : MonoidalCategoryStruct RDCpxDown.{u} :=
    { tensorObj := grayProduct
      whiskerLeft := fun P _ _ g => grayProductMap (𝟙 P) g
      whiskerRight := fun f Q => grayProductMap f (𝟙 Q)
      tensorHom := grayProductMap
      tensorUnit := ⟨point, isRDC_point⟩
      associator := fun P Q R => isoOfIso (grayProductAssoc P.toOGP Q.toOGP R.toOGP)
      leftUnitor := fun P => isoOfIso (P := grayProduct ⟨point, isRDC_point⟩ P)
        (grayProductLeftUnitor P.toOGP)
      rightUnitor := fun P => isoOfIso (P := grayProduct P ⟨point, isRDC_point⟩)
        (grayProductRightUnitor P.toOGP) }
  .ofTensorHom
    (id_tensorHom_id := fun _ _ => rfl)
    (id_tensorHom := fun _ _ _ _ => rfl)
    (tensorHom_id := fun _ _ => rfl)
    (tensorHom_comp_tensorHom := fun _ _ _ _ => rfl)
    (associator_naturality := fun _ _ _ => rfl)
    (leftUnitor_naturality := fun _ => rfl)
    (rightUnitor_naturality := fun _ => rfl)
    (pentagon := fun _ _ _ _ => rfl)
    (triangle := fun _ _ => rfl)

theorem tensorObj_toOGP (P Q : RDCpxDown.{u}) : (P ⊗ Q).toOGP = P.toOGP ⊗ Q.toOGP :=
  rfl

theorem tensorUnit_toOGP : (𝟙_ RDCpxDown.{u}).toOGP = 𝟙_ OGP.{u} :=
  rfl

@[simp] theorem tensorHom_apply {P P' Q Q' : RDCpxDown.{u}} (f : P ⟶ P') (g : Q ⟶ Q')
    (p : (P ⊗ Q : RDCpxDown.{u})) :
    ConcreteCategory.hom (f ⊗ₘ g) p = (ConcreteCategory.hom f p.1, ConcreteCategory.hom g p.2) :=
  rfl

@[simp] theorem whiskerLeft_apply (P : RDCpxDown.{u}) {Q Q' : RDCpxDown.{u}} (g : Q ⟶ Q')
    (p : (P ⊗ Q : RDCpxDown.{u})) :
    ConcreteCategory.hom (P ◁ g) p = (p.1, ConcreteCategory.hom g p.2) :=
  rfl

@[simp] theorem whiskerRight_apply {P P' : RDCpxDown.{u}} (f : P ⟶ P') (Q : RDCpxDown.{u})
    (p : (P ⊗ Q : RDCpxDown.{u})) :
    ConcreteCategory.hom (f ▷ Q) p = (ConcreteCategory.hom f p.1, p.2) :=
  rfl

@[simp] theorem associator_hom_apply (P Q R : RDCpxDown.{u})
    (p : ((P ⊗ Q) ⊗ R : RDCpxDown.{u})) :
    ConcreteCategory.hom (α_ P Q R).hom p = (p.1.1, (p.1.2, p.2)) :=
  rfl

@[simp] theorem leftUnitor_hom_apply (P : RDCpxDown.{u})
    (p : (𝟙_ RDCpxDown.{u} ⊗ P : RDCpxDown.{u})) : ConcreteCategory.hom (λ_ P).hom p = p.2 :=
  rfl

@[simp] theorem rightUnitor_hom_apply (P : RDCpxDown.{u})
    (p : (P ⊗ 𝟙_ RDCpxDown.{u} : RDCpxDown.{u})) : ConcreteCategory.hom (ρ_ P).hom p = p.1 :=
  rfl

@[simp] theorem associator_inv_apply (P Q R : RDCpxDown.{u})
    (p : (P ⊗ (Q ⊗ R) : RDCpxDown.{u})) :
    ConcreteCategory.hom (α_ P Q R).inv p = ((p.1, p.2.1), p.2.2) :=
  rfl

@[simp] theorem leftUnitor_inv_apply (P : RDCpxDown.{u}) (x : P) :
    ConcreteCategory.hom (λ_ P).inv x = ((⊤ : point.{u}), x) :=
  rfl

@[simp] theorem rightUnitor_inv_apply (P : RDCpxDown.{u}) (x : P) :
    ConcreteCategory.hom (ρ_ P).inv x = (x, (⊤ : point.{u})) :=
  rfl

end RDCpxDown

instance : localEmbeddings.{u}.IsMonoidalStable where
  toIsMonoidal := .mk' _ fun _ _ hf hg => IsLocalEmbedding.prodMap hf hg
  associator_hom_mem P Q R :=
    isLocalEmbedding_of_isInclusion (grayProductAssoc P.toOGP Q.toOGP R.toOGP).hom
  associator_inv_mem P Q R :=
    isLocalEmbedding_of_isInclusion (grayProductAssoc P.toOGP Q.toOGP R.toOGP).inv
  leftUnitor_hom_mem P := isLocalEmbedding_of_isInclusion (grayProductLeftUnitor P.toOGP).hom
  leftUnitor_inv_mem P := isLocalEmbedding_of_isInclusion (grayProductLeftUnitor P.toOGP).inv
  rightUnitor_hom_mem P := isLocalEmbedding_of_isInclusion (grayProductRightUnitor P.toOGP).hom
  rightUnitor_inv_mem P := isLocalEmbedding_of_isInclusion (grayProductRightUnitor P.toOGP).inv

instance : cartesian.{u}.IsMonoidalStable where
  toIsMonoidal := .mk' _ fun f g hf hg => by
    have : (ConcreteCategory.hom f).isMap.monotone.functor.IsFibered := hf
    have : (ConcreteCategory.hom g).isMap.monotone.functor.IsFibered := hg
    exact functor_isFibered_prodMap (ConcreteCategory.hom f).isMap.monotone
      (ConcreteCategory.hom g).isMap.monotone _
  associator_hom_mem P Q R :=
    localEmbeddings_le_cartesian _ (localEmbeddings.associator_hom_mem P Q R)
  associator_inv_mem P Q R :=
    localEmbeddings_le_cartesian _ (localEmbeddings.associator_inv_mem P Q R)
  leftUnitor_hom_mem P := localEmbeddings_le_cartesian _ (localEmbeddings.leftUnitor_hom_mem P)
  leftUnitor_inv_mem P := localEmbeddings_le_cartesian _ (localEmbeddings.leftUnitor_inv_mem P)
  rightUnitor_hom_mem P := localEmbeddings_le_cartesian _ (localEmbeddings.rightUnitor_hom_mem P)
  rightUnitor_inv_mem P := localEmbeddings_le_cartesian _ (localEmbeddings.rightUnitor_inv_mem P)

instance : MonoidalCategory RDCpxEq.{u} :=
  inferInstanceAs (MonoidalCategory (WideSubcategory localEmbeddings.{u}))

instance : RDCpxEq.toRDCpx.{u}.Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ => Iso.refl _
      μIso_hom_natural_left := fun _ _ => by ext; rfl
      μIso_hom_natural_right := fun _ _ => by ext; rfl
      associativity := fun _ _ _ => by ext; rfl
      left_unitality := fun _ => by ext; rfl
      right_unitality := fun _ => by ext; rfl }

end Atoms.Molecule.OGP
