import Atoms.Molecule.MoleculeShape.Dual
import Atoms.Shape.Atom

open CategoryTheory Atoms.Molecule Atoms.Molecule.OGP

namespace Atoms.Shape.Atom

@[implicit_reducible] def dual (U : Atom) (J : ℕ → Bool) : Atom :=
  ofIsAtom (U.toMoleculeShape.dual J).toFiniteOGP
    ((isAtom_iff_of_iso (U.toMoleculeShape.dualIso J)).1 ((isAtomIn_dual J).2 U.isAtom))

variable (J : ℕ → Bool)

def dualMap {U V : Atom} (f : U ⟶ V) : U.dual J ⟶ V.dual J :=
  conjHom (U.toMoleculeShape.dualIso J) (V.toMoleculeShape.dualIso J) f ((isMap f).dual J)

@[simp] theorem dualMap_apply {U V : Atom} (f : U ⟶ V) (x : (U.dual J).ogp) :
    dualMap J f x = (V.toMoleculeShape.dualIso J).hom (f ((U.toMoleculeShape.dualIso J).inv x)) :=
  rfl

@[simps obj]
def dualFunctor : Atom ⥤ Atom where
  obj U := U.dual J
  map := dualMap J
  map_id U := conjHom_id _
  map_comp f g := hom_ext fun x => by
    rw [ConcreteCategory.comp_apply, dualMap_apply, dualMap_apply, dualMap_apply,
      ConcreteCategory.comp_apply, Iso.hom_inv_id_apply]

@[simp] theorem dualFunctor_map {U V : Atom} (f : U ⟶ V) : (dualFunctor J).map f = dualMap J f :=
  rfl

def dualDualIso (U : Atom) : (U.dual J).dual J ≅ U :=
  isoOfIso (U.toMoleculeShape.dualDualIso J)

@[simp] theorem dualDualIso_hom_apply (U : Atom) (x : ((U.dual J).dual J).ogp) :
    (dualDualIso J U).hom x =
      (U.toMoleculeShape.dualIso J).inv (((U.dual J).toMoleculeShape.dualIso J).inv x) :=
  rfl

@[simp] theorem dualDualIso_inv_apply (U : Atom) (x : U.ogp) :
    (dualDualIso J U).inv x =
      ((U.dual J).toMoleculeShape.dualIso J).hom ((U.toMoleculeShape.dualIso J).hom x) :=
  rfl

@[simps!]
def dualFunctorCompIso : dualFunctor J ⋙ dualFunctor J ≅ 𝟭 Atom :=
  NatIso.ofComponents (dualDualIso J) fun {U V} f => hom_ext fun (x : ((U.dual J).dual J).ogp) => by
    change (dualDualIso J V).hom (dualMap J (dualMap J f) x) = f ((dualDualIso J U).hom x)
    rw [dualMap_apply, dualMap_apply, dualDualIso_hom_apply, dualDualIso_hom_apply,
      Iso.hom_inv_id_apply, Iso.hom_inv_id_apply]

theorem dualFunctor_map_dualDualIso_hom (U : Atom) :
    (dualFunctor J).map (dualDualIso J U).hom = (dualDualIso J (U.dual J)).hom :=
  hom_ext fun (x : (((U.dual J).dual J).dual J).ogp) => by
    change dualMap J (dualDualIso J U).hom x = (dualDualIso J (U.dual J)).hom x
    rw [dualMap_apply, dualDualIso_hom_apply, dualDualIso_hom_apply, Iso.inv_hom_id_apply]

@[simps]
def dualEquivalence : Atom ≌ Atom where
  functor := dualFunctor J
  inverse := dualFunctor J
  unitIso := (dualFunctorCompIso J).symm
  counitIso := dualFunctorCompIso J
  functor_unitIso_comp U := by
    change (dualFunctor J).map (dualDualIso J U).inv ≫ (dualDualIso J (U.dual J)).hom = 𝟙 _
    rw [← dualFunctor_map_dualDualIso_hom]
    exact ((dualFunctor J).mapIso (dualDualIso J U)).inv_hom_id

end Atoms.Shape.Atom
