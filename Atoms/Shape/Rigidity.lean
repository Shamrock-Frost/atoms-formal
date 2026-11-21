import Atoms.Shape.Atom
import Atoms.Molecule.Rigidity

open CategoryTheory Atoms.Molecule Atoms.Molecule.OGP

namespace Atoms.Shape

variable {U V : Atom}

def Atom.isoOGP (e : U ≅ V) : U.ogp ≅ V.ogp where
  hom := ConcreteCategory.ofHom ⟨e.hom, Atom.isMorphism_of_isInclusionHom e.hom
    (Function.LeftInverse.injective (Iso.hom_inv_id_apply e))⟩
  inv := ConcreteCategory.ofHom ⟨e.inv, Atom.isMorphism_of_isInclusionHom e.inv
    (Function.LeftInverse.injective (Iso.inv_hom_id_apply e))⟩
  hom_inv_id := by ext x; exact Iso.hom_inv_id_apply e x
  inv_hom_id := by ext y; exact Iso.inv_hom_id_apply e y

@[simp] theorem Atom.isoOGP_apply (e : U ≅ V) (x : U.ogp) :
    (Atom.isoOGP e).hom x = e.hom x := rfl

def Atom.isoOfOGPIso (φ : U.ogp ≅ V.ogp) : U ≅ V where
  hom := Atom.ofInclusion φ.hom
  inv := Atom.ofInclusion φ.inv
  hom_inv_id := by ext x; exact ConcreteCategory.congr_hom φ.hom_inv_id x
  inv_hom_id := by ext y; exact ConcreteCategory.congr_hom φ.inv_hom_id y

@[simp] theorem Atom.isoOfOGPIso_hom_apply (φ : U.ogp ≅ V.ogp) (x : U.ogp) :
    (Atom.isoOfOGPIso φ).hom x = φ.hom x := rfl

@[simp] theorem Atom.isoOfOGPIso_inv_apply (φ : U.ogp ≅ V.ogp) (y : V.ogp) :
    (Atom.isoOfOGPIso φ).inv y = φ.inv y := rfl

theorem Atom.iso_eq (e₁ e₂ : U ≅ V) : e₁ = e₂ :=
  have h := (IsMolecule.subsingleton_iso U.isAtom.1).elim (Atom.isoOGP e₁) (Atom.isoOGP e₂)
  Iso.ext (Atom.hom_ext fun x => congrArg (fun φ : U.ogp ≅ V.ogp => φ.hom x) h)

end Atoms.Shape
