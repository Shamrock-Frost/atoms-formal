import Atoms.Doctrine.Shapes
import Atoms.Homotopical.EilenbergZilber.Basic

open CategoryTheory Limits Opposite Atoms.Doctrine HomotopicalAlgebra

universe v u

namespace Atoms

variable {A : Type u} [Category.{v} A]

structure Doctrine (𝕀 : HomotopicalAlgebra.ExactCylinder.{v} (Aᵒᵖ ⥤ Type v)) where
  base : Aᵒᵖ ⥤ Type v
  cylinderClosed : CylinderClosed 𝕀 base
  S : Set (Shapes base)
  manyToOne : Shapes base → Prop
  S_manyToOne : ∀ W ∈ S, manyToOne W
  inputBoundary : ∀ W : Shapes base, Subfunctor (yoneda.obj W)
  inputBoundary_le : ∀ W : Shapes base,
    inputBoundary W ≤ Homotopical.EZCategory.boundary W
  E : Set (Shapes base)
  thinnessMap : Shapes base → Arrow ((Shapes base)ᵒᵖ ⥤ Type v)

namespace Doctrine

variable {𝕀 : HomotopicalAlgebra.ExactCylinder.{v} (Aᵒᵖ ⥤ Type v)} (D : Doctrine 𝕀)

abbrev Psh := (Shapes D.base)ᵒᵖ ⥤ Type v

def localityGenerators : MorphismProperty D.Psh :=
  MorphismProperty.ofHoms fun W : D.S => (D.inputBoundary W.1).ι

def thinnessGenerators : MorphismProperty D.Psh :=
  MorphismProperty.ofHoms fun W : D.E => (D.thinnessMap W.1).hom

def generators : MorphismProperty D.Psh :=
  D.localityGenerators ⊔ D.thinnessGenerators

def weakAlgebras : ObjectProperty D.Psh := fun X =>
  D.cylinderClosed.cylinder.IsFibrant D.generators X

abbrev WeakAlgebra := D.weakAlgebras.FullSubcategory

def strictAlgebras : ObjectProperty D.Psh := fun X =>
  (∀ W ∈ D.S, Function.Bijective
      fun f : yoneda.obj W ⟶ X => (D.inputBoundary W).ι ≫ f) ∧
    ∀ W ∈ D.E, Function.Bijective
      fun f : (D.thinnessMap W).right ⟶ X => (D.thinnessMap W).hom ≫ f

abbrev StrictAlgebra := D.strictAlgebras.FullSubcategory

end Doctrine

end Atoms
