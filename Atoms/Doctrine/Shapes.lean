import Atoms.Homotopical.Cylinder.Induced

open CategoryTheory Limits Opposite HomotopicalAlgebra

namespace Atoms.Doctrine

universe v u

variable {A : Type u} [Category.{v} A]

abbrev Shapes (B : Aᵒᵖ ⥤ Type v) : Type (max u v) := (B.Elements)ᵒᵖ

def shapesProj (B : Aᵒᵖ ⥤ Type v) : Shapes B ⥤ A := (CategoryOfElements.π B).leftOp

def shapesPresheafEquivOver (B : Aᵒᵖ ⥤ Type v) : ((Shapes B)ᵒᵖ ⥤ Type v) ≌ Over B :=
  (Equivalence.congrLeft (CategoryOfElements.costructuredArrowYonedaEquivalence B).op).trans
    (overEquivPresheafCostructuredArrow B).symm

variable (𝕀 : HomotopicalAlgebra.ExactCylinder.{v} (Aᵒᵖ ⥤ Type v)) (B : Aᵒᵖ ⥤ Type v)

structure CylinderClosed where
  cylinder : HomotopicalAlgebra.ExactCylinder.{v} ((Shapes B)ᵒᵖ ⥤ Type v)
  iso : cylinder.I ⋙ (shapesPresheafEquivOver B).functor ≅
    (shapesPresheafEquivOver B).functor ⋙ 𝕀.overCylinderFunctor B
  endpoint_iso : ∀ (ε : Bool) (X : (Shapes B)ᵒᵖ ⥤ Type v),
    (shapesPresheafEquivOver B).functor.map ((cylinder.endpoint ε).app X) ≫ iso.hom.app X =
      (𝕀.overEndpoint B ε).app ((shapesPresheafEquivOver B).functor.obj X)

end Atoms.Doctrine
