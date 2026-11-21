import Atoms.Doctrine.Doctrine

open CategoryTheory Limits Opposite HomotopicalAlgebra

namespace Atoms.Doctrine

universe v u

variable {A : Type u} [Category.{v} A] {𝕀 : HomotopicalAlgebra.ExactCylinder.{v} (Aᵒᵖ ⥤ Type v)}
    (D : Atoms.Doctrine 𝕀)
  [D.strictAlgebras.ι.IsRightAdjoint]

noncomputable def freeMonad : Monad D.Psh :=
  (Adjunction.ofIsRightAdjoint D.strictAlgebras.ι).toMonad

noncomputable def freeShape (s : Shapes D.base) : D.StrictAlgebra :=
  D.strictAlgebras.ι.leftAdjoint.obj (yoneda.obj s)

abbrev ShapeCategory : Type (max u v) :=
  InducedCategory D.StrictAlgebra D.freeShape

end Atoms.Doctrine
