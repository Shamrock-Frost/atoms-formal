import Mathlib.CategoryTheory.Adjunction.Basic

universe v u

namespace CategoryTheory.Equivalence

variable {B B' : Type u} [Category.{v} B] [Category.{v} B']

def congrLeftOpYonedaIso (e : B ≌ B') :
    yoneda ⋙ e.op.congrLeft.functor ≅ e.functor ⋙ yoneda :=
  (e.symm.toAdjunction.compYonedaIso).symm

end CategoryTheory.Equivalence
