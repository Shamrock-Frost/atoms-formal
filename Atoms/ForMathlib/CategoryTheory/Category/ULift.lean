import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.Limits.Shapes.Equivalence

universe w v u

namespace CategoryTheory.AsSmall

open Limits

variable {C : Type u} [Category.{v} C]

instance isEquivalence_up : (up : C ⥤ AsSmall.{w} C).IsEquivalence :=
  equiv.isEquivalence_functor

instance isEquivalence_down : (down : AsSmall.{w} C ⥤ C).IsEquivalence :=
  equiv.isEquivalence_inverse

instance hasTerminal [HasTerminal C] : HasTerminal (AsSmall.{w} C) :=
  hasTerminal_of_equivalence down

end CategoryTheory.AsSmall
