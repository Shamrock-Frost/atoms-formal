import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan

universe w v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

abbrev smallSpan {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : AsSmall.{w} WalkingSpan ⥤ C :=
  AsSmall.down ⋙ span f g

end CategoryTheory.Limits
