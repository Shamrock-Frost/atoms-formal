import Mathlib.CategoryTheory.Presentable.Adjunction
import Mathlib.CategoryTheory.Presentable.Presheaf

universe w v v' u

namespace CategoryTheory.Presheaf

instance isLocallyPresentable {A : Type u} [Category.{v'} A] [IsLocallyPresentable.{max w v} A]
    [Limits.HasPullbacks A] {C : Type v} [SmallCategory C] :
    IsLocallyPresentable.{max w v} (Cᵒᵖ ⥤ A) :=
  ((AsSmall.equiv : C ≌ AsSmall.{max w v} C).op.congrLeft).symm.isLocallyPresentable

end CategoryTheory.Presheaf
