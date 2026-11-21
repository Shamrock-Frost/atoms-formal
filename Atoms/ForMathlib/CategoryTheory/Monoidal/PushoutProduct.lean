import Atoms.ForMathlib.CategoryTheory.Limits.Shapes.EffectiveUnions
import Atoms.ForMathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.PushoutProduct

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

universe v u

namespace CategoryTheory.MonoidalCategory.Arrow

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [HasPushouts C]

theorem mono_pushoutProduct [HasEffectiveUnions C] {A B X Y : C}
    (f : A ⟶ B) (g : X ⟶ Y) [Mono f] [Mono g] : Mono (Arrow.mk f □ Arrow.mk g).hom := by
  have : Mono (B ◁ g) := ⟨fun a b h ↦ by
    ext
    · simpa using congrArg (· ≫ fst _ _) h
    · exact (cancel_mono g).1 (by simpa using congrArg (· ≫ snd _ _) h)⟩
  have : Mono (f ▷ Y) := ⟨fun a b h ↦ by
    ext
    · exact (cancel_mono f).1 (by simpa using congrArg (· ≫ fst _ _) h)
    · simpa using congrArg (· ≫ snd _ _) h⟩
  exact HasEffectiveUnions.mono_pushoutDesc
    (isPullback_whiskerRight_whiskerLeft f g)

end CategoryTheory.MonoidalCategory.Arrow
