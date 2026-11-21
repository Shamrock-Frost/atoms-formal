import Mathlib.CategoryTheory.LiftingProperties.Basic
import Mathlib.CategoryTheory.Types.Basic

namespace CategoryTheory.Types

universe u

theorem hasLiftingProperty_of_injective_of_surjective {X Y S T : Type u} {i : X ⟶ Y}
    {p : S ⟶ T} (hi : Function.Injective i) (hp : Function.Surjective p) :
    HasLiftingProperty i p := by
  classical
  refine ⟨fun {f g} sq => ⟨⟨{ l := ↾fun y => if h : ∃ x, i x = y then f h.choose
      else (hp (g y)).choose, fac_left := ?_, fac_right := ?_ }⟩⟩⟩
  · ext x
    have h : ∃ x', i x' = i x := ⟨x, rfl⟩
    change (if h : ∃ x', i x' = i x then f h.choose else (hp (g (i x))).choose) = f x
    rw [dif_pos h]
    exact congrArg f (hi h.choose_spec)
  · ext y
    change p (if h : ∃ x, i x = y then f h.choose else (hp (g y)).choose) = g y
    split_ifs with h
    · have e := ConcreteCategory.congr_hom sq.w h.choose
      change p (f h.choose) = g (i h.choose) at e
      rw [e, h.choose_spec]
    · exact (hp (g y)).choose_spec

end CategoryTheory.Types
