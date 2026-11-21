import Mathlib.CategoryTheory.LiftingProperties.Over

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {S : C}

namespace CommSq

lemma under_right {X₁ X₂ X₃ X₄ : Under S}
    {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄} (sq : CommSq t l r b) :
    CommSq t.right l.right r.right b.right :=
  ⟨by rw [← Under.comp_right, sq.w, Under.comp_right]⟩

end CommSq

namespace CommSq.HasLift

lemma under {X₁ X₂ X₃ X₄ : Under S}
    {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄} {sq : CommSq t l r b}
    [h : sq.under_right.HasLift] : sq.HasLift := by
  obtain ⟨⟨L⟩⟩ := h
  exact ⟨⟨{
    l := Under.homMk L.l (by rw [← Under.w l, Category.assoc, L.fac_left, Under.w t])
    fac_left := by ext; exact L.fac_left
    fac_right := by ext; exact L.fac_right
  }⟩⟩

end CommSq.HasLift

namespace HasLiftingProperty

lemma under {A B X Y : Under S} (i : A ⟶ B) (p : X ⟶ Y)
    [HasLiftingProperty i.right p.right] : HasLiftingProperty i p :=
  ⟨fun _ ↦ .under⟩

end HasLiftingProperty

end CategoryTheory
