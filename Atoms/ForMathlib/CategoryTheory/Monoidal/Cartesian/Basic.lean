import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace CategoryTheory.CartesianMonoidalCategory

variable {C : Type*} [Category* C] [CartesianMonoidalCategory C]

def tensorTerminalEquiv {S A T Y : C} (hT : IsTerminal T) (a : A ⟶ S) (y : Y ⟶ S) :
    {f : A ⊗ T ⟶ Y // f ≫ y = fst _ _ ≫ a} ≃ {g : A ⟶ Y // g ≫ y = a} where
  toFun f := ⟨lift (𝟙 A) (hT.from A) ≫ f.1, by rw [Category.assoc, f.2, lift_fst_assoc,
    Category.id_comp]⟩
  invFun g := ⟨fst A T ≫ g.1, by rw [Category.assoc, g.2]⟩
  left_inv f := by
    have h : fst A T ≫ lift (𝟙 A) (hT.from A) = 𝟙 _ :=
      CartesianMonoidalCategory.hom_ext _ _ (by simp) (hT.hom_ext _ _)
    exact Subtype.ext ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ f.1) h).trans
      (Category.id_comp _)))
  right_inv g := Subtype.ext ((lift_fst_assoc _ _ _).trans (Category.id_comp _))

instance mono_whiskerLeft (X : C) {Y Z : C} (f : Y ⟶ Z) [Mono f] : Mono (X ◁ f) :=
  ⟨fun g h e ↦ hom_ext _ _ (by simpa using e =≫ fst X Z)
    ((cancel_mono f).1 (by simpa using e =≫ snd X Z))⟩

instance (X : C) : (tensorLeft X).PreservesMonomorphisms :=
  ⟨fun f _ ↦ mono_whiskerLeft X f⟩

instance mono_whiskerRight {Y Z : C} (f : Y ⟶ Z) [Mono f] (X : C) : Mono (f ▷ X) :=
  ⟨fun g h e ↦ hom_ext _ _ ((cancel_mono f).1 (by simpa using e =≫ fst Z X))
    (by simpa using e =≫ snd Z X)⟩

instance (X : C) : (tensorRight X).PreservesMonomorphisms :=
  ⟨fun f _ ↦ mono_whiskerRight f X⟩

instance mono_tensorHom {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') [Mono f] [Mono g] :
    Mono (f ⊗ₘ g) := by
  rw [tensorHom_def]
  infer_instance

open Limits in
theorem isPullback_whiskerRight_whiskerLeft {A B X Y : C} (f : A ⟶ B)
    (g : X ⟶ Y) : IsPullback (f ▷ X) (A ◁ g) (B ◁ g) (f ▷ Y) := by
  refine ⟨⟨(whisker_exchange f g).symm⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s ↦ lift (s.snd ≫ fst A Y) (s.fst ≫ snd B X)) (fun s ↦ ?_) (fun s ↦ ?_)
    (fun s m h₁ h₂ ↦ ?_)⟩⟩
  · have h := congrArg (· ≫ fst B Y) s.condition
    simp only [Category.assoc, whiskerLeft_fst, whiskerRight_fst] at h
    ext <;> simp [h]
  · have h := congrArg (· ≫ snd B Y) s.condition
    simp only [Category.assoc, whiskerLeft_snd, whiskerRight_snd] at h
    ext <;> simp [h]
  · have h₁' := congrArg (· ≫ snd B X) h₁
    have h₂' := congrArg (· ≫ fst A Y) h₂
    simp only [Category.assoc, whiskerRight_snd, whiskerLeft_fst] at h₁' h₂'
    ext
    · simpa using h₂'
    · simpa using h₁'

end CategoryTheory.CartesianMonoidalCategory
