import Mathlib.CategoryTheory.Comma.Basic

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory.Comma

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  {B' : Type u₃} [Category.{v₃} B']

def mapRightToId (u : A ⥤ B) (v : B' ⥤ B) : Comma u v ⥤ Comma u (𝟭 B) where
  obj X := ⟨X.left, v.obj X.right, X.hom⟩
  map f := ⟨f.left, v.map f.right, f.w⟩

def idSection (u : A ⥤ B) : A ⥤ Comma u (𝟭 B) where
  obj a := ⟨a, u.obj a, 𝟙 _⟩
  map f := ⟨f, u.map f, by simp⟩

variable {A' : Type u₄} [Category.{v₄} A']

def ofSquare (w : A' ⥤ A) (u' : A' ⥤ B') (u : A ⥤ B) (v : B' ⥤ B) (h : w ⋙ u = u' ⋙ v) :
    A' ⥤ Comma u v where
  obj a := ⟨w.obj a, u'.obj a, eqToHom (Functor.congr_obj h a)⟩
  map f := ⟨w.map f, u'.map f, by
    have := Functor.congr_hom h f
    simp only [Functor.comp_map] at this
    simp [this]⟩

end CategoryTheory.Comma
