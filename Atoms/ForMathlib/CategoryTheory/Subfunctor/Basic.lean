import Mathlib.CategoryTheory.Subfunctor.Basic
import Mathlib.CategoryTheory.Yoneda

universe w u

namespace CategoryTheory.Subfunctor

def isoOfEq {D : Type*} [Category D] {F : D ⥤ Type*} {G G' : Subfunctor F}
    (h : G = G') : G.toFunctor ≅ G'.toFunctor where
  hom := Subfunctor.homOfLe h.le
  inv := Subfunctor.homOfLe h.ge

variable {C : Type u} [Category.{w} C]

theorem mem_iff_exists_comp_ι {a b : C} (R : Subfunctor (yoneda.obj a))
    (f : b ⟶ a) :
    f ∈ R.obj (Opposite.op b) ↔ ∃ W : yoneda.obj b ⟶ R.toFunctor, W ≫ R.ι = yoneda.map f := by
  constructor
  · intro hf
    obtain ⟨e, he⟩ : ∃ e : R.toFunctor.obj (Opposite.op b), e.1 = f := ⟨⟨f, hf⟩, rfl⟩
    refine ⟨yonedaEquiv.symm e, yonedaEquiv.injective ?_⟩
    rw [yonedaEquiv_comp, Equiv.apply_symm_apply, yonedaEquiv_yoneda_map]
    exact he
  · rintro ⟨W, hW⟩
    have h := congrArg yonedaEquiv hW
    rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map] at h
    rw [← h]
    exact (yonedaEquiv W).2

end CategoryTheory.Subfunctor
