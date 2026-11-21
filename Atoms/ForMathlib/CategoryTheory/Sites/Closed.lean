import Mathlib.CategoryTheory.Sites.Closed

universe v u

namespace CategoryTheory.NatTrans

open Opposite

variable {C : Type u} [Category.{v} C]

theorem app_map_eq_top_of_app_eq_top {K : Cᵒᵖ ⥤ Type max v u} (φ : K ⟶ Functor.sieves C)
    {a a' : Cᵒᵖ} (f : a ⟶ a') {k : K.obj a} (hk : @Eq (Sieve a.unop) (φ.app a k) ⊤) :
    @Eq (Sieve a'.unop) (φ.app a' (K.map f k)) ⊤ := by
  rw [NatTrans.naturality_apply]
  exact (congrArg (Sieve.pullback f.unop) hk).trans Sieve.pullback_top

end CategoryTheory.NatTrans
