import Mathlib.CategoryTheory.Presentable.IsCardinalFiltered

universe w v u u'

namespace CategoryTheory.IsCardinalFiltered

open Limits

variable {K : Type u} [Category.{v} K] {κ : Cardinal.{w}} [Fact κ.IsRegular]
  [IsCardinalFiltered K κ]

theorem exists_map_eq_of_isColimit {S : Type u'} (hS : HasCardinalLT S κ)
    {F : S → K ⥤ Type v} {c : ∀ s, Cocone (F s)} (hc : ∀ s, IsColimit (c s)) {j : K}
    (a b : ∀ s, (F s).obj j) (h : ∀ s, (c s).ι.app j (a s) = (c s).ι.app j (b s)) :
    ∃ (m : K) (t : j ⟶ m), ∀ s, (F s).map t (a s) = (F s).map t (b s) := by
  have := isFiltered_of_isCardinalFiltered K κ
  choose k t ht using fun s => (Types.FilteredColimit.isColimit_eq_iff' (hc s) _ _).1 (h s)
  obtain ⟨m, u, v, huv⟩ := wideSpan t hS
  refine ⟨m, v, fun s => ?_⟩
  rw [← huv s, Functor.map_comp, types_comp_apply, types_comp_apply, ht s]

end CategoryTheory.IsCardinalFiltered
