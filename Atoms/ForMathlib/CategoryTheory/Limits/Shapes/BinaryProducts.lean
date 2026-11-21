import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

namespace CategoryTheory.Limits

theorem coprodComparison_map_desc_comp {C D : Type*} [Category* C] [Category* D]
    [HasBinaryCoproducts C] [HasBinaryCoproducts D] (L : C ⥤ D) {Y Z : C} {W : D}
    (a b : Y ⟶ Z) (ψ : L.obj Z ⟶ W) (a' b' : L.obj Y ⟶ W) (ha : L.map a ≫ ψ = a')
    (hb : L.map b ≫ ψ = b') :
    coprodComparison L Y Y ≫ L.map (coprod.desc a b) ≫ ψ = coprod.desc a' b' := by
  refine coprod.hom_ext ?_ ?_
  · rw [coprodComparison_inl_assoc, ← Functor.map_comp_assoc, coprod.inl_desc, ha,
      coprod.inl_desc]
  · rw [coprodComparison_inr_assoc, ← Functor.map_comp_assoc, coprod.inr_desc, hb,
      coprod.inr_desc]

end CategoryTheory.Limits
