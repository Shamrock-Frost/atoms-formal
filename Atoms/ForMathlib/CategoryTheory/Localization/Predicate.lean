import Mathlib.CategoryTheory.Localization.Predicate

namespace CategoryTheory.Localization

variable {C D : Type*} [Category C] [Category D] (L : C ⥤ D) (W : MorphismProperty C)
  [L.IsLocalization W]

@[reassoc]
theorem map_comp_isoOfHom_inv {X Y X' Y' : C} (b : X ⟶ Y) (hb : W b) (b' : X' ⟶ Y')
    (hb' : W b') (x : Y ⟶ Y') (y : X ⟶ X') (h : b ≫ x = y ≫ b') :
    L.map x ≫ (isoOfHom L W b' hb').inv = (isoOfHom L W b hb).inv ≫ L.map y := by
  rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq, isoOfHom_hom, isoOfHom_hom,
    ← L.map_comp, ← L.map_comp, h]

end CategoryTheory.Localization
