import Mathlib.CategoryTheory.Subfunctor.Image

universe w w' v v' u u'

namespace CategoryTheory.Subfunctor

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (F : (Cᵒᵖ ⥤ Type w) ⥤ (Dᵒᵖ ⥤ Type w')) {X : Cᵒᵖ ⥤ Type w}

@[reassoc]
theorem inv_toRange_comp {Y : Cᵒᵖ ⥤ Type w} (p : X ⟶ Y) [Mono p] :
    inv (Subfunctor.toRange p) ≫ p = (Subfunctor.range p).ι := by
  rw [IsIso.inv_comp_eq, Subfunctor.toRange_ι]

theorem range_map_ι_le_of_le {S T : Subfunctor X} (h : S ≤ T) :
    Subfunctor.range (F.map S.ι) ≤ Subfunctor.range (F.map T.ι) := by
  rw [← Subfunctor.homOfLe_ι h, F.map_comp]
  exact Subfunctor.range_comp_le _ _

noncomputable def arrowIsoOfRangeEq {Y : Cᵒᵖ ⥤ Type w} (m : X ⟶ Y) [Mono m] (G : Subfunctor Y)
    (h : Subfunctor.range m = G) : Arrow.mk m ≅ Arrow.mk G.ι := by
  subst h
  exact Arrow.isoMk (asIso (Subfunctor.toRange m)) (Iso.refl _) (by simp)

theorem nonempty_arrow_iso_of_range_comp_eq {Y Y' : Cᵒᵖ ⥤ Type w} (m : X ⟶ Y) [Mono m]
    (e : Y ≅ Y') (G : Subfunctor Y') (h : Subfunctor.range (m ≫ e.hom) = G) :
    Nonempty (Arrow.mk m ≅ Arrow.mk G.ι) :=
  ⟨Arrow.isoMk (g := Arrow.mk (m ≫ e.hom)) (Iso.refl _) e (by simp) ≪≫
    arrowIsoOfRangeEq _ G h⟩

theorem exists_comp_eq_of_range_le {Y Z : Cᵒᵖ ⥤ Type w} (m : X ⟶ Y) [Mono m] (f : Z ⟶ Y)
    (h : Subfunctor.range f ≤ Subfunctor.range m) : ∃ g : Z ⟶ X, g ≫ m = f := by
  exact ⟨Subfunctor.lift f h ≫ inv (Subfunctor.toRange m), by
    rw [Category.assoc, Subfunctor.inv_toRange_comp, Subfunctor.lift_ι]⟩

end CategoryTheory.Subfunctor
