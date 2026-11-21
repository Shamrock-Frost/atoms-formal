import Atoms.Homotopical.Simplicial.Diagonal
import Atoms.Homotopical.Simplicial.SubdivisionQuillen

open CategoryTheory Limits MonoidalCategory MorphismProperty Simplicial

universe u

namespace Atoms.Homotopical

private theorem kanWeak_prod_map_id {X Y : SSet.{u}} {f : X ⟶ Y} (hf : kanWeak f)
    (K : SSet.{u}) : kanWeak (prod.map f (𝟙 K)) := by
  let e (Z : SSet.{u}) : Z ⨯ K ≅ Z ⊗ K :=
    { hom := CartesianMonoidalCategory.lift prod.fst prod.snd
      inv := prod.lift (CartesianMonoidalCategory.fst _ _) (CartesianMonoidalCategory.snd _ _)
      inv_hom_id := CartesianMonoidalCategory.hom_ext _ _
        (by simp only [Category.assoc, CartesianMonoidalCategory.lift_fst, Category.id_comp]
            exact prod.lift_fst _ _)
        (by simp only [Category.assoc, CartesianMonoidalCategory.lift_snd, Category.id_comp]
            exact prod.lift_snd _ _) }
  refine (kanWeak.arrow_mk_iso_iff (Arrow.isoMk (e X) (e Y) ?_)).2 (kanWeak_whiskerRight hf K)
  dsimp [e]
  ext : 1 <;> simp

theorem kanWeak_prod_map {X Y X' Y' : SSet.{u}} {f : X ⟶ Y} {g : X' ⟶ Y'} (hf : kanWeak f)
    (hg : kanWeak g) : kanWeak (Limits.prod.map f g) := by
  have h : kanWeak (prod.map (𝟙 Y) g) :=
    (kanWeak.arrow_mk_iso_iff (Arrow.isoMk (prod.braiding _ _) (prod.braiding _ _) (by
      ext; simp))).2 (kanWeak_prod_map_id hg Y)
  rw [← Category.comp_id f, ← Category.id_comp g, ← prod.map_map]
  exact kanWeak.comp_mem _ _ (kanWeak_prod_map_id hf X') h

theorem kanWeak_prodComparison_sd (K L : SSet.{u}) : kanWeak (prodComparison SSet.sd K L) := by
  have e : prodComparison SSet.sd K L ≫ prod.map (lastVertex.app K) (lastVertex.app L) =
      lastVertex.app (K ⨯ L) := by
    ext <;> simp [lastVertex.naturality]
  exact kanWeak.of_postcomp _ _ (kanWeak_prod_map (kanWeak_lastVertex_app K)
    (kanWeak_lastVertex_app L)) (e ▸ kanWeak_lastVertex_app _)

end Atoms.Homotopical
