import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Quillen
import Mathlib.AlgebraicTopology.ModelCategory.FundamentalLemma

open CategoryTheory

namespace HomotopicalAlgebra

variable {C : Type*} [Category* C] [ModelCategory C] {H : Type*} [Category* H]
  (L : C ⥤ H) [L.IsLocalization (weakEquivalences C)]

private lemma weakEquivalence_of_isIso_map_of_bifibrant {X Y : C} [IsCofibrant X] [IsFibrant X]
    [IsCofibrant Y] [IsFibrant Y] (f : X ⟶ Y) [IsIso (L.map f)] : WeakEquivalence f := by
  obtain ⟨g, hg⟩ := map_surjective_of_isLocalization L Y X (inv (L.map f))
  refine weakEquivalence_of_rightHomotopyRel f g ?_ ?_
  · rw [RightHomotopyRel.iff_map_eq L, L.map_comp, hg, IsIso.hom_inv_id, L.map_id]
  · rw [RightHomotopyRel.iff_map_eq L, L.map_comp, hg, IsIso.inv_hom_id, L.map_id]

theorem weakEquivalence_iff_isIso_map {X Y : C} (f : X ⟶ Y) :
    WeakEquivalence f ↔ IsIso (L.map f) := by
  have hL {A B : C} (g : A ⟶ B) [WeakEquivalence g] : IsIso (L.map g) :=
    Localization.inverts L (weakEquivalences C) g ((weakEquivalence_iff g).1 inferInstance)
  refine ⟨fun _ ↦ hL f, fun _ ↦ ?_⟩
  let f₁ := CofibrantObject.HoCat.resolutionMap f
  let f₂ := FibrantObject.HoCat.resolutionMap f₁
  rw [← CofibrantObject.HoCat.weakEquivalence_resolutionMap_iff,
    ← FibrantObject.HoCat.weakEquivalence_resolutionMap_iff]
  have := hL (CofibrantObject.HoCat.pResolutionObj X)
  have := hL (CofibrantObject.HoCat.pResolutionObj Y)
  have h₁ : IsIso (L.map f₁) := by
    have e : L.map f₁ = (L.map (CofibrantObject.HoCat.pResolutionObj X) ≫ L.map f) ≫
        inv (L.map (CofibrantObject.HoCat.pResolutionObj Y)) := by
      rw [IsIso.eq_comp_inv, ← L.map_comp, ← L.map_comp,
        CofibrantObject.HoCat.resolutionMap_fac]
    rw [e]
    infer_instance
  have := hL (FibrantObject.HoCat.iResolutionObj (CofibrantObject.HoCat.resolutionObj X))
  have := hL (FibrantObject.HoCat.iResolutionObj (CofibrantObject.HoCat.resolutionObj Y))
  have h₂ : IsIso (L.map f₂) := by
    have e : L.map f₂ = inv (L.map (FibrantObject.HoCat.iResolutionObj
        (CofibrantObject.HoCat.resolutionObj X))) ≫ L.map f₁ ≫
          L.map (FibrantObject.HoCat.iResolutionObj (CofibrantObject.HoCat.resolutionObj Y)) := by
      rw [IsIso.eq_inv_comp, ← L.map_comp, ← L.map_comp,
        FibrantObject.HoCat.resolutionMap_fac]
    rw [e]
    infer_instance
  exact weakEquivalence_of_isIso_map_of_bifibrant L f₂

end HomotopicalAlgebra
