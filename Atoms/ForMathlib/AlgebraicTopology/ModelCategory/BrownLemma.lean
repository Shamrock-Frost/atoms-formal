import Mathlib.AlgebraicTopology.ModelCategory.BrownLemma

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [ModelCategory C] (F : C ⥤ D)
  (W : MorphismProperty D) [W.HasTwoOutOfThreeProperty] [W.ContainsIdentities]

theorem map_mem_of_cofibrant
    (hF : ∀ ⦃A B : C⦄ (i : A ⟶ B), IsCofibrant A → IsCofibrant B → Cofibration i →
      WeakEquivalence i → W (F.map i))
    {A B : C} [IsCofibrant A] [IsCofibrant B] (f : A ⟶ B) [WeakEquivalence f] : W (F.map f) := by
  obtain ⟨b⟩ := (inferInstance : Nonempty (CofibrantBrownFactorization f))
  have : IsCofibrant b.Z := isCofibrant_of_cofibration b.s
  have hs := hF b.s inferInstance inferInstance inferInstance inferInstance
  have hp : W (F.map b.p) :=
    W.of_precomp _ _ hs (by rw [← F.map_comp, b.s_p, F.map_id]; exact W.id_mem _)
  rw [← b.fac, F.map_comp]
  exact W.comp_mem _ _ (hF b.i inferInstance inferInstance inferInstance inferInstance) hp

theorem map_mem_of_fibrant
    (hF : ∀ ⦃X Y : C⦄ (p : X ⟶ Y), IsFibrant X → IsFibrant Y → Fibration p →
      WeakEquivalence p → W (F.map p))
    {X Y : C} [IsFibrant X] [IsFibrant Y] (f : X ⟶ Y) [WeakEquivalence f] : W (F.map f) := by
  obtain ⟨b⟩ := (inferInstance : Nonempty (FibrantBrownFactorization f))
  have : IsFibrant b.Z := isFibrant_of_fibration b.r
  have hr := hF b.r inferInstance inferInstance inferInstance inferInstance
  have hi : W (F.map b.i) :=
    W.of_postcomp _ _ hr (by rw [← F.map_comp, b.i_r, F.map_id]; exact W.id_mem _)
  rw [← b.fac, F.map_comp]
  exact W.comp_mem _ _ hi (hF b.p inferInstance inferInstance inferInstance inferInstance)

end CategoryTheory.Functor
