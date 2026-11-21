import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.BrownLemma
import Mathlib.AlgebraicTopology.ModelCategory.BrownLemma
import Mathlib.AlgebraicTopology.ModelCategory.Instances

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra

variable {C : Type*} [Category* C] [ModelCategory C]

private theorem weakEquivalence_prodMap_id_of_trivialFibration {X X' : C} (Y : C) (p : X ⟶ X')
    [Fibration p] [WeakEquivalence p] : WeakEquivalence (prod.map p (𝟙 Y)) :=
  (weakEquivalence_iff _).2 ((trivialFibrations C).of_isPullback
    (IsPullback.of_prod_fst_with_id p Y) (mem_trivialFibrations p)).2

theorem weakEquivalence_prodMap_id {X X' : C} (Y : C) [IsFibrant X] [IsFibrant X']
    (f : X ⟶ X') [WeakEquivalence f] : WeakEquivalence (prod.map f (𝟙 Y)) := by
  rw [weakEquivalence_iff]
  exact (prod.functor.flip.obj Y).map_mem_of_fibrant (weakEquivalences C)
    (fun _ _ p _ _ _ _ => (weakEquivalence_iff _).1
      (weakEquivalence_prodMap_id_of_trivialFibration Y p)) f

theorem weakEquivalence_id_prodMap (X : C) {Y Y' : C} [IsFibrant Y] [IsFibrant Y']
    (g : Y ⟶ Y') [WeakEquivalence g] : WeakEquivalence (prod.map (𝟙 X) g) := by
  have := weakEquivalence_prodMap_id X g
  have e : prod.map (𝟙 X) g = (prod.braiding X Y).hom ≫ prod.map g (𝟙 X) ≫
      (prod.braiding Y' X).hom := by
    ext <;> simp only [prod.braiding_hom, prod.map_fst, prod.map_snd, Category.comp_id,
      Category.assoc, prod.lift_fst, prod.lift_snd, prod.lift_fst_assoc]
  rw [e]
  infer_instance

theorem weakEquivalence_prodMap {X X' Y Y' : C} [IsFibrant X] [IsFibrant X'] [IsFibrant Y]
    [IsFibrant Y'] (f : X ⟶ X') (g : Y ⟶ Y') [WeakEquivalence f] [WeakEquivalence g] :
    WeakEquivalence (prod.map f g) := by
  have := weakEquivalence_prodMap_id Y f
  have := weakEquivalence_id_prodMap X' g
  rw [show prod.map f g = prod.map f (𝟙 Y) ≫ prod.map (𝟙 X') g by
    rw [prod.map_map, Category.comp_id, Category.id_comp]]
  infer_instance

theorem weakEquivalence_piMap {J : Type*} {X Y : J → C}
    [HasProductsOfShape J C] [∀ j, IsFibrant (X j)] [∀ j, IsFibrant (Y j)]
    (f : ∀ j, X j ⟶ Y j) [∀ j, WeakEquivalence (f j)] :
    WeakEquivalence (Limits.Pi.map f) := by
  let b (j : J) : FibrantBrownFactorization (f j) := Classical.choice inferInstance
  have : ∀ j, Fibration (b j).p := fun j => inferInstance
  have : ∀ j, WeakEquivalence (b j).p := fun j => inferInstance
  have : ∀ j, Fibration (b j).r := fun j => inferInstance
  have : ∀ j, WeakEquivalence (b j).r := fun j => inferInstance
  have : WeakEquivalence (Limits.Pi.map fun j => (b j).r) := inferInstance
  have hi : Limits.Pi.map (fun j => (b j).i) ≫ Limits.Pi.map (fun j => (b j).r) = 𝟙 _ := by
    apply Pi.hom_ext
    intro j
    rw [Category.assoc, Pi.map_π, Pi.map_π_assoc, (b j).i_r,
      Category.comp_id, Category.id_comp]
  have : WeakEquivalence (Limits.Pi.map fun j => (b j).i) :=
    weakEquivalence_of_postcomp_of_fac hi
  have hf : Limits.Pi.map f =
      Limits.Pi.map (fun j => (b j).i) ≫ Limits.Pi.map (fun j => (b j).p) := by
    apply Pi.hom_ext
    intro j
    rw [Pi.map_π, Category.assoc, Pi.map_π, Pi.map_π_assoc, (b j).fac]
  rw [hf]
  infer_instance

end HomotopicalAlgebra
