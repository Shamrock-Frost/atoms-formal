import Atoms.ForMathlib.AlgebraicTopology.SimplexCategory.Augmented.Decalage
import Mathlib.CategoryTheory.Subfunctor.Basic

open CategoryTheory MonoidalCategory Opposite Simplicial

namespace AugmentedSimplexCategory

universe w

variable {C : Type*} [Category C]

structure ExtraDegeneracy (P : AugmentedSimplexCategoryᵒᵖ ⥤ C) where
  h : P ⟶ (decalage C).obj P
  h_comp_counit : h ≫ (decalageCounit C).app P = 𝟙 P
  h_comp_comult : h ≫ (decalageComult C).app P = h ≫ (decalage C).map h

namespace ExtraDegeneracy

variable {P : AugmentedSimplexCategoryᵒᵖ ⥤ C} (h : ExtraDegeneracy P)

@[reassoc]
theorem app_comp_map_inr (y : AugmentedSimplexCategory) :
    h.h.app (op y) ≫ P.map (inr (WithInitial.of ⦋0⦌) y).op = 𝟙 _ :=
  NatTrans.congr_app h.h_comp_counit (op y)

@[reassoc]
theorem map_comp_app {y y' : AugmentedSimplexCategory} (f : y ⟶ y') :
    P.map f.op ≫ h.h.app (op y) = h.h.app (op y') ≫ P.map (WithInitial.of ⦋0⦌ ◁ f).op :=
  h.h.naturality f.op

@[reassoc]
theorem app_comp_app (y : AugmentedSimplexCategory) :
    h.h.app (op y) ≫ h.h.app (op (WithInitial.of ⦋0⦌ ⊗ y)) =
      h.h.app (op y) ≫ P.map ((α_ _ _ y).inv ≫ zeroMul ▷ y).op :=
  (NatTrans.congr_app h.h_comp_comult (op y)).symm

section Descent

variable {P : AugmentedSimplexCategoryᵒᵖ ⥤ Type w} {I : Type*}
  {E : I → AugmentedSimplexCategoryᵒᵖ ⥤ Type w} (hE : ∀ i, ExtraDegeneracy (E i))
  (π : ∀ i, E i ⟶ P)

theorem exists_of_jointlySurjective
    (hsurj : ∀ (a : AugmentedSimplexCategoryᵒᵖ) (x : P.obj a), ∃ (i : I) (y : (E i).obj a),
      (π i).app a y = x)
    (hwd : ∀ (a : AugmentedSimplexCategoryᵒᵖ) (i j : I) (y : (E i).obj a) (y' : (E j).obj a),
      (π i).app a y = (π j).app a y' → ((hE i).h ≫ (decalage _).map (π i)).app a y =
        ((hE j).h ≫ (decalage _).map (π j)).app a y') :
    ∃ h : ExtraDegeneracy P, ∀ i, π i ≫ h.h = (hE i).h ≫ (decalage _).map (π i) := by
  choose i y hy using hsurj
  let F : ∀ a, P.obj a → ((decalage _).obj P).obj a := fun a x =>
    ((hE (i a x)).h ≫ (decalage _).map (π (i a x))).app a (y a x)
  have hF : ∀ (a : AugmentedSimplexCategoryᵒᵖ) (j : I) (z : (E j).obj a),
      F a ((π j).app a z) = ((hE j).h ≫ (decalage _).map (π j)).app a z :=
    fun a j z => hwd a _ _ _ _ (hy a _)
  have hnat : ∀ (a b : AugmentedSimplexCategoryᵒᵖ) (f : a ⟶ b) (j : I) (z : (E j).obj a),
      F b (P.map f ((π j).app a z)) = ((decalage _).obj P).map f (F a ((π j).app a z)) := by
    intro a b f j z
    rw [← NatTrans.naturality_apply, hF, hF]
    exact NatTrans.naturality_apply ((hE j).h ≫ (decalage _).map (π j)) f z
  let h : P ⟶ (decalage _).obj P :=
    { app a := ↾F a
      naturality a b f := by
        ext x
        have := hnat a b f (i a x) (y a x)
        rw [hy] at this
        exact this }
  have hπ : ∀ j, π j ≫ h = (hE j).h ≫ (decalage _).map (π j) := fun j => by
    ext a z
    exact hF a j z
  have hext : ∀ {Y : AugmentedSimplexCategoryᵒᵖ ⥤ Type w} (g g' : P ⟶ Y),
      (∀ j, π j ≫ g = π j ≫ g') → g = g' := fun g g' hg => by
    ext a x
    rw [← hy a x]
    exact congrArg (fun t => t.app a (y a x)) (hg (i a x))
  refine ⟨⟨h, hext _ _ fun j => ?_, hext _ _ fun j => ?_⟩, hπ⟩
  · rw [reassoc_of% (hπ j), (decalageCounit _).naturality, ← Category.assoc,
      (hE j).h_comp_counit, Category.comp_id, Category.id_comp, Functor.id_map]
  · rw [reassoc_of% (hπ j), (decalageComult _).naturality, ← Category.assoc,
      (hE j).h_comp_comult, reassoc_of% (hπ j), Functor.comp_map, Category.assoc,
      ← Functor.map_comp, ← Functor.map_comp, hπ, Functor.map_comp]

theorem h_comp_map_eq_of_jointlySurjective {Q : AugmentedSimplexCategoryᵒᵖ ⥤ Type w}
    (p : P ⟶ Q) (hQ : ExtraDegeneracy Q)
    (hsurj : ∀ (a : AugmentedSimplexCategoryᵒᵖ) (x : P.obj a), ∃ (i : I) (y : (E i).obj a),
      (π i).app a y = x)
    (h : ExtraDegeneracy P) (hπ : ∀ i, π i ≫ h.h = (hE i).h ≫ (decalage _).map (π i))
    (hp : ∀ i, (hE i).h ≫ (decalage _).map (π i ≫ p) = π i ≫ p ≫ hQ.h) :
    h.h ≫ (decalage _).map p = p ≫ hQ.h := by
  ext a x
  obtain ⟨i, y, rfl⟩ := hsurj a x
  have := congrArg (fun t => t.app a y) ((reassoc_of% (hπ i)) ((decalage _).map p))
  rw [← Functor.map_comp, hp] at this
  exact this

end Descent

end ExtraDegeneracy

def boundary (a : AugmentedSimplexCategory) : Subfunctor (uliftYoneda.{w}.obj a) where
  obj b := {f | ¬ Function.Surjective (toFun f.down)}
  map g f hf hs := hf (Function.Surjective.of_comp (g := toFun g.unop) fun i => by
    obtain ⟨j, hj⟩ := hs i
    exact ⟨j, (toFun_comp_apply g.unop f.down j).symm.trans hj⟩)

end AugmentedSimplexCategory
