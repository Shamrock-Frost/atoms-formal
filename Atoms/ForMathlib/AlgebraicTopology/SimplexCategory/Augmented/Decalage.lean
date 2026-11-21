import Atoms.ForMathlib.AlgebraicTopology.SimplexCategory.Augmented.Monoidal

open CategoryTheory MonoidalCategory Opposite Simplicial

namespace AugmentedSimplexCategory

def zeroMul : (WithInitial.of ⦋0⦌ ⊗ WithInitial.of ⦋0⦌ : AugmentedSimplexCategory) ⟶
    WithInitial.of ⦋0⦌ :=
  inclusion.map (SimplexCategory.const _ ⦋0⦌ 0)

variable (C : Type*) [Category C]

def decalage : (AugmentedSimplexCategoryᵒᵖ ⥤ C) ⥤ (AugmentedSimplexCategoryᵒᵖ ⥤ C) :=
  (Functor.whiskeringLeft _ _ C).obj (tensorLeft (WithInitial.of ⦋0⦌)).op

def decalageCounit : decalage C ⟶ 𝟭 _ where
  app P :=
    { app y := P.map (inr (WithInitial.of ⦋0⦌) y.unop).op
      naturality y y' g := by
        dsimp [decalage]
        rw [← P.map_comp, ← P.map_comp]
        congr 1
        apply Quiver.Hom.unop_inj
        dsimp
        rw [← id_tensorHom, inr_comp_tensorHom] }
  naturality P Q f := by
    ext y
    exact (f.naturality _).symm

def decalageComult : decalage C ⟶ decalage C ⋙ decalage C where
  app P :=
    { app y := P.map ((α_ _ _ y.unop).inv ≫ zeroMul ▷ y.unop).op
      naturality y y' g := by
        dsimp [decalage]
        rw [← P.map_comp, ← P.map_comp]
        congr 1
        apply Quiver.Hom.unop_inj
        dsimp
        rw [Category.assoc, associator_inv_naturality_right_assoc, whisker_exchange] }
  naturality P Q f := by
    ext y
    exact (f.naturality _).symm

end AugmentedSimplexCategory
