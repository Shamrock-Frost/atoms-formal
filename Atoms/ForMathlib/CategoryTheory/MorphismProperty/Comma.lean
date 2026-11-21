import Atoms.ForMathlib.CategoryTheory.MorphismProperty.Saturation
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.MorphismProperty.Comma

universe w v u

open CategoryTheory Limits

namespace CategoryTheory.MorphismProperty

instance HasFactorization.under {C : Type*} [Category* C] (W₁ W₂ : MorphismProperty C)
    [W₁.HasFactorization W₂] (S : C) :
    (W₁.under (X := S)).HasFactorization W₂.under where
  nonempty_mapFactorizationData {X Y} f := by
    let hf := W₁.factorizationData W₂ f.right
    exact ⟨{
      Z := .mk (X.hom ≫ hf.i)
      i := CategoryTheory.Under.homMk hf.i
      p := CategoryTheory.Under.homMk hf.p (by
        simp only [CategoryTheory.Under.mk_hom, Category.assoc, hf.fac, CategoryTheory.Under.w f])
      fac := by ext; exact hf.fac
      hi := hf.hi
      hp := hf.hp
    }⟩

variable {C : Type u} [Category.{v} C]

instance IsSaturated.under (P : MorphismProperty C) [IsSaturated.{w} P] (S : C) :
    IsSaturated.{w} (P.under (X := S)) where
  isStableUnderCobaseChange :=
    ⟨fun sq hf ↦ P.of_isPushout (sq.map (CategoryTheory.Under.forget S)) hf⟩
  isStableUnderRetracts := by
    rw [MorphismProperty.under_eq_inverseImage]
    infer_instance
  isStableUnderTransfiniteComposition :=
    ⟨fun J _ _ _ _ ↦
      have : IsConnected J := isConnected_of_hasInitial J
      have : PreservesWellOrderContinuousOfShape J (CategoryTheory.Under.forget S) := ⟨fun {j} hj ↦
        have : Nonempty (Set.Iio j) := ⟨⟨⊥, hj.bot_lt⟩⟩
        inferInstance⟩
      ⟨fun _ _ f hf ↦ P.transfiniteCompositionsOfShape_le J _
        (transfiniteCompositionsOfShape_map_of_preserves J (CategoryTheory.Under.forget S) f
          (P := P) hf)⟩⟩

end CategoryTheory.MorphismProperty
