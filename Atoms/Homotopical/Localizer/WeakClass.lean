import Atoms.Homotopical.Cellular.Model
import Atoms.Homotopical.Localizer.Basic
import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Cisinski.FibrantObject
import Atoms.ForMathlib.CategoryTheory.Presentable.Presheaf

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra

namespace Atoms.Homotopical

universe w v

variable {A : Type v} [SmallCategory A]

end Atoms.Homotopical

namespace HomotopicalAlgebra.ExactCylinder

open Atoms.Homotopical

universe w v

variable {A : Type v} [SmallCategory A]

variable (𝕀 : ExactCylinder.{max w v} (Aᵒᵖ ⥤ Type (max w v)))
  (S : MorphismProperty (Aᵒᵖ ⥤ Type (max w v)))

theorem isALocalizer_weakEquivalences [S.IsSmall.{max w v}]
    (hS : S ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v))) :
    IsALocalizer (𝕀.weakEquivalences S) where
  hasTwoOutOfThreeProperty := 𝕀.weakEquivalences_hasTwoOutOfThreeProperty S
  rlp_monomorphisms_le _ _ p hp := 𝕀.weakEquivalences_of_rlp_monomorphisms S p hp
  isStableUnderCobaseChange := (𝕀.isSaturated_trivialCofibrations S hS).isStableUnderCobaseChange
  isStableUnderTransfiniteComposition :=
    (𝕀.isSaturated_trivialCofibrations S hS).isStableUnderTransfiniteComposition

theorem anodyneGenerators_le_weakEquivalences
    (hS : S ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v))) :
    𝕀.anodyneGenerators S ≤ 𝕀.weakEquivalences S :=
  iSup_le fun n ↦
    (𝕀.anodyneGeneratorsStage_le_anodyne S hS n).trans (𝕀.anodyne_le_weakEquivalences S hS)

section

attribute [local instance] isSmall_anodyneGenerators
  hasSmallObjectArgument_of_isLocallyPresentable
  MorphismProperty.smallObjectκ_isRegular

theorem transfiniteCompositions_ιObj [S.IsSmall.{max w v}] {X Y : Aᵒᵖ ⥤ Type (max w v)}
    (f : X ⟶ Y) :
    (MorphismProperty.coproducts.{max w v}
      (𝕀.anodyneGenerators S)).pushouts.transfiniteCompositions.{max w v}
      (SmallObject.ιObj (𝕀.anodyneGenerators S)
        (𝕀.anodyneGenerators S).smallObjectκ.{max w v} f) :=
  transfiniteCompositionsOfShape_le_transfiniteCompositions _ _ _
    (SmallObject.transfiniteCompositionsOfShape_ιObj _ _ f)

theorem anodyne_ιObj [S.IsSmall.{max w v}]
    (hS : S ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)))
    {X Y : Aᵒᵖ ⥤ Type (max w v)} (f : X ⟶ Y) :
    𝕀.anodyne S
      (SmallObject.ιObj (𝕀.anodyneGenerators S)
        (𝕀.anodyneGenerators S).smallObjectκ.{max w v} f) := by
  rw [𝕀.anodyne_eq_llp_rlp S hS]
  exact SmallObject.llp_rlp_ιObj _ _ f

theorem rlp_anodyne_πObj (hS : S ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)))
    [S.IsSmall.{max w v}] {X Y : Aᵒᵖ ⥤ Type (max w v)} (f : X ⟶ Y) :
    𝕀.naiveFibrations S
      (SmallObject.πObj (𝕀.anodyneGenerators S)
        (𝕀.anodyneGenerators S).smallObjectκ.{max w v} f) := by
  rw [𝕀.naiveFibrations_eq_rlp_anodyneGenerators S hS]
  exact SmallObject.rlp_πObj _ _ f

theorem isFibrant_obj_terminal_from [S.IsSmall.{max w v}]
    (hS : S ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v))) (Y : Aᵒᵖ ⥤ Type (max w v)) :
    𝕀.IsFibrant S (SmallObject.obj (𝕀.anodyneGenerators S)
      (𝕀.anodyneGenerators S).smallObjectκ.{max w v} (terminal.from Y)) := by
  unfold IsFibrant
  rw [Subsingleton.elim (terminal.from _)
    (SmallObject.πObj (𝕀.anodyneGenerators S) (𝕀.anodyneGenerators S).smallObjectκ.{max w v}
      (terminal.from Y))]
  exact 𝕀.rlp_anodyne_πObj S hS _

theorem exists_cellular_rlp_monomorphisms_of_weakEquivalences [S.IsSmall.{max w v}]
    (hS : S ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)))
    {X Y : Aᵒᵖ ⥤ Type (max w v)} (f : X ⟶ Y) (hf : 𝕀.weakEquivalences S f) :
    ∃ (X' Y' : Aᵒᵖ ⥤ Type (max w v)) (i : X ⟶ X') (j : Y ⟶ Y') (f' : X' ⟶ Y'),
      i ≫ f' = f ≫ j ∧
      (MorphismProperty.coproducts.{max w v}
        (𝕀.anodyneGenerators S)).pushouts.transfiniteCompositions.{max w v} i ∧
      (MorphismProperty.coproducts.{max w v}
        (𝕀.anodyneGenerators S)).pushouts.transfiniteCompositions.{max w v} j ∧
      (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v))).rlp f' := by
  have h3 := 𝕀.weakEquivalences_hasTwoOutOfThreeProperty S
  let I := 𝕀.anodyneGenerators S
  let κ := I.smallObjectκ.{max w v}
  let j := SmallObject.ιObj I κ (terminal.from Y)
  let g := f ≫ j
  refine ⟨_, _, SmallObject.ιObj I κ g, j, SmallObject.πObj I κ g,
    SmallObject.ιObj_πObj I κ g, 𝕀.transfiniteCompositions_ιObj S g,
    𝕀.transfiniteCompositions_ιObj S _, ?_⟩
  have hj : 𝕀.weakEquivalences S j :=
    𝕀.anodyne_le_weakEquivalences S hS _ (𝕀.anodyne_ιObj S hS _)
  have hi : 𝕀.weakEquivalences S (SmallObject.ιObj I κ g) :=
    𝕀.anodyne_le_weakEquivalences S hS _ (𝕀.anodyne_ιObj S hS _)
  have hg : 𝕀.weakEquivalences S (SmallObject.ιObj I κ g ≫ SmallObject.πObj I κ g) := by
    rw [SmallObject.ιObj_πObj]
    exact (𝕀.weakEquivalences S).comp_mem f j hf hj
  have hf' := (𝕀.weakEquivalences S).of_precomp _ _ hi hg
  exact (𝕀.weakEquivalences_iff_rlp_monomorphisms_of_rlp_anodyne S _
    (𝕀.rlp_anodyne_πObj S hS g) (𝕀.isFibrant_obj_terminal_from S hS Y)).1 hf'

end

theorem weakEquivalences_eq_generatedALocalizer [S.IsSmall.{max w v}]
    (hS : S ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v))) :
    𝕀.weakEquivalences S = generatedALocalizer (𝕀.anodyneGenerators S) := by
  have := 𝕀.isALocalizer_weakEquivalences S hS
  refine le_antisymm (fun X Y f hf ↦ ?_)
    (generatedALocalizer_le (𝕀.anodyneGenerators_le_weakEquivalences S hS))
  rw [generatedALocalizer_iff]
  intro V hV hIV
  obtain ⟨X', Y', i, j, f', hsq, hi, hj, hf'⟩ :=
    𝕀.exists_cellular_rlp_monomorphisms_of_weakEquivalences S hS f hf
  have hT : 𝕀.anodyneGenerators S ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)) ⊓ V :=
    le_inf (𝕀.anodyneGenerators_le_monomorphisms S hS) hIV
  have hiV := (hV.transfiniteCompositions_pushouts_coproducts_le hT _ hi).2
  have hjV := (hV.transfiniteCompositions_pushouts_coproducts_le hT _ hj).2
  have hfj : V (f ≫ j) := by
    rw [← hsq]
    exact V.comp_mem i f' hiV (hV.rlp_monomorphisms_le _ hf')
  exact V.of_postcomp f j hjV hfj

theorem isAccessibleALocalizer_weakEquivalences [S.IsSmall.{max w v}]
    (hS : S ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v))) :
    IsAccessibleALocalizer (𝕀.weakEquivalences S) :=
  .of_eq (𝕀.isSmall_anodyneGenerators S) (𝕀.weakEquivalences_eq_generatedALocalizer S hS).symm

end HomotopicalAlgebra.ExactCylinder
