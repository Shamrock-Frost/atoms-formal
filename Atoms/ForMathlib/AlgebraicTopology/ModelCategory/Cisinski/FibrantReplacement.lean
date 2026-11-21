import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Cisinski.FibrantObject
import Atoms.ForMathlib.CategoryTheory.SmallObject.CellularReplacement

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra.ExactCylinder

universe v u

variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C] [HasPushouts C] [HasTerminal C]
  [HasCellularModel C] [HasColimitsOfSize.{v, v} C] [IsLocallyPresentable.{v} C]

noncomputable def fibrantReplacement (𝕀 : ExactCylinder.{v} C) (S : MorphismProperty C)
    [S.IsSmall.{v}] : C ⥤ C :=
  letI := 𝕀.isSmall_anodyneGenerators S
  letI := MorphismProperty.smallObjectκ_isRegular.{v} (𝕀.anodyneGenerators S)
  SmallObject.cellularReplacement (𝕀.anodyneGenerators S)
    (𝕀.anodyneGenerators S).smallObjectκ.{v}

noncomputable def fibrantReplacementUnit (𝕀 : ExactCylinder.{v} C) (S : MorphismProperty C)
    [S.IsSmall.{v}] : 𝟭 C ⟶ 𝕀.fibrantReplacement S :=
  letI := 𝕀.isSmall_anodyneGenerators S
  letI := MorphismProperty.smallObjectκ_isRegular.{v} (𝕀.anodyneGenerators S)
  SmallObject.cellularReplacementUnit (𝕀.anodyneGenerators S)
    (𝕀.anodyneGenerators S).smallObjectκ.{v}

variable (𝕀 : ExactCylinder.{v} C) (S : MorphismProperty C) [S.IsSmall.{v}]

section

attribute [local instance] isSmall_anodyneGenerators
  MorphismProperty.smallObjectκ_isRegular

theorem fibrantReplacement_eq :
    𝕀.fibrantReplacement S =
      SmallObject.cellularReplacement (𝕀.anodyneGenerators S)
        (𝕀.anodyneGenerators S).smallObjectκ.{v} :=
  rfl

theorem fibrantReplacementUnit_eq :
    𝕀.fibrantReplacementUnit S =
      SmallObject.cellularReplacementUnit (𝕀.anodyneGenerators S)
        (𝕀.anodyneGenerators S).smallObjectκ.{v} :=
  rfl

theorem exists_isCardinalAccessible_fibrantReplacement :
    ∃ (κ : Cardinal.{v}) (_ : Fact κ.IsRegular),
      (𝕀.fibrantReplacement S).IsCardinalAccessible κ := by
  have := 𝕀.isSmall_anodyneGenerators S
  obtain ⟨κ', hκ', hU⟩ := exists_isCardinalPresentable_of_isSmall (𝕀.anodyneGenerators S)
  exact ⟨κ', hκ', SmallObject.isCardinalAccessible_cellularReplacement _ _ κ' hU⟩

variable [HasPullbacks C] [FinitaryPreExtensive C] [HasEffectiveUnions C] [HasBinaryProducts C]

theorem anodyne_fibrantReplacementUnit (hS : S ≤ MorphismProperty.monomorphisms C) (X : C) :
    𝕀.anodyne S ((𝕀.fibrantReplacementUnit S).app X) := by
  rw [𝕀.anodyne_eq_llp_rlp S hS, fibrantReplacementUnit_eq]
  exact SmallObject.llp_rlp_cellularReplacementUnit _ _ X

theorem isFibrant_fibrantReplacement (hS : S ≤ MorphismProperty.monomorphisms C) (X : C) :
    𝕀.IsFibrant S ((𝕀.fibrantReplacement S).obj X) := by
  rw [isFibrant_iff_naiveFibrations, 𝕀.naiveFibrations_eq_rlp_anodyneGenerators S hS,
    fibrantReplacement_eq]
  exact SmallObject.rlp_terminal_from_cellularReplacement _ _ X

omit [HasBinaryProducts C] in
theorem mono_fibrantReplacement_map [(monomorphisms C).IsStableUnderFilteredColimits.{v, v}]
    (hS : S ≤ MorphismProperty.monomorphisms C) {X Y : C} (u : X ⟶ Y) [Mono u] :
    Mono ((𝕀.fibrantReplacement S).map u) := by
  have := IsCellularlyClosed.isStableUnderCoproducts.{v} (monomorphisms C)
  rw [fibrantReplacement_eq]
  exact SmallObject.mono_cellularReplacement_map _ _
    (𝕀.anodyneGenerators_le_monomorphisms S hS) u

end

variable [HasPullbacks C] [FinitaryPreExtensive C] [HasEffectiveUnions C] [HasBinaryProducts C]
  [(monomorphisms C).IsStableUnderFilteredColimits.{v, v}]

theorem exists_deformation_retract_fibrantReplacement_map
    (hS : S ≤ MorphismProperty.monomorphisms C) {X Y : C} (i : X ⟶ Y)
    (hi : 𝕀.trivialCofibrations S i) :
    Nonempty (𝕀.DeformationRetract ((𝕀.fibrantReplacement S).map i)) := by
  have : Mono i := hi.1
  have hmono := 𝕀.mono_fibrantReplacement_map S hS i
  have hl : ∀ X, 𝕀.weakEquivalences S ((𝕀.fibrantReplacementUnit S).app X) := fun X =>
    𝕀.anodyne_le_weakEquivalences S hS _ (𝕀.anodyne_fibrantReplacementUnit S hS X)
  have e : (𝕀.fibrantReplacementUnit S).app X ≫ (𝕀.fibrantReplacement S).map i =
      i ≫ (𝕀.fibrantReplacementUnit S).app Y :=
    ((𝕀.fibrantReplacementUnit S).naturality i).symm
  have hw : 𝕀.weakEquivalences S ((𝕀.fibrantReplacement S).map i) :=
    of_precomp _ _ _ (hl X) (by rw [e]; exact comp_mem _ _ _ hi.2 (hl Y))
  have ha := (𝕀.anodyne_iff_weakEquivalences_of_isFibrant S hS _ hmono
    (𝕀.isFibrant_fibrantReplacement S hS Y)).2 hw
  exact 𝕀.exists_deformation_retract_of_anodyne S hS _ ha
    (𝕀.isFibrant_fibrantReplacement S hS X) (𝕀.isFibrant_fibrantReplacement S hS Y)

omit [(monomorphisms C).IsStableUnderFilteredColimits.{v, v}] in
theorem trivialCofibrations_of_deformation_retract_fibrantReplacement_map
    (hS : S ≤ MorphismProperty.monomorphisms C) {M K : C}
    (u : M ⟶ K) [Mono u] (d : 𝕀.DeformationRetract ((𝕀.fibrantReplacement S).map u)) :
    𝕀.trivialCofibrations S u := by
  have ha := 𝕀.anodyne_of_deformation_retract S hS _ d
  have hl : ∀ X, 𝕀.weakEquivalences S ((𝕀.fibrantReplacementUnit S).app X) := fun X =>
    𝕀.anodyne_le_weakEquivalences S hS _ (𝕀.anodyne_fibrantReplacementUnit S hS X)
  have e : (𝕀.fibrantReplacementUnit S).app M ≫ (𝕀.fibrantReplacement S).map u =
      u ≫ (𝕀.fibrantReplacementUnit S).app K :=
    ((𝕀.fibrantReplacementUnit S).naturality u).symm
  refine ⟨(inferInstance : Mono u), of_postcomp _ u _ (hl K) ?_⟩
  rw [← e]
  exact comp_mem _ _ _ (hl M) (𝕀.anodyne_le_weakEquivalences S hS _ ha)

end HomotopicalAlgebra.ExactCylinder
