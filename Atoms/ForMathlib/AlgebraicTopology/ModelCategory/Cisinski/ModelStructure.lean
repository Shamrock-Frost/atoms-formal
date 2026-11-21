import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Cisinski.FibrantObject
import Mathlib.AlgebraicTopology.ModelCategory.Basic

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra

universe v u

variable {C : Type u} [Category.{v} C]

@[instance_reducible]
def monoModelCategory [HasFiniteLimits C] [HasFiniteColimits C]
    [IsSaturated.{v} (monomorphisms C)]
    [HasFunctorialFactorization (monomorphisms C) (monomorphisms C).rlp]
    (V : MorphismProperty C) [V.HasTwoOutOfThreeProperty] [V.IsStableUnderRetracts]
    (hV : (monomorphisms C).rlp = (monomorphisms C ⊓ V).rlp ⊓ V)
    [HasFactorization (monomorphisms C ⊓ V) (monomorphisms C ⊓ V).rlp] :
    ModelCategory C :=
  have h5b : HasFactorization (monomorphisms C) ((monomorphisms C ⊓ V).rlp ⊓ V) := by
    rw [← hV]
    infer_instance
  { categoryWithFibrations := ⟨(monomorphisms C ⊓ V).rlp⟩
    categoryWithCofibrations := ⟨monomorphisms C⟩
    categoryWithWeakEquivalences := ⟨V⟩
    cm2 := ‹V.HasTwoOutOfThreeProperty›
    cm3a := ‹V.IsStableUnderRetracts›
    cm3b := rlp_isStableUnderRetracts _
    cm3c := IsSaturated.isStableUnderRetracts.{v} (W := monomorphisms C)
    cm4a := fun i _ hi hw hp ↦ hp.mem i ⟨hi.mem, hw.mem⟩
    cm4b := fun i p hi hp hw ↦ by
      have hp' : (monomorphisms C).rlp p := by
        rw [hV]
        exact ⟨hp.mem, hw.mem⟩
      exact hp' i hi.mem
    cm5a := ‹HasFactorization (monomorphisms C ⊓ V) _›
    cm5b := h5b }

namespace ExactCylinder

variable [HasBinaryCoproducts C] [HasPushouts C] [HasTerminal C] (𝕀 : ExactCylinder.{v} C)
  (S : MorphismProperty C)

def TrivialCofibrationsSetGenerated : Prop :=
  ∃ T : MorphismProperty C, MorphismProperty.IsSmall.{v} T ∧
    𝕀.trivialCofibrations S = saturation.{v} T

theorem hasFunctorialFactorization_trivialCofibrations [HasColimitsOfSize.{v, v} C]
    [IsLocallyPresentable.{v} C] (hgen : 𝕀.TrivialCofibrationsSetGenerated S) :
    HasFunctorialFactorization (𝕀.trivialCofibrations S) (𝕀.fibrations S) := by
  obtain ⟨T, hT, hTC⟩ := hgen
  rw [fibrations, hTC, rlp_saturation]
  exact hasFunctorialFactorization_saturation T

theorem trivialCofibrations_of_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hg : Mono g)
    (hf : 𝕀.trivialCofibrations S f) (hfg : 𝕀.trivialCofibrations S (f ≫ g)) :
    𝕀.trivialCofibrations S g :=
  ⟨hg, (𝕀.weakEquivalences S).of_precomp f g hf.2 hfg.2⟩

@[instance_reducible]
def modelCategoryOfSetGenerated [HasFiniteLimits C] [HasInitial C] [HasStrictInitialObjects C]
    [HasColimitsOfSize.{v, v} C] [IsLocallyPresentable.{v} C] [HasCellularModel C]
    (hgen : 𝕀.TrivialCofibrationsSetGenerated S) : ModelCategory C :=
  have := 𝕀.hasFunctorialFactorization_trivialCofibrations S hgen
  monoModelCategory (𝕀.weakEquivalences S) (𝕀.rlp_monomorphisms_eq S)

end ExactCylinder

end HomotopicalAlgebra
