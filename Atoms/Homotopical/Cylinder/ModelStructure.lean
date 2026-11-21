import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Cisinski.ModelStructure
import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant
import Atoms.Homotopical.Cellular.BoundedGenerators
import Atoms.Homotopical.Cylinder.BoundedEnlargement
import Atoms.ForMathlib.CategoryTheory.Presentable.Presheaf

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra

namespace HomotopicalAlgebra.ExactCylinder

open Atoms.Homotopical

universe v u

section Embedding

variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C] [HasPushouts C] [HasTerminal C]
  [HasCellularModel C] [HasColimitsOfSize.{v, v} C] [IsLocallyPresentable.{v} C]
  [HasPullbacks C] [FinitaryPreExtensive C] [HasEffectiveUnions C] [HasBinaryProducts C]
  [(monomorphisms C).IsStableUnderFilteredColimits.{v, v}]
  {B : Type v} [SmallCategory B] (E : BoundedEmbedding C B)
  (𝕀 : ExactCylinder.{v} C) (S : MorphismProperty C) [S.IsSmall.{v}]

include E in
theorem trivialCofibrationsSetGenerated_of_embedding
    (hS : S ≤ MorphismProperty.monomorphisms C) :
    𝕀.TrivialCofibrationsSetGenerated S := by
  have := 𝕀.isSaturated_trivialCofibrations S hS
  obtain ⟨α₀, hα₀, henlarge⟩ := 𝕀.exists_bounded_enlargement_of_embedding E S hS
  obtain ⟨α, hα₀α, -, hα⟩ := exists_two_pow_bound B α₀
  obtain ⟨-, -, hB⟩ := hα α le_rfl
  obtain ⟨ι, R, -, hrep⟩ := E.exists_boundedRepresentatives (2 ^ α)
  refine ⟨E.boundedGenerators (𝕀.trivialCofibrations S) R, inferInstance, ?_⟩
  refine E.eq_saturation_boundedGenerators (E.IsBounded (2 ^ α)) _ (fun _ _ _ h => h.1)
    (fun f g _ hg hf hfg => 𝕀.trivialCofibrations_of_comp S f g hg hf hfg) R hrep
    (fun X => eq_top_iff.2 ((iSup_boundedSubfunctor_eq_top hB (E.ι.obj X)).ge.trans
      (iSup_le fun T => le_iSup_of_le ⟨T.1, (E.isBounded_sub_iff _ _).2 T.2⟩ le_rfl)))
    fun i hi Z hZ => ?_
  obtain ⟨K, hZK, hK, hKi⟩ := henlarge α hα₀α i hi Z ((E.isBounded_sub_iff _ _).1 hZ)
  exact ⟨K, hZK, (E.isBounded_sub_iff _ _).2 hK, hKi⟩

@[instance_reducible]
def modelCategoryOfEmbedding [HasFiniteLimits C] [HasInitial C]
    [HasStrictInitialObjects C]
    (hS : S ≤ MorphismProperty.monomorphisms C) : ModelCategory C :=
  𝕀.modelCategoryOfSetGenerated S (𝕀.trivialCofibrationsSetGenerated_of_embedding E S hS)

end Embedding

end HomotopicalAlgebra.ExactCylinder

namespace HomotopicalAlgebra.ExactCylinder

open Atoms.Homotopical

universe w v

variable {A : Type v} [SmallCategory A]

variable (𝕀 : ExactCylinder.{max w v} (Aᵒᵖ ⥤ Type (max w v)))
  (S : MorphismProperty (Aᵒᵖ ⥤ Type (max w v)))

theorem trivialCofibrationsSetGenerated [S.IsSmall.{max w v}]
    (hS : S ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v))) :
    𝕀.TrivialCofibrationsSetGenerated S :=
  𝕀.trivialCofibrationsSetGenerated_of_embedding (BoundedEmbedding.asSmall.{w} A) S hS

@[instance_reducible]
def modelCategory [S.IsSmall.{max w v}]
    (hS : S ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v))) :
    ModelCategory (Aᵒᵖ ⥤ Type (max w v)) :=
  𝕀.modelCategoryOfEmbedding (BoundedEmbedding.asSmall A) S hS

namespace modelCategory

variable [S.IsSmall.{max w v}]
  (hS : S ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)))

theorem cofibrations_eq :
    letI := 𝕀.modelCategory S hS
    cofibrations (Aᵒᵖ ⥤ Type (max w v)) = MorphismProperty.monomorphisms _ := rfl

theorem weakEquivalences_eq :
    letI := 𝕀.modelCategory S hS
    HomotopicalAlgebra.weakEquivalences (Aᵒᵖ ⥤ Type (max w v)) = 𝕀.weakEquivalences S := rfl

theorem fibrations_eq :
    letI := 𝕀.modelCategory S hS
    HomotopicalAlgebra.fibrations (Aᵒᵖ ⥤ Type (max w v)) = 𝕀.fibrations S := rfl

theorem isFibrant_iff (X : Aᵒᵖ ⥤ Type (max w v)) :
    letI := 𝕀.modelCategory S hS
    HomotopicalAlgebra.IsFibrant X ↔ 𝕀.IsFibrant S X := by
  let := 𝕀.modelCategory S hS
  exact (HomotopicalAlgebra.fibration_iff _).trans
    (𝕀.rlp_trivialCofibrations_terminal_from_iff S hS X)

end modelCategory

end HomotopicalAlgebra.ExactCylinder
