import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Uniqueness
import Atoms.Homotopical.Simplicial.Joyal
import Atoms.Homotopical.Simplicial.KanQuillen

open CategoryTheory HomotopicalAlgebra

universe u

namespace SSet

theorem modelCategoryQuillen.eq_kanQuillenModelCategory (M : ModelCategory SSet.{u})
    (hc : @cofibrations SSet.{u} _ M.categoryWithCofibrations =
      MorphismProperty.monomorphisms SSet.{u})
    (hf : ∀ X : SSet.{u}, @IsFibrant SSet.{u} _ M.categoryWithFibrations _ X ↔ X.KanComplex) :
    M = modelCategoryQuillen.kanQuillenModelCategory :=
  ModelCategory.eq_of_cofibrations_eq_of_isFibrant_iff _ _ hc hf

theorem modelCategoryJoyal.eq_joyalModelCategory (M : ModelCategory SSet.{u})
    (hc : @cofibrations SSet.{u} _ M.categoryWithCofibrations =
      MorphismProperty.monomorphisms SSet.{u})
    (hf : ∀ X : SSet.{u}, @IsFibrant SSet.{u} _ M.categoryWithFibrations _ X ↔ X.Quasicategory) :
    M = modelCategoryJoyal.joyalModelCategory :=
  ModelCategory.eq_of_cofibrations_eq_of_isFibrant_iff _ _ hc fun X =>
    (hf X).trans (letI := modelCategoryJoyal.joyalModelCategory.{u};
      (modelCategoryJoyal.isFibrant_iff_quasicategory X).symm)

end SSet
