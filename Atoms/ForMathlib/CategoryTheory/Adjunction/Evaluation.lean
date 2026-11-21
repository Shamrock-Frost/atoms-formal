import Atoms.ForMathlib.CategoryTheory.Types.Monomorphisms
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.LiftingProperties.Adjunction
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
import Mathlib.CategoryTheory.Types.Monomorphisms

namespace CategoryTheory

open Opposite

universe u

variable {A : Type u} [SmallCategory A]

theorem rlp_monomorphisms_evaluationRightAdjoint_map (a : A) {S T : Type u} {p : S ⟶ T}
    (hp : Function.Surjective p) :
    (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type u)).rlp
      ((evaluationRightAdjoint (Type u) (op a)).map p) := fun K L i hi => by
  have : Mono i := hi
  have hm : Mono (((evaluation Aᵒᵖ (Type u)).obj (op a)).map i) :=
    inferInstanceAs (Mono (i.app (op a)))
  exact ((evaluationAdjunctionLeft (Type u) (op a)).hasLiftingProperty_iff i p).1
    (Types.hasLiftingProperty_of_injective_of_surjective ((mono_iff_injective _).1 hm) hp)

end CategoryTheory
