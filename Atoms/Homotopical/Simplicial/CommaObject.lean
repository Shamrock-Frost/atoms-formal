import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Over
import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.CommaObject
import Atoms.Homotopical.Simplicial.CartesianMonoidal

open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory Simplicial
  HomotopicalAlgebra

universe u

namespace SSet

variable {A B A' B' : SSet.{u}} {F : A ⟶ B} {F' : A' ⟶ B'} {b : 𝟙_ SSet.{u} ⟶ B}
  {b' : 𝟙_ SSet.{u} ⟶ B'}

open modelCategoryJoyal in
theorem modelCategoryJoyal.weakEquivalence_commaObjectMap (α : Bool) (u : A ⟶ A') (v : B ⟶ B')
    (hF : F ≫ v = u ≫ F') (hb : b ≫ v = b') [A.Quasicategory] [A'.Quasicategory]
    [B.Quasicategory] [B'.Quasicategory] [WeakEquivalence u] [WeakEquivalence v] :
    WeakEquivalence (commaObjectMap α u v hF hb) := by
  have : IsFibrant A := (isFibrant_iff_quasicategory A).2 inferInstance
  have : IsFibrant A' := (isFibrant_iff_quasicategory A').2 inferInstance
  have : IsFibrant B := (isFibrant_iff_quasicategory B).2 inferInstance
  have : IsFibrant B' := (isFibrant_iff_quasicategory B').2 inferInstance
  have : IsFibrant ((ihom (∂Δ[1] : SSet.{u})).obj B) :=
    (isFibrant_iff_quasicategory _).2 inferInstance
  have : IsFibrant ((ihom (∂Δ[1] : SSet.{u})).obj B') :=
    (isFibrant_iff_quasicategory _).2 inferInstance
  have : Fibration ((pre (∂Δ[1]).ι).app B) :=
    (fibration_iff_isofibration _).2 (isofibration_pre_boundaryOne B)
  have : Fibration ((pre (∂Δ[1]).ι).app B') :=
    (fibration_iff_isofibration _).2 (isofibration_pre_boundaryOne B')
  have := weakEquivalence_ihom_map Δ[1] v
  have := weakEquivalence_ihom_map (∂Δ[1] : SSet.{u}) v
  exact (isPullback_commaObject α F b).weakEquivalence_map_of_fibration
    (isPullback_commaObject α F' b') ((ihom Δ[1]).map v) ((ihom (∂Δ[1] : SSet.{u})).map v) u
    (commaObjectMap α u v hF hb) (pre_comm_ihom_map _ _)
    (commaObjectBase_comp_ihom_map α u v hF hb) (commaObjectMap_arrow α u v hF hb)
    (commaObjectMap_π α u v hF hb)

end SSet
