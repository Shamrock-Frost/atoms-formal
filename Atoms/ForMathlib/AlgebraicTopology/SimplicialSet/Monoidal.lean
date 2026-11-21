import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

universe u

namespace SSet

open CategoryTheory MonoidalCategory

def rightFactorProjection {C : Type u} [SmallCategory C]
    (k : C ⥤ SSet.{u}) (T : SSet.{u}) : k ⋙ tensorRight T ⟶ k where
  app a := CartesianMonoidalCategory.fst _ _
  naturality a b f := by cat_disch

end SSet
