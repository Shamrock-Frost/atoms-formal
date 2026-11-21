import Atoms.Homotopical.Simplicial.Joyal
import Atoms.Homotopical.Simplicial.KanQuillen
import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Cisinski.Quillen

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra

universe u

namespace Atoms.Homotopical

theorem joyal_isFibrant_of_kanComplex (X : SSet.{u}) [X.KanComplex] :
    joyalInterval.{u}.cylinder.IsFibrant SSet.innerHornInclusions X := by
  exact (ExactCylinder.modelCategory.isFibrant_iff _ _ _ X).1
    ((SSet.modelCategoryJoyal.isFibrant_iff_quasicategory X).2 inferInstance)

theorem joyal_weakEquivalences_le_kanWeak :
    joyalInterval.{u}.cylinder.weakEquivalences SSet.innerHornInclusions ≤ kanWeak := by
  refine ExactCylinder.weakEquivalences_le_of_isFibrant _ _ _ _ fun X hX => ?_
  have := (isFibrant_bot_iff_kanComplex X).1 hX
  exact joyal_isFibrant_of_kanComplex X

open SSet.modelCategoryQuillen in
theorem kanComplex_of_joyal_weakEquivalences {X Y : SSet.{u}} [X.KanComplex]
    (hY : joyalInterval.{u}.cylinder.IsFibrant SSet.innerHornInclusions Y) (f : X ⟶ Y)
    (hf : joyalInterval.{u}.cylinder.weakEquivalences SSet.innerHornInclusions f) :
    Y.KanComplex := by
  obtain ⟨g, hfg, hgf⟩ := joyalInterval.{u}.cylinder.exists_homotopy_inverse_of_weakEquivalences
    SSet.innerHornInclusions (joyal_isFibrant_of_kanComplex X) hY f hf
  apply (isFibrant_iff Y).2
  exact (SSet.modelCategoryQuillen.fibration_iff (terminal.from Y)).2
    (joyalInterval.{u}.cylinder.rlp_terminal_from_of_homotopy_retract SSet.innerHornInclusions
      SSet.modelCategoryQuillen.J SSet.modelCategoryQuillen.J_le_monomorphisms hY
      ((SSet.modelCategoryQuillen.fibration_iff (terminal.from X)).1 inferInstance) g f hgf)

theorem joyal_weakEquivalences_iff_kanWeak {X Y : SSet.{u}} [X.KanComplex] [Y.KanComplex]
    (f : X ⟶ Y) :
    joyalInterval.{u}.cylinder.weakEquivalences SSet.innerHornInclusions f ↔ kanWeak f := by
  refine ⟨fun hf => joyal_weakEquivalences_le_kanWeak f hf, fun hf => ?_⟩
  have hX := (isFibrant_bot_iff_kanComplex X).2 inferInstance
  have hY := (isFibrant_bot_iff_kanComplex Y).2 inferInstance
  obtain ⟨g, hfg, hgf⟩ :=
    simplicialCylinder.exists_homotopy_inverse_of_weakEquivalences ⊥ hX hY f hf
  exact joyalInterval.{u}.cylinder.weakEquivalences_of_homotopic _ f g
    ((ExactCylinder.homotopic_iff_of_isFibrant _ _ ⊥ SSet.innerHornInclusions hX
      (joyal_isFibrant_of_kanComplex X) _ _).1 hfg)
    ((ExactCylinder.homotopic_iff_of_isFibrant _ _ ⊥ SSet.innerHornInclusions hY
      (joyal_isFibrant_of_kanComplex Y) _ _).1 hgf)

end Atoms.Homotopical
