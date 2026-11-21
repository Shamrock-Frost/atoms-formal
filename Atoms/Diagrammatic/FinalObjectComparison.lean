import Atoms.Diagrammatic.Fibration.CartesianEdgeComparison
import Atoms.Diagrammatic.FinalObject
import Atoms.Diagrammatic.MappingFrameComparison
import Atoms.Homotopical.Simplicial.JoyalOp

open CategoryTheory Limits Simplicial MorphismProperty HomotopicalAlgebra
open Atoms.Homotopical Atoms.Shape SSet.modelCategoryQuillen

universe u

namespace Atoms.Diagrammatic

variable {X : DiagSet.{u}}

private theorem rlp_I_from_iff_weakEquivalence (K : SSet.{u}) [K.KanComplex] :
    I.rlp (SSet.stdSimplex.isTerminalObj₀.from K) ↔
      WeakEquivalence (SSet.stdSimplex.isTerminalObj₀.from K) := by
  have : Fibration (SSet.stdSimplex.isTerminalObj₀.from K) :=
    (isFibrant_iff_of_isTerminal _ SSet.stdSimplex.isTerminalObj₀).1 inferInstance
  rw [← SSet.rlp_monomorphisms]
  change (cofibrations SSet.{u}).rlp _ ↔ _
  rw [cofibrations_rlp, mem_trivialFibrations_iff]
  exact ⟨fun h => h.2, fun h => ⟨this, h⟩⟩

private theorem rlp_I_from_iff_of_span {K K' Z : SSet.{u}} [K.KanComplex] [K'.KanComplex]
    (l : Z ⟶ K) (r : Z ⟶ K') [WeakEquivalence l] [WeakEquivalence r] :
    I.rlp (SSet.stdSimplex.isTerminalObj₀.from K) ↔
      I.rlp (SSet.stdSimplex.isTerminalObj₀.from K') := by
  rw [rlp_I_from_iff_weakEquivalence, rlp_I_from_iff_weakEquivalence]
  have hl : l ≫ SSet.stdSimplex.isTerminalObj₀.from K = SSet.stdSimplex.isTerminalObj₀.from Z :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  have hr : r ≫ SSet.stdSimplex.isTerminalObj₀.from K' = SSet.stdSimplex.isTerminalObj₀.from Z :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have : WeakEquivalence (r ≫ SSet.stdSimplex.isTerminalObj₀.from K') := by
      rw [hr, ← hl]
      infer_instance
    exact weakEquivalence_of_precomp r _
  · have : WeakEquivalence (l ≫ SSet.stdSimplex.isTerminalObj₀.from K) := by
      rw [hl, ← hr]
      infer_instance
    exact weakEquivalence_of_precomp l _

private theorem rlp_I_from_toSSet_obj_iff (G : DiagSet.{u}) :
    I.rlp (SSet.stdSimplex.isTerminalObj₀.from (DiagSet.toSSet.obj G)) ↔
      I.rlp (DiagSet.toSSet.map (isTerminalBallAtomPoint.from G)) := by
  have hT : IsTerminal (DiagSet.toSSet.obj (ball.{u} atomPoint)) :=
    isTerminalBallAtomPoint.isTerminalObj DiagSet.toSSet _
  rw [← (I.rlp).cancel_right_of_respectsIso (DiagSet.toSSet.map (isTerminalBallAtomPoint.from G))
    (hT.uniqueUpToIso SSet.stdSimplex.isTerminalObj₀).hom]
  exact iff_of_eq (congrArg _ (SSet.stdSimplex.isTerminalObj₀.hom_ext _ _))

theorem DiagSet.isContractible_iff_rlp_toSSet {G : DiagSet.{u}} (hG : IsInftyCategory 0 G) :
    G.IsContractible ↔ I.rlp (SSet.stdSimplex.isTerminalObj₀.from (DiagSet.toSSet.obj G)) := by
  rw [rlp_I_from_toSSet_obj_iff]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact rlp_I_toSSet_map_of_rlp_monomorphisms
      (h.rlp_monomorphisms ((isFibrant_infty_iff 0 G).2 hG))
  · have hG₁ : IsFibrant ((DiagSet.toInfty 1).obj G) :=
      (isFibrant_infty_iff 1 G).2 (hG.of_le (by simp))
    have hT : IsTerminal ((DiagSet.toInfty 1).obj (ball.{u} atomPoint)) := isTerminalBallAtomPoint
    have : Fibration ((DiagSet.toInfty 1).map (isTerminalBallAtomPoint.from G)) :=
      (isFibrant_iff_of_isTerminal _ hT).1 hG₁
    have : IsFibrant ((DiagSet.toInfty 1).obj (ball.{u} atomPoint)) :=
      (isFibrant_iff_of_isTerminal (𝟙 _) hT).2 inferInstance
    exact weakEquivalence_toInfty_map_of_rlp_monomorphisms 0
      (rlp_monomorphisms_of_rlp_I_toSSet_map _ h)

theorem DiagSet.isContractible_bipointedHom_iff_mappingSpace (hX : IsInftyCategory 1 X)
    (x y : X.Vertex) :
    (bipointedHom.obj (X.bipoint x y)).IsContractible ↔
      I.rlp (SSet.stdSimplex.isTerminalObj₀.from (SSet.mappingSpace (DiagSet.toSSet.obj X)
        (X.vertexEquivSSet x) (X.vertexEquivSSet y))) := by
  have hG : IsInftyCategory 0 (bipointedHom.obj (X.bipoint x y)) :=
    (isFibrant_infty_iff 0 _).1 (isFibrant_bipointedHom hX)
  have := kanComplex_toSSet_obj hG
  have := kanComplex_mappingSpace_toSSet_obj hX x y
  obtain ⟨Z, l, r, hl, hr⟩ := bipointedHomMappingSpaceComparison_exists hX x y
  exact (DiagSet.isContractible_iff_rlp_toSSet hG).trans (rlp_I_from_iff_of_span l r)

theorem DiagSet.isFinalObject_iff_isFinal (hX : IsInftyCategory 1 X) (t : X.Vertex) :
    X.IsFinalObject t ↔ SSet.IsFinal (X.vertexEquivSSet t) := by
  have : (DiagSet.toSSet.obj X).Quasicategory :=
    quasicategory_toSSet_obj X ((isFibrant_infty_iff 1 X).2 hX)
  rw [SSet.isFinal_iff_mappingSpace]
  exact X.vertexEquivSSet.forall_congr fun x =>
    DiagSet.isContractible_bipointedHom_iff_mappingSpace hX x t

theorem DiagSet.isInitialObject_iff_isInitialObject (hX : IsInftyCategory 1 X) (t : X.Vertex) :
    X.IsInitialObject t ↔ SSet.IsInitialObject (X.vertexEquivSSet t) := by
  have : (DiagSet.toSSet.obj X).Quasicategory :=
    quasicategory_toSSet_obj X ((isFibrant_infty_iff 1 X).2 hX)
  rw [SSet.isInitialObject_iff_mappingSpace]
  exact X.vertexEquivSSet.forall_congr fun x =>
    DiagSet.isContractible_bipointedHom_iff_mappingSpace hX t x

theorem DiagSet.isZeroObject_iff_isZeroObject (hX : IsInftyCategory 1 X) (t : X.Vertex) :
    X.IsZeroObject t ↔ SSet.IsZeroObject (X.vertexEquivSSet t) :=
  Bool.forall_bool.trans (and_comm.trans
    (and_congr (X.isFinalObject_iff_isFinal hX t) (X.isInitialObject_iff_isInitialObject hX t)))

end Atoms.Diagrammatic
