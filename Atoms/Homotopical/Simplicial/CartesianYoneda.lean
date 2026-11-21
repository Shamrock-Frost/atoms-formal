import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.FinalObject
import Atoms.Homotopical.Simplicial.CartesianOver
import Atoms.Homotopical.Simplicial.MarkedMapOver

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Simplicial MorphismProperty

universe u

namespace Atoms.Homotopical

theorem markedRightAnodyne_sharp_sliceId (C : SSet.{u}) (c : C _⦋0⦌) :
    markedRightAnodyne ((MarkedPresheaf.sharp edgeMarking).map
      (SSet.yonedaEquiv.symm (SSet.sliceId C c) : Δ[0] ⟶ SSet.sliceAt C c)) :=
  markedRightAnodyne_sharp_map (SSet.rightAnodyneExtensions_sliceId C c)

end Atoms.Homotopical

namespace SSet

open Atoms.Homotopical
open MarkedPresheaf (forget)

theorem isCartesianEdge_sliceAtπ (C : SSet.{u}) [C.Quasicategory] (c : C _⦋0⦌)
    (e : Δ[1] ⟶ sliceAt C c) : IsCartesianEdge (sliceAtπ C c) e :=
  ((rightFibrations_iff_isCartesianFibration_and_forall _).1 (rightFibrations_sliceAtπ C c)).2 e

noncomputable abbrev cartesianFunOver {X C : SSet.{u}} (p : X ⟶ C) [IsCartesianFibration p]
    (c : C _⦋0⦌) : SSet.{u} :=
  markedMapOver ((MarkedPresheaf.sharp edgeMarking).map (sliceAtπ C c))
    (MarkedSSet.cartesianNaturalHom p)

private noncomputable def isTerminalFlatStdSimplexZero :
    IsTerminal ((MarkedPresheaf.flat edgeMarking).obj (Δ[0] : SSet.{u})) :=
  IsTerminal.ofUniqueHom
    (fun _ => edgeHomMk (stdSimplex.isTerminalObj₀.from _) fun e _ =>
      MarkedSSet.mem_marked_of_eq
        (yonedaEquiv.symm.injective (stdSimplex.isTerminalObj₀.hom_ext _ _))
        (MarkedSSet.map_σ_mem_marked ((MarkedPresheaf.flat edgeMarking).obj Δ[0])
          (Δ[0].δ 0 ((stdSimplex.isTerminalObj₀.from _).app _ e))))
    fun _ _ => MarkedPresheaf.hom_ext (stdSimplex.isTerminalObj₀.hom_ext _ _)

private noncomputable def sharpCartesianNaturalEquiv {X K S : SSet.{u}} (p : X ⟶ S)
    [IsCartesianFibration p] (q : K ⟶ S) :
    {g : (MarkedPresheaf.sharp edgeMarking).obj K ⟶ MarkedSSet.cartesianNatural p //
      g ≫ MarkedSSet.cartesianNaturalHom p = (MarkedPresheaf.sharp edgeMarking).map q} ≃
      {f : K ⟶ X // f ≫ p = q ∧ ∀ e : Δ[1] ⟶ K, IsCartesianEdge p (e ≫ f)} where
  toFun g := ⟨forget.map g.1, (forget.map_comp _ _).symm.trans (congrArg forget.map g.2),
    fun e => (congrArg (IsCartesianEdge p) ((congrArg yonedaEquiv.symm
      (yonedaEquiv_comp e (forget.map g.1)).symm).trans (Equiv.symm_apply_apply _ _))).mp
        ((MarkedSSet.mem_marked_ofEdges _ _ _ _).1 (MarkedPresheaf.map_mem_marked g.1
          ((MarkedPresheaf.mem_marked_sharp _ _ _ (yonedaEquiv e)).2 rfl)))⟩
  invFun f := ⟨edgeHomMk f.1 fun e _ => (MarkedSSet.mem_marked_ofEdges _ _ _ _).2
      ((congrArg (IsCartesianEdge p) (yonedaEquiv_symm_comp e f.1)).mp (f.2.2 _)),
    MarkedPresheaf.hom_ext f.2.1⟩
  left_inv _ := Subtype.ext (MarkedPresheaf.hom_ext rfl)
  right_inv _ := Subtype.ext rfl

noncomputable def cartesianFunOverVertexEquiv {X C : SSet.{u}} (p : X ⟶ C)
    [IsCartesianFibration p] (c : C _⦋0⦌) :
    (cartesianFunOver p c) _⦋0⦌ ≃
      {f : sliceAt C c ⟶ X // f ≫ p = sliceAtπ C c ∧
        ∀ e : Δ[1] ⟶ sliceAt C c, IsCartesianEdge p (e ≫ f)} :=
  (markedMapOverSimplexEquiv _ _ 0).trans
    ((tensorTerminalEquiv isTerminalFlatStdSimplexZero.{u} _ _).trans
      (sharpCartesianNaturalEquiv p (sliceAtπ C c)))

noncomputable def cartesianYonedaEval {X C : SSet.{u}} (p : X ⟶ C) [IsCartesianFibration p]
    (c : C _⦋0⦌) : cartesianFunOver p c ⟶ pullback p (yonedaEquiv.symm c : Δ[0] ⟶ C) :=
  markedMapOverRestrict ((MarkedPresheaf.sharp edgeMarking).map (yonedaEquiv.symm (sliceId C c)))
      ((MarkedPresheaf.sharp edgeMarking).map (sliceAtπ C c)) (MarkedSSet.cartesianNaturalHom p) ≫
    eqToHom (by rw [← Functor.map_comp, sliceId_comp_sliceAtπ]) ≫
    (markedMapOverVertexIso c (MarkedSSet.cartesianNaturalHom p)).hom

theorem trivialFibration_cartesianYoneda {X C : SSet.{u}} (p : X ⟶ C) [IsCartesianFibration p]
    (c : C _⦋0⦌) : modelCategoryQuillen.I.rlp (cartesianYonedaEval p c) :=
  modelCategoryQuillen.I.rlp.comp_mem _ _
    (trivialFibration_markedMapOverRestrict (markedRightAnodyne_sharp_sliceId C c) _
      (markedRightFibrations_cartesianNaturalHom p))
    (modelCategoryQuillen.I.rlp.comp_mem _ _ (MorphismProperty.rlp_of_isIso _ _)
      (MorphismProperty.rlp_of_isIso _
        (markedMapOverVertexIso c (MarkedSSet.cartesianNaturalHom p)).hom))

end SSet
