import Atoms.ForMathlib.CategoryTheory.Monoidal.Closed.Cartesian
import Atoms.Homotopical.Simplicial.MarkedRightAnodyne

open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory Simplicial
  MorphismProperty Opposite

universe u

namespace Atoms.Homotopical

open MarkedPresheaf (forget)

noncomputable def markedMapOver {S A Y : MarkedSSet.{u}} (a : A ⟶ S) (y : Y ⟶ S) : SSet.{u} :=
  forget.obj (ihomOver a y)

noncomputable def markedMapOverRestrict {S A B Y : MarkedSSet.{u}} (i : A ⟶ B) (b : B ⟶ S)
    (y : Y ⟶ S) : markedMapOver b y ⟶ markedMapOver (i ≫ b) y :=
  forget.map (ihomOverRestrict i b y)

theorem trivialFibration_markedMapOverRestrict {S A B Y : MarkedSSet.{u}} {i : A ⟶ B}
    (hi : markedRightAnodyne i) (b : B ⟶ S) {y : Y ⟶ S} (hy : markedRightFibrations y) :
    SSet.modelCategoryQuillen.I.rlp (markedMapOverRestrict i b y) := by
  rintro _ _ _ ⟨n⟩
  let j := (MarkedPresheaf.flat edgeMarking).map (∂Δ[n] : (Δ[n] : SSet.{u}).Subcomplex).ι
  have : Mono j := (MarkedPresheaf.mono_iff _).2
    (inferInstanceAs (Mono (∂Δ[n] : (Δ[n] : SSet.{u}).Subcomplex).ι))
  refine ((MarkedPresheaf.flatForgetAdjunction edgeMarking).hasLiftingProperty_iff _
    (ihomOverRestrict i b y)).1 ?_
  refine MorphismProperty.of_isPullback (P := (MorphismProperty.ofHoms fun _ : Unit => j).rlp)
    (isPullback_ihomOverRestrict i b y) ?_ _ (.mk ())
  rintro _ _ _ ⟨⟩
  refine (internalHomAdjunction₂.hasLiftingProperty_iff
    (Functor.PushoutObjObj.ofHasPushout (curriedTensor MarkedSSet.{u}) i j)
    (Functor.PullbackObjObj.ofHasPullback internalHom i y)).1 ?_
  have := markedRightAnodyne_pushoutProduct i hi j
  rw [markedRightAnodyne_eq_llp] at this
  exact this _ hy

noncomputable def markedMapOverSimplexEquiv {S A Y : MarkedSSet.{u}} (a : A ⟶ S) (y : Y ⟶ S)
    (n : ℕ) :
    (markedMapOver a y) _⦋n⦌ ≃
      {f : A ⊗ (MarkedPresheaf.flat edgeMarking).obj Δ[n] ⟶ Y // f ≫ y = fst _ _ ≫ a} :=
  SSet.yonedaEquiv.symm.trans
    ((((MarkedPresheaf.flatForgetAdjunction edgeMarking).homEquiv _ _).symm).trans
      (ihomOverHomEquiv a y _))

private noncomputable def isTerminalSharpStdSimplexZero :
    IsTerminal ((MarkedPresheaf.sharp edgeMarking).obj (Δ[0] : SSet.{u})) :=
  IsTerminal.ofUniqueHom
    (fun _ => (MarkedPresheaf.forgetSharpAdjunction edgeMarking).homEquiv _ _
      (SSet.stdSimplex.isTerminalObj₀.from _))
    fun _ _ => MarkedPresheaf.hom_ext (SSet.stdSimplex.isTerminalObj₀.hom_ext _ _)

noncomputable def markedMapOverVertexIso {C : SSet.{u}} {Y : MarkedSSet.{u}} (c : C _⦋0⦌)
    (y : Y ⟶ (MarkedPresheaf.sharp edgeMarking).obj C) :
    markedMapOver ((MarkedPresheaf.sharp edgeMarking).map (SSet.yonedaEquiv.symm c)) y ≅
      pullback (forget.map y) (SSet.yonedaEquiv.symm c : Δ[0] ⟶ C) :=
  let hT := isTerminalSharpStdSimplexZero.{u}
  IsPullback.isoPullback (IsPullback.of_iso
    (fst' := forget.map (pullback.fst _ _ ≫ (ihomTerminalIso hT Y).hom))
    (snd' := SSet.stdSimplex.isTerminalObj₀.from _)
    ((IsPullback.of_hasPullback _ _).map forget) (Iso.refl _)
    (forget.mapIso (ihomTerminalIso hT Y))
    ((isTerminalTensorUnit.isTerminalObj forget).uniqueUpToIso SSet.stdSimplex.isTerminalObj₀)
    (forget.mapIso (ihomTerminalIso hT _))
    ((forget.map_comp _ _).symm.trans (Category.id_comp _).symm)
    (SSet.stdSimplex.isTerminalObj₀.hom_ext _ _)
    ((forget.map_comp _ _).symm.trans ((congrArg forget.map
      (ihom_map_comp_ihomTerminalIso_hom hT y)).trans (forget.map_comp _ _)))
    ((forget.map_comp _ _).symm.trans ((congrArg forget.map
      ((curry_comp_ihomTerminalIso_hom hT _).trans (lift_fst_assoc _ _ _))).trans
        ((forget.map_comp _ _).trans
          (congrArg (· ≫ _) (SSet.stdSimplex.isTerminalObj₀.hom_ext _ _))))))

end Atoms.Homotopical
