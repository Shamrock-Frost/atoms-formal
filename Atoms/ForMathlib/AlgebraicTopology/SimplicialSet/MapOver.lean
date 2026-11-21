import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.RightPushoutProduct
import Atoms.ForMathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Atoms.ForMathlib.CategoryTheory.Monoidal.Closed.Cartesian

open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory Simplicial
  MorphismProperty HomotopicalAlgebra Opposite

universe u

namespace SSet

noncomputable abbrev mapOver {C F G : SSet.{u}} (pF : F ⟶ C) (pG : G ⟶ C) : SSet.{u} :=
  ihomOver pF pG

noncomputable abbrev mapOverRestrict {C F F' G : SSet.{u}} (i : F ⟶ F') (pF' : F' ⟶ C)
    (pG : G ⟶ C) : mapOver pF' pG ⟶ mapOver (i ≫ pF') pG :=
  ihomOverRestrict i pF' pG

theorem trivialFibration_mapOverRestrict {C F F' G : SSet.{u}} {i : F ⟶ F'}
    (hi : rightAnodyneExtensions i) (pF' : F' ⟶ C) {pG : G ⟶ C} (hp : rightFibrations pG) :
    modelCategoryQuillen.I.rlp (mapOverRestrict i pF' pG) := by
  refine MorphismProperty.of_isPullback (isPullback_ihomOverRestrict i pF' pG)
    (?_ : modelCategoryQuillen.I.rlp (Functor.PullbackObjObj.ofHasPullback internalHom i pG).π)
  rintro _ _ _ ⟨n⟩
  exact (internalHomAdjunction₂.hasLiftingProperty_iff
    (Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet) i ∂Δ[n].ι)
    (Functor.PullbackObjObj.ofHasPullback internalHom i pG)).1
    (rightAnodyneExtensions_pushoutObjObjι_left _ hi _ hp)

noncomputable def ihomStdSimplexZeroIso (X : SSet.{u}) : (ihom Δ[0]).obj X ≅ X :=
  ihomTerminalIso stdSimplex.isTerminalObj₀ X

noncomputable def mapOverVertexIso {C G : SSet.{u}} (c : C _⦋0⦌) (pG : G ⟶ C) :
    mapOver (yonedaEquiv.symm c : Δ[0] ⟶ C) pG ≅ pullback pG (yonedaEquiv.symm c : Δ[0] ⟶ C) :=
  IsPullback.isoPullback (IsPullback.of_iso
    (fst' := pullback.fst _ _ ≫ (ihomStdSimplexZeroIso G).hom)
    (snd' := pullback.snd _ _ ≫ stdSimplex.isTerminalObj₀.from (𝟙_ SSet.{u}))
    (IsPullback.of_hasPullback _ _) (Iso.refl _) (ihomStdSimplexZeroIso G)
    (isTerminalTensorUnit.uniqueUpToIso stdSimplex.isTerminalObj₀) (ihomStdSimplexZeroIso C)
    (Category.id_comp _).symm (Category.id_comp _).symm
    (ihom_map_comp_ihomTerminalIso_hom _ pG)
    (by
      refine (curry_comp_ihomTerminalIso_hom _ _).trans ?_
      rw [lift_fst_assoc]
      exact congrArg (· ≫ _) (stdSimplex.isTerminalObj₀.hom_ext _ _)))

noncomputable def mapOverVertexEquiv {C F G : SSet.{u}} (pF : F ⟶ C) (pG : G ⟶ C) :
    (mapOver pF pG) _⦋0⦌ ≃ {f : F ⟶ G // f ≫ pG = pF} :=
  yonedaEquiv.symm.trans ((ihomOverHomEquiv pF pG Δ[0]).trans
    (tensorTerminalEquiv stdSimplex.isTerminalObj₀ pF pG))

theorem mapOverVertexEquiv_mapOverRestrict {C F F' G : SSet.{u}} (i : F ⟶ F') (pF' : F' ⟶ C)
    (pG : G ⟶ C) (v : (mapOver pF' pG) _⦋0⦌) :
    (mapOverVertexEquiv (i ≫ pF') pG ((mapOverRestrict i pF' pG).app _ v)).1 =
      i ≫ (mapOverVertexEquiv pF' pG v).1 := by
  simp only [mapOverVertexEquiv, Equiv.trans_apply, ihomOverHomEquiv, tensorTerminalEquiv,
    Equiv.coe_fn_mk]
  rw [← yonedaEquiv_symm_comp, Category.assoc, ihomOverRestrict_fst, ← Category.assoc,
    uncurry_pre_app, ← Category.assoc, ← Category.assoc]
  refine congrArg (· ≫ _) ?_
  ext1
  · simp
  · exact stdSimplex.isTerminalObj₀.hom_ext _ _

end SSet
