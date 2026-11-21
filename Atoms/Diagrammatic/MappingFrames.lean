import Atoms.Diagrammatic.Joyal.GrayHomFaceNerve
import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.UnderFrame
import Atoms.Homotopical.Simplicial.Frame

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open Atoms.Homotopical
open Atoms.Homotopical.MarkedSSet.modelCategoryCartesian

universe u

namespace Atoms.Diagrammatic

local instance : HasLimits (DiagSet.Infty.{u} 1) :=
  inferInstanceAs (HasLimits DiagSet.{u})

noncomputable def faceNerveRightSimplicialFrameUnder (S : DiagSet.Infty.{u} 1)
    (C : MarkedSSet.{u}) [IsFibrant C] (f : faceNerve.{u}.obj S ⟶ C) :
    SimplicialFrame ((Under.post (faceNerveRight : MarkedSSet.{u} ⥤ DiagSet.Infty.{u} 1) ⋙
      Under.map (T := DiagSet.Infty.{u} 1) (faceNerveAdjunction.{u}.unit.app S)).obj
      (Under.mk f)) := by
  exact (isQuillen_postAdjunctionLeft isQuillen_faceNerveAdjunction.{u} S).mapSimplicialFrame
    ((markedSimplicialFrame C).under f)

theorem exists_framed_replacement_under (S : DiagSet.Infty.{u} 1) [IsCofibrant S]
    (X : Under S) [IsCofibrant X] :
    ∃ (Z : Under S) (_ : SimplicialFrame Z) (η : X ⟶ Z), WeakEquivalence η := by
  let F : DiagSet.Infty.{u} 1 ⥤ MarkedSSet.{u} :=
    DiagSet.Infty.flat 1 ⋙ MarkedDiagSet.Coinductive.markedFaceNerve
  let adj := Under.postAdjunctionLeft (X := S) faceNerveAdjunction.{u}
  let φ := MorphismProperty.factorizationData
    (trivialCofibrations (Under (F.obj S))) (fibrations _)
    (terminal.from ((Under.post F).obj X))
  have : IsFibrant φ.Z := by
    rw [HomotopicalAlgebra.isFibrant_iff, Subsingleton.elim (terminal.from φ.Z) φ.p]
    exact (fibration_iff _).2 φ.hp
  have : IsFibrant φ.Z.right := (isFibrant_under_iff _ φ.Z).1 inferInstance
  have hi : WeakEquivalence φ.i := (weakEquivalence_iff _).2 φ.hi.2
  let q := isQuillenEquivalence_postAdjunctionLeft
    isQuillenEquivalence_faceNerveAdjunction.{u} S
  have hη := (@q.weakEquivalence_iff X φ.Z ‹IsCofibrant X› ‹IsFibrant φ.Z› φ.i).1 hi
  exact ⟨_, faceNerveRightSimplicialFrameUnder S φ.Z.right φ.Z.hom,
    adj.homEquiv X φ.Z φ.i, hη⟩

noncomputable def faceNerveRightSimplicialFrameUnderMap (S : DiagSet.Infty.{u} 1)
    {C C' : MarkedSSet.{u}} [IsFibrant C] [IsFibrant C'] {f : faceNerve.{u}.obj S ⟶ C}
    {f' : faceNerve.{u}.obj S ⟶ C'} (c : C ⟶ C') (h : f ≫ c = f') :
    (faceNerveRightSimplicialFrameUnder S C f).obj ⟶
      (faceNerveRightSimplicialFrameUnder S C' f').obj :=
  Functor.whiskerRight ((markedSimplicialFrame C).underMap (markedSimplicialFrame C')
      (markedPowerSimplicialObjectMap c) (markedPowerSimplicialObjectMap_app_zero c) h)
    (Under.post (faceNerveRight : MarkedSSet.{u} ⥤ DiagSet.Infty.{u} 1) ⋙
      Under.map (T := DiagSet.Infty.{u} 1) (faceNerveAdjunction.{u}.unit.app S))

theorem faceNerveRightSimplicialFrameUnderMap_app_zero (S : DiagSet.Infty.{u} 1)
    {C C' : MarkedSSet.{u}} [IsFibrant C] [IsFibrant C'] {f : faceNerve.{u}.obj S ⟶ C}
    {f' : faceNerve.{u}.obj S ⟶ C'} (c : C ⟶ C') (h : f ≫ c = f') :
    (faceNerveRightSimplicialFrameUnderMap S c h).app (op ⦋0⦌) ≫
        (faceNerveRightSimplicialFrameUnder S C' f').iso.hom =
      (faceNerveRightSimplicialFrameUnder S C f).iso.hom ≫
        (Under.post (faceNerveRight : MarkedSSet.{u} ⥤ DiagSet.Infty.{u} 1) ⋙
          Under.map (T := DiagSet.Infty.{u} 1) (faceNerveAdjunction.{u}.unit.app S)).map
          (Under.homMk (U := Under.mk f) (V := Under.mk f') c h) := by
  let R := Under.post (faceNerveRight : MarkedSSet.{u} ⥤ DiagSet.Infty.{u} 1) ⋙
    Under.map (T := DiagSet.Infty.{u} 1) (faceNerveAdjunction.{u}.unit.app S)
  change R.map _ ≫ R.map _ = R.map _ ≫ R.map _
  exact ((R.map_comp _ _).symm.trans (congrArg R.map
    ((markedSimplicialFrame C).underMap_app_zero (markedSimplicialFrame C')
      (markedPowerSimplicialObjectMap c) (markedPowerSimplicialObjectMap_app_zero c) h))).trans
    (R.map_comp _ _)

theorem exists_framed_replacement_under_map (S : DiagSet.Infty.{u} 1) [IsCofibrant S]
    {X X' : Under S} [IsCofibrant X] [IsCofibrant X'] (q : X ⟶ X') :
    ∃ (Z Z' : Under S) (Y : SimplicialFrame Z) (Y' : SimplicialFrame Z') (η : X ⟶ Z)
      (η' : X' ⟶ Z') (ζ : Z ⟶ Z') (ψ : Y.obj ⟶ Y'.obj), WeakEquivalence η ∧ WeakEquivalence η' ∧
        η ≫ ζ = q ≫ η' ∧ ψ.app (op ⦋0⦌) ≫ Y'.iso.hom = Y.iso.hom ≫ ζ := by
  let F : DiagSet.Infty.{u} 1 ⥤ MarkedSSet.{u} :=
    DiagSet.Infty.flat 1 ⋙ MarkedDiagSet.Coinductive.markedFaceNerve
  let adj := Under.postAdjunctionLeft (X := S) faceNerveAdjunction.{u}
  let φ := MorphismProperty.factorizationData
    (trivialCofibrations (Under (F.obj S))) (fibrations _)
    (terminal.from ((Under.post F).obj X))
  let φ' := MorphismProperty.factorizationData
    (trivialCofibrations (Under (F.obj S))) (fibrations _)
    (terminal.from ((Under.post F).obj X'))
  have hZ : IsFibrant φ.Z := by
    rw [HomotopicalAlgebra.isFibrant_iff, Subsingleton.elim (terminal.from φ.Z) φ.p]
    exact (fibration_iff _).2 φ.hp
  have hZ' : IsFibrant φ'.Z := by
    rw [HomotopicalAlgebra.isFibrant_iff, Subsingleton.elim (terminal.from φ'.Z) φ'.p]
    exact (fibration_iff _).2 φ'.hp
  have : IsFibrant φ.Z.right := (isFibrant_under_iff _ φ.Z).1 inferInstance
  have : IsFibrant φ'.Z.right := (isFibrant_under_iff _ φ'.Z).1 inferInstance
  have hi : WeakEquivalence φ.i := (weakEquivalence_iff _).2 φ.hi.2
  have hi' : WeakEquivalence φ'.i := (weakEquivalence_iff _).2 φ'.hi.2
  have hic : Cofibration φ.i := (cofibration_iff _).2 φ.hi.1
  let q' := isQuillenEquivalence_postAdjunctionLeft
    isQuillenEquivalence_faceNerveAdjunction.{u} S
  have hη := (@q'.weakEquivalence_iff X φ.Z ‹IsCofibrant X› hZ φ.i).1 hi
  have hη' := (@q'.weakEquivalence_iff X' φ'.Z ‹IsCofibrant X'› hZ' φ'.i).1 hi'
  have sq : CommSq ((Under.post F).map q ≫ φ'.i) φ.i (terminal.from φ'.Z) (terminal.from φ.Z) :=
    ⟨Subsingleton.elim _ _⟩
  have : Fibration (terminal.from φ'.Z) := (HomotopicalAlgebra.isFibrant_iff _).1 hZ'
  let c := sq.lift
  have hc : φ.i ≫ c = (Under.post F).map q ≫ φ'.i := sq.fac_left
  refine ⟨_, _, faceNerveRightSimplicialFrameUnder S φ.Z.right φ.Z.hom,
    faceNerveRightSimplicialFrameUnder S φ'.Z.right φ'.Z.hom,
    adj.homEquiv X φ.Z φ.i, adj.homEquiv X' φ'.Z φ'.i, _,
    faceNerveRightSimplicialFrameUnderMap S c.right (Under.w c), hη, hη', ?_,
    faceNerveRightSimplicialFrameUnderMap_app_zero S c.right (Under.w c)⟩
  exact ((adj.homEquiv_naturality_right φ.i c).symm.trans (congrArg _ hc)).trans
    (adj.homEquiv_naturality_left q φ'.i)

end Atoms.Diagrammatic
