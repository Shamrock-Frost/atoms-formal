import Atoms.Diagrammatic.Fibration.CartesianSquare
import Atoms.Diagrammatic.Marked.GrayTensorEntireLifting

open CategoryTheory Limits Opposite HomotopicalAlgebra Atoms.Homotopical
open Atoms.Shape Atoms.Molecule Atoms.Molecule.OGP

universe u

namespace Atoms.Diagrammatic

attribute [local irreducible] grayTensorBifunctor GrayDiagSet.leftUnitor

private theorem exists_markedIntervalVertex_eq (x : markedTensorUnit.{u} ⟶ markedInterval) :
    ∃ ε, x = markedIntervalVertex ε := by
  let f := uliftYoneda.preimage (MarkedPresheaf.forget.map x ≫ intervalBallIso.inv)
  obtain ⟨ε, hf⟩ := exists_eq_atomGlobeVertex f
  refine ⟨ε, MarkedPresheaf.hom_ext ?_⟩
  have he : MarkedPresheaf.forget.map x ≫ intervalBallIso.inv =
      uliftYoneda.map (atomGlobeVertex ε) :=
    (uliftYoneda.map_preimage _).symm.trans (congrArg uliftYoneda.map hf)
  exact (Iso.comp_inv_eq intervalBallIso).1 he

private theorem mem_marked_app_of_top {Y : MarkedDiagSet.{u}} {U T : Atom}
    (hU : 0 < U.dimension) (q : ball.{u} U ⟶ Y.underlying)
    (hq : uliftYonedaEquiv q ∈ Y.marked U)
    (w : diagram (ball.{u} U) T) (hw : w ∈ (MarkedDiagSet.markedAtom U hU).marked T) :
    q.app (op T) w ∈ Y.marked T := by
  have h := MarkedPresheaf.map_mem_marked (MarkedDiagSet.markedAtomHom U hU _ hq) hw
  rw [MarkedDiagSet.forget_map_markedAtomHom, Equiv.symm_apply_apply] at h
  exact h

private theorem cartesian_leftEdge_of_markedTensor {E S : DiagSet.{u}} (p : E ⟶ S)
    [Fibration ((DiagSet.toInfty 1).map p)] [IsFibrant ((DiagSet.toInfty 1).obj S)]
    (l : grayTensor (ball.{u} (atomGlobe 1)) markedInterval.underlying ⟶ E)
    (r₀ : markedTensor false ((MarkedPresheaf.flat atomMarking).obj
      (ball.{u} (atomGlobe 1))) markedInterval ⟶ DiagSet.cartesianMarked p)
    (hr : MarkedPresheaf.forget.map r₀ = l) (ε : Bool) :
    DiagSet.IsCartesianEdge p (DiagSet.graySquareLeftEdge
      ((grayTensorLeft (ball.{u} (atomGlobe 1))).map intervalBallIso.hom ≫ l) ε) := by
  let σ : grayTensor (ball.{u} (atomGlobe 1)) (ball.{u} (atomGlobe 1)) ⟶ E :=
    (grayTensorLeft (ball.{u} (atomGlobe 1))).map intervalBallIso.hom ≫ l
  let xv : markedTensorUnit.{u} ⟶ (MarkedPresheaf.flat atomMarking).obj
      (ball.{u} (atomGlobe 1)) := (MarkedPresheaf.flat atomMarking).map
        (uliftYoneda.map (atomGlobeVertex ε))
  let r : markedInterval.{u} ⟶ DiagSet.cartesianMarked p :=
    (markedTensorLeftUnitor false markedInterval).inv ≫
      markedTensorMap false xv (𝟙 markedInterval) ≫ r₀
  have he : uliftYonedaEquiv (intervalBallIso.hom ≫ MarkedPresheaf.forget.map r) =
      (DiagSet.graySquareLeftEdge σ ε).cell := by
    have hx : MarkedPresheaf.forget.map xv =
        uliftYoneda.map (atomGlobeVertex ε) := rfl
    simp only [r, Functor.map_comp, forget_map_markedTensorLeftUnitor_inv,
      forget_map_markedTensorMap, hx, hr]
    rw [DiagSet.graySquareLeftEdge_cell_eq]
    dsimp only [σ]
    simp only [grayTensorLeft_map_eq, grayTensorRight_map_eq]
    rw [grayTensor_leftSide_map_assoc, Category.comp_id]
    rfl
  apply (DiagSet.mem_marked_cartesianMarked_edge_iff p _).1
  rw [← he]
  exact MarkedPresheaf.map_mem_marked r intervalBallIso_top_mem_marked

private theorem cartesian_rightEdge_of_marked {E S : DiagSet.{u}} (p : E ⟶ S)
    [Fibration ((DiagSet.toInfty 1).map p)] [IsFibrant ((DiagSet.toInfty 1).obj S)]
    (l : grayTensor (ball.{u} (atomGlobe 1)) markedInterval.underlying ⟶ E)
    (r : MarkedDiagSet.markedAtom (atomGlobe 1) (by rw [dimension_atomGlobe]; omega) ⟶
      DiagSet.cartesianMarked p)
    (hr : MarkedPresheaf.forget.map r =
      (GrayDiagSet.rightUnitor (ball.{u} (atomGlobe 1))).inv ≫
        (grayTensorLeft (ball.{u} (atomGlobe 1))).map
          (MarkedPresheaf.forget.map (markedIntervalVertex true)) ≫ l) :
    DiagSet.IsCartesianEdge p (DiagSet.graySquareRightEdge
      ((grayTensorLeft (ball.{u} (atomGlobe 1))).map intervalBallIso.hom ≫ l) true) := by
  let σ : grayTensor (ball.{u} (atomGlobe 1)) (ball.{u} (atomGlobe 1)) ⟶ E :=
    (grayTensorLeft (ball.{u} (atomGlobe 1))).map intervalBallIso.hom ≫ l
  have he : uliftYonedaEquiv (MarkedPresheaf.forget.map r) =
      (DiagSet.graySquareRightEdge σ true).cell := by
    rw [hr, forget_map_markedIntervalVertex]
    rw [DiagSet.graySquareRightEdge_cell_eq]
    dsimp only [σ]
    rw [← Functor.map_comp_assoc]
    rfl
  apply (DiagSet.mem_marked_cartesianMarked_edge_iff p _).1
  rw [← he]
  exact MarkedPresheaf.map_mem_marked r
    ((MarkedPresheaf.mem_marked_ofMarking _ _ _ _).2 (Or.inr (IsIso.id _)))

theorem DiagSet.hasLiftingProperty_pushoutProduct_markingInclusion_arrow {E S : DiagSet.{u}}
    (p : E ⟶ S) [Fibration ((DiagSet.toInfty 1).map p)]
    [IsFibrant ((DiagSet.toInfty 1).obj S)] :
    HasLiftingProperty (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} false))
      (MarkedDiagSet.markingInclusion (atomGlobe 1) (by rw [dimension_atomGlobe]; omega))
      (markedIntervalVertex true)).ι (DiagSet.cartesianMarkedHom p) := by
  let a := MarkedDiagSet.markingInclusion.{u} (atomGlobe 1) (by rw [dimension_atomGlobe]; omega)
  let B := MarkedDiagSet.markedAtom.{u} (atomGlobe 1) (by rw [dimension_atomGlobe]; omega)
  let sq := Functor.PushoutObjObj.ofHasPushout
    (Functor.curry.obj (markedTensorBifunctor.{u} false)) a (markedIntervalVertex.{u} true)
  change HasLiftingProperty sq.ι (DiagSet.cartesianMarkedHom p)
  have : IsIso (MarkedPresheaf.forget.map sq.ι) := isIso_forget_map_pushoutProduct_left a _
  refine hasLiftingProperty_of_isIso_forget_of_mem_marked sq.ι (DiagSet.cartesianMarkedHom p) ?_
  intro u v csq l₀ hl₀ hly₀ T z hz
  have hleg {W : MarkedDiagSet.{u}} (j : W ⟶ sq.pt) :
      MarkedPresheaf.forget.map j ≫ MarkedPresheaf.forget.map u =
        MarkedPresheaf.forget.map (j ≫ sq.ι) ≫ l₀ :=
    (congrArg (MarkedPresheaf.forget.map j ≫ ·) hl₀.symm).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ l₀) (MarkedPresheaf.forget.map_comp _ _).symm))
  have hr₀ : MarkedPresheaf.forget.map sq.inr ≫ MarkedPresheaf.forget.map u =
      MarkedPresheaf.forget.map (markedTensorMap false a (𝟙 markedInterval)) ≫ l₀ :=
    (hleg sq.inr).trans (congrArg (MarkedPresheaf.forget.map · ≫ l₀) sq.inr_ι)
  have hi₀ : MarkedPresheaf.forget.map sq.inl ≫ MarkedPresheaf.forget.map u =
      MarkedPresheaf.forget.map (markedTensorMap false (𝟙 B) (markedIntervalVertex true)) ≫
        l₀ :=
    (hleg sq.inl).trans (congrArg (MarkedPresheaf.forget.map · ≫ l₀) sq.inl_ι)
  let l : grayTensor (ball.{u} (atomGlobe 1)) markedInterval.underlying ⟶ E := l₀
  have hl : MarkedPresheaf.forget.map sq.ι ≫ l = MarkedPresheaf.forget.map u := hl₀
  have hr : MarkedPresheaf.forget.map sq.inr ≫ MarkedPresheaf.forget.map u = l := by
    refine hr₀.trans ?_
    change grayTensorBifunctor.map (𝟙 _, 𝟙 _) ≫ l = l
    have hid : (𝟙 (ball.{u} (atomGlobe 1)), 𝟙 markedInterval.underlying) =
        𝟙 (ball.{u} (atomGlobe 1), markedInterval.underlying) := rfl
    rw [hid, grayTensorBifunctor.map_id, Category.id_comp]
  have hi : MarkedPresheaf.forget.map sq.inl ≫ MarkedPresheaf.forget.map u =
      (grayTensorLeft (ball.{u} (atomGlobe 1))).map
        (MarkedPresheaf.forget.map (markedIntervalVertex true)) ≫ l := hi₀
  let σ : grayTensor (ball.{u} (atomGlobe 1)) (ball.{u} (atomGlobe 1)) ⟶ E :=
    (grayTensorLeft (ball.{u} (atomGlobe 1))).map intervalBallIso.hom ≫ l
  have hleft (ε : Bool) := cartesian_leftEdge_of_markedTensor p l (sq.inr ≫ u)
    ((Functor.map_comp _ _ _).trans hr) ε
  have hright := cartesian_rightEdge_of_marked p l
    ((markedTensorRightUnitor false B).inv ≫ sq.inl ≫ u) (by
      simp only [Functor.map_comp]
      exact congrArg ((GrayDiagSet.rightUnitor (ball.{u} (atomGlobe 1))).inv ≫ ·) hi)
  have hzero := DiagSet.IsCartesianEdge.of_graySquare σ (hleft false) (hleft true) hright
  apply mem_marked_of_pushoutProduct_left a sq u l hl
    (fun T z hT _ ↦ (DiagSet.mem_marked_cartesianMarked p T _).2 (Or.inr (Or.inl hT)))
    (fun xv T w hw ↦ ?_) z hz
  obtain ⟨ε, rfl⟩ := exists_markedIntervalVertex_eq xv
  let q : ball.{u} (atomGlobe 1) ⟶ E :=
    MarkedPresheaf.forget.map ((markedTensorRightUnitor false B).inv ≫
      markedTensorMap false (𝟙 B) (markedIntervalVertex ε)) ≫ l
  change q.app (op T) w ∈ _
  apply mem_marked_app_of_top (Y := DiagSet.cartesianMarked p)
    (by rw [dimension_atomGlobe]; omega) q _ w hw
  have he : uliftYonedaEquiv
      (MarkedPresheaf.forget.map ((markedTensorRightUnitor false B).inv ≫
        markedTensorMap false (𝟙 B) (markedIntervalVertex ε)) ≫ l) =
        (DiagSet.graySquareRightEdge σ ε).cell := by
    simp only [Functor.map_comp, forget_map_markedTensorRightUnitor_inv,
      forget_map_markedTensorMap, forget_map_markedIntervalVertex]
    rw [DiagSet.graySquareRightEdge_cell_eq]
    dsimp only [σ]
    rw [← Functor.map_comp_assoc]
    rfl
  exact he.symm ▸ (DiagSet.mem_marked_cartesianMarked_edge_iff p _).2
    (Bool.rec hzero hright ε)

noncomputable def MarkedDiagSet.markingInclusionIsoOfIso {U V : Atom}
    (i : U ≅ V) (hU : 0 < U.dimension) (hV : 0 < V.dimension) :
    Arrow.mk (MarkedDiagSet.markingInclusion.{u} U hU) ≅
      Arrow.mk (MarkedDiagSet.markingInclusion.{u} V hV) := by
  let e := uliftYoneda.{u}.mapIso i
  let m : MarkedDiagSet.markedAtom.{u} U hU ≅ MarkedDiagSet.markedAtom.{u} V hV :=
    markedIsoMk e fun T x ↦ by
      refine (MarkedPresheaf.mem_marked_ofMarking _ _ _ _).trans
        (Iff.trans ?_ (MarkedPresheaf.mem_marked_ofMarking _ _ _ _).symm)
      refine or_congr ⟨isDegenerate_app e.hom, isDegenerate_of_isDegenerate_app e.hom⟩ ?_
      change IsIso (x.down : T ⟶ U) ↔ IsIso ((x.down : T ⟶ U) ≫ i.hom)
      exact (isIso_comp_right_iff _ i.hom).symm
  exact Arrow.isoMk ((MarkedPresheaf.flat atomMarking).mapIso e) m
    (MarkedPresheaf.hom_ext (by simp only [Functor.map_comp]; exact
      (Category.id_comp e.hom).trans (Category.comp_id e.hom).symm))

theorem DiagSet.hasLiftingProperty_pushoutProduct_markingInclusion_dimension_one
    {E S : DiagSet.{u}} (p : E ⟶ S) [Fibration ((DiagSet.toInfty 1).map p)]
    [IsFibrant ((DiagSet.toInfty 1).obj S)] (U : Atom) (hU : U.dimension = 1) :
    HasLiftingProperty (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} false))
      (MarkedDiagSet.markingInclusion U (by omega)) (markedIntervalVertex true)).ι
      (DiagSet.cartesianMarkedHom p) := by
  obtain ⟨i⟩ := nonempty_iso_atomGlobe_of_dimension_eq_one hU
  let e := MarkedDiagSet.markingInclusionIsoOfIso.{u} i
    (by rw [dimension_atomGlobe]; omega) (by omega)
  let b := Functor.PushoutObjObj.ι_iso_of_iso_left
    (f₂ := Arrow.mk (markedIntervalVertex.{u} true))
    (Functor.PushoutObjObj.ofHasPushout (Functor.curry.obj (markedTensorBifunctor.{u} false)) _ _)
    (Functor.PushoutObjObj.ofHasPushout _ _ _) e
  have h : HasLiftingProperty (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} false))
      (MarkedDiagSet.markingInclusion (atomGlobe 1) (by rw [dimension_atomGlobe]; omega))
      (markedIntervalVertex.{u} true)).ι (DiagSet.cartesianMarkedHom p) :=
    DiagSet.hasLiftingProperty_pushoutProduct_markingInclusion_arrow p
  exact (HasLiftingProperty.iff_of_arrow_iso_left b (DiagSet.cartesianMarkedHom p)).1 h

end Atoms.Diagrammatic
