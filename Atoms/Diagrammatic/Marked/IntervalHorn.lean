import Atoms.Diagrammatic.Marked.CylinderTensor
import Atoms.Diagrammatic.Marked.Fibrancy
import Atoms.Diagrammatic.Marked.HornGrayTensor

open CategoryTheory Limits Opposite Atoms.Shape Atoms.Molecule Atoms.Molecule.OGP
open Atoms.Homotopical

universe u

namespace Atoms.Diagrammatic

abbrev intervalInputHorn : MarkedHornData := by
  let U := atomGlobe 1
  let i := FiniteOGP.ofOGPIso (globe 1)
  let x : U.ogp := i.hom (SuspCarrier.pole false)
  have ht : i.hom ⊤ = U.top := by
    have h := map_Iic i.hom ⊤
    rw [LowerSet.Iic_top, map_top_of_isIso] at h
    exact (LowerSet.Iic_inj.1 (U.Iic_top.trans h)).symm
  have hbd : U.ogp.bdry ⊤ false = LowerSet.Iic x := by
    change (FiniteOGP.ofOGP (globe 1)).ogp.bdry ⊤ false = _
    rw [← map_top_of_isIso i.hom, ← map_bdry, bdry_globe_one, map_Iic]
    rfl
  have hx : x ⋖ U.top := by
    rw [← ht]
    exact (isMorphism i.hom).covBy_apply (SuspCarrier.pole_covBy_susp.2 (isMin_point _))
  have ho : U.ogp.orient hx = false := by
    have he : SuspCarrier.pole false ⋖ (⊤ : globe 1) :=
      SuspCarrier.pole_covBy_susp.2 (isMin_point _)
    have h := (isMorphism i.hom).orient_apply he
    exact (U.ogp.orient_congr ht rfl _ hx).symm.trans
      (h.trans rfl)
  refine ⟨U, by rw [dimension_atomGlobe]; omega, false, x,
    ⟨hx, ho⟩, ∅, fun _ h => h.elim, (fun _ => ⊥), (fun _ => ⊥),
    (fun _ => LowerSet.Iic x), ?_, ?_, ?_⟩
  · refine ⟨rfl, fun _ _ => U.isRDC x, ?_, ?_, ?_⟩ <;>
      intro j hj <;> rw [dimension_atomGlobe] at hj <;> omega
  · exact hbd.symm
  · intro j hj
    rw [dimension_atomGlobe] at hj
    omega
private theorem intervalInputHorn_targetMarking :
    intervalInputHorn.targetMarking = {intervalInputHorn.atom.top} := by
  ext a
  refine intervalInputHorn.mem_targetMarking_iff.trans ?_
  constructor
  · rintro (h | ⟨h, -⟩ | h)
    · exact h
    · have hd := intervalInputHorn.dim_face_add_one
      have hp := intervalInputHorn.dim_face_pos_of_faceSet_subset h
      have he : intervalInputHorn.atom.dimension = 1 := dimension_atomGlobe 1
      omega
    · exact h.elim
  · exact Or.inl

private theorem intervalInputHorn_hornSet :
    intervalInputHorn.hornSet = Atom.map (atomGlobeVertex true) ⊤ := by
  let m := intervalInputHorn
  let i := FiniteOGP.ofOGPIso (globe 1)
  let y : m.atom.ogp := i.hom (SuspCarrier.pole true)
  have hbd : m.atom.ogp.bdry ⊤ true = LowerSet.Iic y := by
    change (FiniteOGP.ofOGP (globe 1)).ogp.bdry ⊤ true = _
    rw [← map_top_of_isIso i.hom, ← map_bdry, bdry_globe_one, map_Iic]
    rfl
  obtain ⟨z, hz⟩ := m.exists_hornSet_eq_singleton (dimension_atomGlobe 1)
  have hy : y = z := by
    apply Set.mem_singleton_iff.1
    rw [← hz]
    exact m.bdry_not_subset_hornSet (hbd.symm ▸ LowerSet.mem_Iic_iff.2 le_rfl)
  have hm : IsMin y := grade_eq_zero_iff.1
    (((isMorphism i.hom).grade_eq _).trans (SuspCarrier.grade_pole true))
  rw [Atom.map_top, atomGlobeVertex_apply]
  ext a
  change a ∈ m.hornSet ↔ a ≤ y
  rw [show a ∈ m.hornSet ↔ a = z from Set.ext_iff.1 hz a, ← hy]
  exact ⟨fun h => h ▸ le_rfl, fun h => hm.eq_of_le h⟩

private noncomputable def intervalInputHornTargetIso :
    intervalInputHorn.target ≅ markedInterval.{u} :=
  markedTargetIso intervalInputHorn ≪≫
    (by simpa only [intervalInputHorn_targetMarking, markedInterval] using
      (yonedaMarkedIso.{u} (atomGlobe 1) markable_atomGlobe_one).symm)

private theorem intervalInputHorn_arrowIso :
    Nonempty (Arrow.mk (markedIntervalVertex.{u} true) ≅
      Arrow.mk (markedHornInclusion.{u} intervalInputHorn)) := by
  have hr : Subfunctor.range (MarkedPresheaf.forget.map (markedIntervalVertex.{u} true) ≫
      intervalBallIso.inv) =
        closedSubpresheaf intervalInputHorn.atom intervalInputHorn.hornSet := by
    have he : (MarkedPresheaf.forget.map (markedIntervalVertex.{u} true) :
        ball.{u} atomPoint ⟶ markedInterval.underlying) ≫ intervalBallIso.inv =
          uliftYoneda.map (atomGlobeVertex true) := by
      calc
        _ = (uliftYoneda.map (atomGlobeVertex true) ≫ intervalBallIso.hom) ≫
            intervalBallIso.inv := congrArg (fun f : ball.{u} atomPoint ⟶
              markedInterval.underlying => f ≫ intervalBallIso.inv)
                (forget_map_markedIntervalVertex true)
        _ = _ := by rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact (congrArg (fun f : ball.{u} atomPoint ⟶ ball.{u} (atomGlobe 1) =>
      Subfunctor.range f) he).trans (by
      rw [range_yoneda_map_of_isInclusionHom _ (fun _ _ _ => Subsingleton.elim _ _),
        intervalInputHorn_hornSet])
  have : Mono (atomGlobeVertex true) :=
    mono_of_isInclusionHom _ (fun _ _ _ => Subsingleton.elim _ _)
  have : Mono (MarkedPresheaf.forget.map (markedIntervalVertex.{u} true)) := by
    change Mono (uliftYoneda.{u}.map (atomGlobeVertex true) ≫ intervalBallIso.hom)
    infer_instance
  obtain ⟨e⟩ := Subfunctor.nonempty_arrow_iso_of_range_comp_eq
    (MarkedPresheaf.forget.map (markedIntervalVertex.{u} true)) intervalBallIso.symm _ hr
  let E := e ≪≫ intervalInputHorn.forgetArrowIso.symm
  refine nonempty_arrowIso_of_forget (markedIntervalVertex true)
    (markedHornInclusion intervalInputHorn) (fun V x hx => ?_)
    (fun _ x hx => mem_marked_source_of_markedHornInclusion _ x hx) E (fun V y => ?_)
  · apply (MarkedDiagSet.mem_marked_flat_iff_isDegenerate _ V x).2
    exact isDegenerate_map_of_dimension_eq_zero (Y := ball.{u} atomPoint) x.down
      dimension_atomPoint (markedInterval.markable _ _ hx)
      (⟨𝟙 atomPoint⟩ : diagram (ball atomPoint) atomPoint)
  · have he : Arrow.rightFunc.mapIso E ≪≫
        (MarkedPresheaf.forget.mapIso intervalInputHornTargetIso) ≪≫ intervalBallIso.symm =
        intervalBallIso.symm := iso_ball_ext _ _
    have hmap : E.hom.right =
        MarkedPresheaf.forget.map intervalInputHornTargetIso.inv := by
      apply (cancel_mono (MarkedPresheaf.forget.map intervalInputHornTargetIso.hom)).1
      rw [← Functor.map_comp, Iso.inv_hom_id, MarkedPresheaf.forget.map_id]
      exact (cancel_mono intervalBallIso.inv).1 (congrArg Iso.hom he)
    rw [hmap]
    exact ⟨MarkedPresheaf.map_mem_marked _, fun h => by
      have h' := MarkedPresheaf.map_mem_marked intervalInputHornTargetIso.hom h
      have heval : (MarkedPresheaf.forget.map intervalInputHornTargetIso.hom).app (op V)
          ((MarkedPresheaf.forget.map intervalInputHornTargetIso.inv).app (op V) y) = y :=
        congrArg (fun f => f.app (op V) y)
          (MarkedPresheaf.forget.mapIso intervalInputHornTargetIso).inv_hom_id
      exact heval ▸ h'⟩

theorem exists_arrowIso_pushoutProduct_flat_sphere_intervalVertex (V : Atom) :
    ∃ h : MarkedHornData, h.atom = Atom.grayTensor V (atomGlobe 1) ∧
      h.toHornData = HornData.grayTensorLeft V intervalInputHorn.toHornData ∧
      HEq h.targetMarking {w : (Atom.grayTensor V (atomGlobe 1)).ogp |
        ((Atom.grayTensorIso V (atomGlobe 1)).inv w).2 = (atomGlobe 1).top} ∧
      Nonempty (Arrow.mk (Functor.PushoutObjObj.ofHasPushout
        (Functor.curry.obj (markedTensorBifunctor.{u} false))
        ((MarkedPresheaf.flat atomMarking).map (sphereInclusion V))
        (markedIntervalVertex true)).ι ≅ Arrow.mk (markedHornInclusion.{u} h)) := by
  obtain ⟨e⟩ := intervalInputHorn_arrowIso.{u}
  obtain ⟨h, ha, hh, hm, ⟨b⟩⟩ :=
    exists_arrowIso_pushoutProduct_sphere_markedHornInclusion_with_data.{u} V intervalInputHorn
  let b₁ := Functor.PushoutObjObj.ι_iso_of_iso_left
    (f₂ := Arrow.mk (markedIntervalVertex.{u} true))
    (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} false)) _ _)
    (Functor.PushoutObjObj.ofHasPushout _ _ _) (flatSphereInclusionArrowIso V)
  let b₂ := Functor.PushoutObjObj.ι_iso_of_iso_right
    (f₁ := Arrow.mk (sphereToMarkedBall.{u} V))
    (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} false)) _ _)
    (Functor.PushoutObjObj.ofHasPushout _ _ _) e
  refine ⟨h, ha, hh, ?_, ⟨b₁ ≪≫ b₂ ≪≫ b⟩⟩
  simpa only [intervalInputHorn_targetMarking, Set.mem_singleton_iff] using hm

end Atoms.Diagrammatic
