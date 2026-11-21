import Atoms.Diagrammatic.GrayCylinder.Exact
import Atoms.Shape.Horn

open CategoryTheory Limits Opposite Atoms.Molecule Atoms.Molecule.OGP Atoms.Shape HomotopicalAlgebra

universe u

namespace Atoms.Diagrammatic

def horn (h : HornData) : DiagSet.{u} := (closedSubpresheaf h.atom (hornSubset h)).toFunctor

def hornInclusion (h : HornData) : horn.{u} h ⟶ ball h.atom :=
  (closedSubpresheaf h.atom (hornSubset h)).ι

def hornInclusions : MorphismProperty DiagSet.{u} := MorphismProperty.ofHoms hornInclusion

def IsHornFibrant (X : DiagSet.{u}) : Prop := hornInclusions.rlp (terminal.from X)

theorem isHornFibrant_prod {X Y : DiagSet.{u}} (hX : IsHornFibrant X) (hY : IsHornFibrant Y) :
    IsHornFibrant (X ⨯ Y) := by
  have h : terminal.from (X ⨯ Y) = prod.fst ≫ terminal.from X := terminal.hom_ext _ _
  rw [IsHornFibrant, h]
  exact hornInclusions.rlp.comp_mem _ _
    (hornInclusions.rlp.of_isPullback (IsPullback.of_hasBinaryProduct' X Y).flip hY) hX

theorem hornInclusions_le_monomorphisms :
    hornInclusions ≤ MorphismProperty.monomorphisms DiagSet.{u} := by
  rw [hornInclusions, MorphismProperty.ofHoms_le_iff]
  intro h
  exact MorphismProperty.monomorphisms.infer_property
    (closedSubpresheaf h.atom (hornSubset h)).ι

instance isSmall_hornInclusions : MorphismProperty.IsSmall.{u} hornInclusions.{u} :=
  MorphismProperty.isSmall_ofHoms _

theorem range_grayCylinderFunctor_map_closedSubpresheaf_ι (U : Atom) (S : LowerSet U.ogp) :
    Subfunctor.range (grayCylinderFunctor.map (closedSubpresheaf.{u} U S).ι ≫
      (grayCylinderFunctorYonedaIso.app U).hom) =
      closedSubpresheaf (grayCylinder.obj U) (cylinderSubset U S) := by
  have key : ∀ {A Y Y' : DiagSet.{u}} (G : Subfunctor Y') (a : A ≅ G.toFunctor) (e : Y ≅ Y'),
      Subfunctor.range ((a.hom ≫ G.ι ≫ e.inv) ≫ e.hom) = G := by
    intro A Y Y' G a e
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Subfunctor.range_comp, Subfunctor.range_eq_top, Subfunctor.image_top, Subfunctor.range_ι]
  rw [grayCylinderFunctor_map_closedSubpresheaf_ι U S]
  exact key _ _ _

theorem range_grayCylinderEndpoint_app_ball (ε : Bool) (U : Atom) :
    Subfunctor.range ((grayCylinderEndpoint ε).app (ball.{u} U) ≫
      (grayCylinderFunctorYonedaIso.app U).hom) =
      closedSubpresheaf (grayCylinder.obj U) (endpointSubset ε U) := by
  rw [Iso.app_hom, grayCylinderEndpoint_app_ball]
  exact range_yoneda_map_of_isInclusionHom _ (isInclusionHom_grayEndpoint ε U)

theorem range_endpointBox_closedSubpresheaf_ι (ε : Bool) (U : Atom) (S : LowerSet U.ogp) :
    Subfunctor.range (grayExactCylinder.{u}.endpointBox ε (closedSubpresheaf U S).ι ≫
      (grayCylinderFunctorYonedaIso.app U).hom) =
      closedSubpresheaf (grayCylinder.obj U)
        (cylinderSubset U S ⊔ endpointSubset ε U) := by
  refine (Subfunctor.range_pushout_desc_comp _ _ _ _ _ _).trans ?_
  rw [closedSubpresheaf_union]
  exact congrArg₂ (· ⊔ ·) (range_grayCylinderFunctor_map_closedSubpresheaf_ι U S)
    (range_grayCylinderEndpoint_app_ball ε U)

theorem range_bothBox_closedSubpresheaf_ι (U : Atom) (S : LowerSet U.ogp) :
    Subfunctor.range (grayExactCylinder.{u}.bothBox (closedSubpresheaf U S).ι ≫
      (grayCylinderFunctorYonedaIso.app U).hom) =
      closedSubpresheaf (grayCylinder.obj U)
        (cylinderSubset U S ⊔ (endpointSubset false U ⊔ endpointSubset true U)) := by
  refine (Subfunctor.range_pushout_desc_comp _ _ _ _ _ _).trans ?_
  rw [closedSubpresheaf_union, closedSubpresheaf_union]
  exact congrArg₂ (· ⊔ ·) (range_grayCylinderFunctor_map_closedSubpresheaf_ι U S)
    ((Subfunctor.range_coprod_desc_comp ((grayCylinderEndpoint false).app (ball.{u} U)) _ _).trans
      (congrArg₂ (· ⊔ ·) (range_grayCylinderEndpoint_app_ball false U)
        (range_grayCylinderEndpoint_app_ball true U)))

theorem endpointBox_sphereInclusion_iso (ε : Bool) (U : Atom) :
    Nonempty (Arrow.mk (grayExactCylinder.{u}.endpointBox ε (sphereInclusion U)) ≅
      Arrow.mk (hornInclusion (endpointHornData ε U))) := by
  have key : ∀ B : Subfunctor (ball.{u} U), closedSubpresheaf U (U.ogp.bdryFull ⊤) = B →
      Nonempty (Arrow.mk (grayExactCylinder.endpointBox ε B.ι) ≅
        Arrow.mk (hornInclusion (endpointHornData ε U))) := by
    rintro B rfl
    have := grayExactCylinder.{u}.mono_endpointBox ε _
      (inferInstance : Mono (closedSubpresheaf U (U.ogp.bdryFull ⊤)).ι)
    have h := range_endpointBox_closedSubpresheaf_ι.{u} ε U (U.ogp.bdryFull ⊤)
    rw [← hornSubset_endpointHornData] at h
    exact @Subfunctor.nonempty_arrow_iso_of_range_comp_eq _ _ _ _ _ _ this
      (grayCylinderFunctorYonedaIso.app U) _ h
  exact key _ (closedSubpresheaf_univ_erase_top U)

theorem bothBox_hornInclusion_iso (h : HornData) :
    Nonempty (Arrow.mk (grayExactCylinder.{u}.bothBox (hornInclusion h)) ≅
      Arrow.mk (hornInclusion (cylinderHornData h))) := by
  have := grayExactCylinder.{u}.mono_bothBox _
    (inferInstance : Mono (closedSubpresheaf h.atom (hornSubset h)).ι)
  have e := range_bothBox_closedSubpresheaf_ι.{u} h.atom (hornSubset h)
  rw [← hornSubset_cylinderHornData] at e
  exact @Subfunctor.nonempty_arrow_iso_of_range_comp_eq _ _ _ _ _ _ this
    (grayCylinderFunctorYonedaIso.app h.atom) _ e

theorem endpointBox_sphereInclusion_mem_saturation (ε : Bool) (U : Atom) :
    MorphismProperty.saturation.{u} hornInclusions.{u}
      (grayExactCylinder.{u}.endpointBox ε (sphereInclusion U)) := by
  obtain ⟨e⟩ := endpointBox_sphereInclusion_iso ε U
  exact (MorphismProperty.arrow_mk_iso_iff _ e).2
    (MorphismProperty.le_saturation hornInclusions _ (MorphismProperty.ofHoms.mk _))

theorem bothBox_hornInclusion_mem_saturation (h : HornData) :
    MorphismProperty.saturation.{u} hornInclusions.{u}
      (grayExactCylinder.{u}.bothBox (hornInclusion h)) := by
  obtain ⟨e⟩ := bothBox_hornInclusion_iso h
  exact (MorphismProperty.arrow_mk_iso_iff _ e).2
    (MorphismProperty.le_saturation hornInclusions _ (MorphismProperty.ofHoms.mk _))

end Atoms.Diagrammatic
