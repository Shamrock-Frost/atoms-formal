import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Cisinski.Anodyne
import Atoms.ForMathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Atoms.ForMathlib.CategoryTheory.MorphismProperty.Basic
import Atoms.ForMathlib.CategoryTheory.MorphismProperty.Saturation

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra.ExactCylinder

universe w w' v v' u u'

variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]

section Compatible

variable {D : Type u'} [Category.{v'} D] [HasBinaryCoproducts D] [HasPushouts C] [HasPushouts D]
  (𝕀 : ExactCylinder.{w} C) (𝕁 : ExactCylinder.{w'} D)
  (F : C ⥤ D) [PreservesColimitsOfShape WalkingSpan F]
  [PreservesColimitsOfShape (Discrete WalkingPair) F] (α : 𝕀.I ⋙ F ≅ F ⋙ 𝕁.I)
  (hα : ∀ (ε : Bool) (X : C), F.map ((𝕀.endpoint ε).app X) ≫ α.hom.app X =
    (𝕁.endpoint ε).app (F.obj X))

omit [HasPushouts D] [PreservesColimitsOfShape (Discrete WalkingPair) F] in
include hα in
theorem isPushout_map_endpointBoxSource (ε : Bool) {K Y : C} (i : K ⟶ Y) :
    IsPushout ((𝕁.endpoint ε).app (F.obj K)) (F.map i)
      (α.inv.app K ≫ F.map (pushout.inl ((𝕀.endpoint ε).app K) i))
      (F.map (pushout.inr ((𝕀.endpoint ε).app K) i)) := by
  refine ((IsPushout.of_hasPushout ((𝕀.endpoint ε).app K) i).map F).of_iso (Iso.refl _)
    (α.app K) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [Iso.app_hom, Iso.refl_hom, Category.id_comp]
    exact hα ε K
  · simp
  · simp
  · simp

omit [PreservesColimitsOfShape (Discrete WalkingPair) F] in
include hα in
theorem isoPushout_hom_endpointBox (ε : Bool) {K Y : C} (i : K ⟶ Y) :
    (isPushout_map_endpointBoxSource 𝕀 𝕁 F α hα ε i).isoPushout.hom ≫
        𝕁.endpointBox ε (F.map i) = F.map (𝕀.endpointBox ε i) ≫ α.hom.app Y := by
  dsimp only [ExactCylinder.endpointBox, ExactCylinder.endpointBoxSource]
  refine (isPushout_map_endpointBoxSource 𝕀 𝕁 F α hα ε i).hom_ext ?_ ?_
  · rw [IsPushout.inl_isoPushout_hom_assoc]
    simp only [pushout.inl_desc, Category.assoc, ← Functor.map_comp_assoc]
    exact (NatIso.naturality_1 α i).symm
  · rw [IsPushout.inr_isoPushout_hom_assoc]
    simp only [pushout.inr_desc, ← Functor.map_comp_assoc]
    exact (hα ε Y).symm

omit [PreservesColimitsOfShape (Discrete WalkingPair) F] in
noncomputable def endpointBoxMapArrowIso (ε : Bool) {K Y : C} (i : K ⟶ Y) :
    Arrow.mk (F.map (𝕀.endpointBox ε i)) ≅ Arrow.mk (𝕁.endpointBox ε (F.map i)) :=
  Arrow.isoMk (isPushout_map_endpointBoxSource 𝕀 𝕁 F α hα ε i).isoPushout (α.app Y)
    (isoPushout_hom_endpointBox 𝕀 𝕁 F α hα ε i)

omit [HasPushouts D] in
include hα in
theorem isPushout_map_bothBoxSource {K Y : C} (i : K ⟶ Y) :
    IsPushout (𝕁.endpoints (F.obj K)) (coprod.map (F.map i) (F.map i))
      (α.inv.app K ≫ F.map (pushout.inl (𝕀.endpoints K) (coprod.map i i)))
      (coprodComparison F Y Y ≫ F.map (pushout.inr (𝕀.endpoints K) (coprod.map i i))) := by
  refine ((IsPushout.of_hasPushout (𝕀.endpoints K) (coprod.map i i)).map F).of_iso
    (asIso (coprodComparison F K K)).symm (α.app K)
    (asIso (coprodComparison F Y Y)).symm (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [Iso.symm_hom, asIso_inv, IsIso.eq_inv_comp, Iso.app_hom]
    exact coprodComparison_map_desc_comp F _ _ _ _ _ (hα false K) (hα true K)
  · rw [Iso.symm_hom, asIso_inv, Iso.symm_hom, asIso_inv, IsIso.eq_inv_comp, ← Category.assoc,
      IsIso.comp_inv_eq, coprodComparison_natural]
  · simp
  · simp

include hα in
theorem isoPushout_hom_bothBox {K Y : C} (i : K ⟶ Y) :
    (isPushout_map_bothBoxSource 𝕀 𝕁 F α hα i).isoPushout.hom ≫ 𝕁.bothBox (F.map i) =
      F.map (𝕀.bothBox i) ≫ α.hom.app Y := by
  dsimp only [ExactCylinder.bothBox, ExactCylinder.bothBoxSource]
  refine (isPushout_map_bothBoxSource 𝕀 𝕁 F α hα i).hom_ext ?_ ?_
  · rw [IsPushout.inl_isoPushout_hom_assoc]
    simp only [pushout.inl_desc, Category.assoc, ← Functor.map_comp_assoc]
    exact (NatIso.naturality_1 α i).symm
  · rw [IsPushout.inr_isoPushout_hom_assoc]
    simp only [pushout.inr_desc, Category.assoc, ← Functor.map_comp_assoc]
    exact (coprodComparison_map_desc_comp F _ _ _ _ _ (hα false Y) (hα true Y)).symm

noncomputable def bothBoxMapArrowIso {K Y : C} (i : K ⟶ Y) :
    Arrow.mk (F.map (𝕀.bothBox i)) ≅ Arrow.mk (𝕁.bothBox (F.map i)) :=
  Arrow.isoMk (isPushout_map_bothBoxSource 𝕀 𝕁 F α hα i).isoPushout (α.app Y)
    (isoPushout_hom_bothBox 𝕀 𝕁 F α hα i)

end Compatible

section Transport

variable {D : Type u'} [Category.{v'} D] [HasBinaryCoproducts D] (𝕀 : ExactCylinder.{w} C)
  (e : C ≌ D)

noncomputable def transport : ExactCylinder.{w} D where
  I := e.inverse ⋙ 𝕀.I ⋙ e.functor
  endpoint ε :=
    { app X := e.counitIso.inv.app X ≫ e.functor.map ((𝕀.endpoint ε).app (e.inverse.obj X))
      naturality X Y f := by
        simp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map,
          Category.assoc, ← Functor.map_comp, ← (𝕀.endpoint ε).naturality]
        simp }
  contraction :=
    { app X := e.functor.map (𝕀.contraction.app (e.inverse.obj X)) ≫ e.counitIso.hom.app X
      naturality X Y f := by
        simp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map,
          ← Category.assoc, ← Functor.map_comp, 𝕀.contraction.naturality]
        simp }
  endpoint_contraction ε := by
    ext X
    simp [← Functor.map_comp_assoc]
  mono_endpoints X := by
    have h := coprodComparison_map_desc_comp e.functor ((𝕀.endpoint false).app (e.inverse.obj X))
      ((𝕀.endpoint true).app (e.inverse.obj X)) (𝟙 _) _ _ (Category.comp_id _)
      (Category.comp_id _)
    have := 𝕀.mono_endpoints (e.inverse.obj X)
    have hm : Mono (coprod.desc (e.functor.map ((𝕀.endpoint false).app (e.inverse.obj X)))
        (e.functor.map ((𝕀.endpoint true).app (e.inverse.obj X)))) := by
      rw [← h, Category.comp_id]
      infer_instance
    have hi : IsIso (coprod.map (e.counitIso.inv.app X) (e.counitIso.inv.app X)) :=
      ⟨coprod.map (e.counitIso.hom.app X) (e.counitIso.hom.app X), by simp, by simp⟩
    rw [← coprod.map_desc]
    exact @mono_comp _ _ _ _ _ _ inferInstance _ hm
  preservesMonomorphisms := inferInstance
  preservesColimits := inferInstance

end Transport

section Anodyne

variable {D : Type u'} [Category.{v} D] [HasBinaryCoproducts D] [HasPushouts C] [HasPushouts D]
  (𝕀 : ExactCylinder.{w} C) (e : C ≌ D)

private noncomputable def functorIso : 𝕀.I ⋙ e.functor ≅ e.functor ⋙ (𝕀.transport e).I :=
  Functor.isoWhiskerRight e.unitIso (𝕀.I ⋙ e.functor)

omit [HasPushouts C] [HasPushouts D] in
private theorem functorIso_comp (ε : Bool) (X : C) :
    e.functor.map ((𝕀.endpoint ε).app X) ≫ (functorIso 𝕀 e).hom.app X =
      ((𝕀.transport e).endpoint ε).app (e.functor.obj X) := by
  change e.functor.map ((𝕀.endpoint ε).app X) ≫ e.functor.map (𝕀.I.map (e.unit.app X)) =
    e.counitInv.app (e.functor.obj X) ≫
      e.functor.map ((𝕀.endpoint ε).app (e.inverse.obj (e.functor.obj X)))
  rw [← Functor.map_comp, ← (𝕀.endpoint ε).naturality, Functor.map_comp,
    Equivalence.counitInv_app_functor]
  rfl

private noncomputable def inverseIso : (𝕀.transport e).I ⋙ e.inverse ≅ e.inverse ⋙ 𝕀.I :=
  Functor.isoWhiskerLeft (e.inverse ⋙ 𝕀.I) e.unitIso.symm

omit [HasPushouts C] [HasPushouts D] in
private theorem inverseIso_comp (ε : Bool) (X : D) :
    e.inverse.map (((𝕀.transport e).endpoint ε).app X) ≫ (inverseIso 𝕀 e).hom.app X =
      (𝕀.endpoint ε).app (e.inverse.obj X) := by
  change e.inverse.map (e.counitInv.app X ≫
      e.functor.map ((𝕀.endpoint ε).app (e.inverse.obj X))) ≫
      e.unitInv.app (𝕀.I.obj (e.inverse.obj X)) = (𝕀.endpoint ε).app (e.inverse.obj X)
  have h := e.unitInv.naturality ((𝕀.endpoint ε).app (e.inverse.obj X))
  rw [Functor.comp_map, Functor.id_map] at h
  rw [Functor.map_comp, Category.assoc, h]
  simp

theorem anodyne_transport_map_iff (S : MorphismProperty C) {X Y : C} (f : X ⟶ Y) :
    (𝕀.transport e).anodyne (functorImage e.functor S) (e.functor.map f) ↔ 𝕀.anodyne S f := by
  constructor
  · intro hf
    have hle := (𝕀.transport e).anodyne_le (functorImage e.functor S)
      ((𝕀.anodyne S).inverseImage e.inverse)
      { isSaturated := IsSaturated.inverseImage e.inverse _
        generators_le := by
          rintro _ _ g ⟨K, L, t, ht, h⟩
          refine (arrow_mk_iso_iff _ ((e.inverse.mapArrow).mapIso (eqToIso h))).1 ?_
          exact (map_functor_map_inverse_iff e.symm (𝕀.anodyne S) t).2 (𝕀.le_anodyne S t ht)
        endpointBox_mem := fun ε _ _ j hj ↦ by
          have : Mono j := hj
          exact ((𝕀.anodyne S).arrow_mk_iso_iff
            (endpointBoxMapArrowIso _ 𝕀 e.inverse (inverseIso 𝕀 e) (inverseIso_comp 𝕀 e) ε j)).2
            ((𝕀.isAnodyneClass_anodyne S).endpointBox_mem ε _ (e.inverse.map_mono j))
        bothBox_mem := fun j hj h ↦ by
          have : Mono j := hj
          exact ((𝕀.anodyne S).arrow_mk_iso_iff
            (bothBoxMapArrowIso _ 𝕀 e.inverse (inverseIso 𝕀 e) (inverseIso_comp 𝕀 e) j)).2
            ((𝕀.isAnodyneClass_anodyne S).bothBox_mem _ (e.inverse.map_mono j) h) }
    exact (map_functor_map_inverse_iff e.symm (𝕀.anodyne S) f).1 (hle _ hf)
  · intro hf
    refine 𝕀.anodyne_le S (((𝕀.transport e).anodyne (functorImage e.functor S)).inverseImage
      e.functor)
      { isSaturated := IsSaturated.inverseImage e.functor _
        generators_le := fun K L t ht ↦ (𝕀.transport e).le_anodyne _ _ ⟨K, L, t, ht, rfl⟩
        endpointBox_mem := fun ε _ _ i hi ↦ by
          have : Mono i := hi
          exact (((𝕀.transport e).anodyne _).arrow_mk_iso_iff
            (endpointBoxMapArrowIso 𝕀 _ e.functor (functorIso 𝕀 e) (functorIso_comp 𝕀 e) ε i)).2
            (((𝕀.transport e).isAnodyneClass_anodyne _).endpointBox_mem ε _
              (e.functor.map_mono i))
        bothBox_mem := fun i hi h ↦ by
          have : Mono i := hi
          exact (((𝕀.transport e).anodyne _).arrow_mk_iso_iff
            (bothBoxMapArrowIso 𝕀 _ e.functor (functorIso 𝕀 e) (functorIso_comp 𝕀 e) i)).2
            (((𝕀.transport e).isAnodyneClass_anodyne _).bothBox_mem _ (e.functor.map_mono i) h) }
      f hf

end Anodyne

end HomotopicalAlgebra.ExactCylinder
