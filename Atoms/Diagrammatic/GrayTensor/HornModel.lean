import Atoms.ForMathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Atoms.Diagrammatic.GrayTensor.Monoidal
import Atoms.Diagrammatic.GrayTensor.PushoutProduct
import Atoms.Diagrammatic.InfinityEquivalence
import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Quillen
import Atoms.Shape.GrayTensorHorn

open CategoryTheory Limits Opposite MorphismProperty Atoms.Molecule Atoms.Molecule.OGP
  Atoms.Shape

universe u

namespace Atoms.Diagrammatic

private theorem nonempty_arrowIso_realize_restrictIncl_hornSubset (h : HornData) :
    Nonempty (Arrow.mk (realize.{u}.map ((atomToRDCpx.obj h.atom).restrictIncl (hornSubset h))) ≅
      Arrow.mk (hornInclusion.{u} h)) :=
  ⟨Arrow.isoMk (realizeRestrictIso _ _ _ rfl ≪≫ realizeSubsetAtomIso h.atom _)
    (realizeAtomIso h.atom) (by ext T f; rfl)⟩

private theorem image_realizeSubset_grayProductRDC (V U : Atom)
    (S : LowerSet (grayProduct V.ogp U.ogp)) :
    (realizeSubset.{u} (grayProductRDC (atomToRDCpx.obj V) (atomToRDCpx.obj U)) S).image
        (realize.map (atomGrayProductIso V U).inv ≫ (realizeAtomIso _).hom) =
      closedSubpresheaf (Atom.grayTensor V U) (map (Atom.grayTensorIso V U).hom S) := by
  ext ⟨T⟩ ⟨f : T ⟶ Atom.grayTensor V U⟩
  constructor
  · rintro ⟨⟨c⟩, hc, hcf⟩ t
    rw [← hcf]
    exact OGP.mem_map.2 ⟨_, hc t, rfl⟩
  · intro hf
    refine ⟨⟨atomToRDCpx.map f ≫ (atomGrayProductIso V U).hom⟩, fun t => ?_,
      ULift.ext _ _ (Atom.hom_ext fun t => Iso.inv_hom_id_apply _ (f t))⟩
    obtain ⟨s, hs, hst⟩ := OGP.mem_map.1 (hf t)
    change (Atom.grayTensorIso V U).inv (f t) ∈ S
    rwa [← hst, Iso.hom_inv_id_apply]

private theorem nonempty_arrowIso_pushoutProduct_realize_restrictIncl (V U : Atom)
    (S : LowerSet V.ogp) (T : LowerSet U.ogp) :
    Nonempty (Arrow.mk (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj grayTensorBifunctor.{u})
      (realize.map ((atomToRDCpx.obj V).restrictIncl S))
      (realize.map ((atomToRDCpx.obj U).restrictIncl T))).ι ≅
      Arrow.mk (closedSubpresheaf.{u} (Atom.grayTensor V U)
        (map (Atom.grayTensorIso V U).hom (S ×ˢ (⊤ : LowerSet U.ogp) ⊔
          (⊤ : LowerSet V.ogp) ×ˢ T))).ι) := by
  have := mono_pushoutProduct_realize_restrictIncl.{u} (atomToRDCpx.obj V) (atomToRDCpx.obj U) S T
  refine Subfunctor.nonempty_arrow_iso_of_range_comp_eq _
    ((realizeGrayProductIso _ _).symm ≪≫ realize.mapIso (atomGrayProductIso V U).symm ≪≫
      realizeAtomIso _) _ ?_
  rw [Iso.trans_hom, Iso.trans_hom, ← Category.assoc, Subfunctor.range_comp, Iso.symm_hom,
    range_pushoutProduct_realize_restrictIncl]
  exact image_realizeSubset_grayProductRDC V U _

theorem nonempty_arrowIso_pushoutProduct_hornInclusion_sphereInclusion (h : HornData) (U : Atom) :
    Nonempty (Arrow.mk (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj grayTensorBifunctor.{u}) (hornInclusion h) (sphereInclusion U)).ι ≅
      Arrow.mk (hornInclusion (h.grayTensorRight U))) := by
  obtain ⟨e₁⟩ := nonempty_arrowIso_realize_restrictIncl_hornSubset.{u} h
  obtain ⟨e₂⟩ := nonempty_arrowIso_realize_restrictIncl_bdryFull.{u} U
  obtain ⟨e⟩ := nonempty_arrowIso_pushoutProduct_realize_restrictIncl.{u} h.atom U
    (hornSubset h) (U.ogp.bdryFull ⊤)
  rw [← hornSubset_grayTensorRight] at e
  have e₃ := Functor.PushoutObjObj.ι_iso_of_iso_left (f₂ := Arrow.mk (sphereInclusion U))
    (Functor.PushoutObjObj.ofHasPushout (Functor.curry.obj grayTensorBifunctor.{u}) _ _)
    (Functor.PushoutObjObj.ofHasPushout _ _ _) e₁.symm
  have e₄ := Functor.PushoutObjObj.ι_iso_of_iso_right
    (f₁ := Arrow.mk (realize.map ((atomToRDCpx.obj h.atom).restrictIncl (hornSubset h))))
    (Functor.PushoutObjObj.ofHasPushout (Functor.curry.obj grayTensorBifunctor.{u}) _ _)
    (Functor.PushoutObjObj.ofHasPushout _ _ _) e₂.symm
  exact ⟨e₃ ≪≫ e₄ ≪≫ e⟩

theorem nonempty_arrowIso_pushoutProduct_sphereInclusion_hornInclusion (U : Atom) (h : HornData) :
    Nonempty (Arrow.mk (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj grayTensorBifunctor.{u}) (sphereInclusion U) (hornInclusion h)).ι ≅
      Arrow.mk (hornInclusion (HornData.grayTensorLeft U h))) := by
  obtain ⟨e₁⟩ := nonempty_arrowIso_realize_restrictIncl_bdryFull.{u} U
  obtain ⟨e₂⟩ := nonempty_arrowIso_realize_restrictIncl_hornSubset.{u} h
  obtain ⟨e⟩ := nonempty_arrowIso_pushoutProduct_realize_restrictIncl.{u} U h.atom
    (U.ogp.bdryFull ⊤) (hornSubset h)
  rw [← hornSubset_grayTensorLeft] at e
  have e₃ := Functor.PushoutObjObj.ι_iso_of_iso_left (f₂ := Arrow.mk (hornInclusion h))
    (Functor.PushoutObjObj.ofHasPushout (Functor.curry.obj grayTensorBifunctor.{u}) _ _)
    (Functor.PushoutObjObj.ofHasPushout _ _ _) e₁.symm
  have e₄ := Functor.PushoutObjObj.ι_iso_of_iso_right
    (f₁ := Arrow.mk (realize.map ((atomToRDCpx.obj U).restrictIncl (U.ogp.bdryFull ⊤))))
    (Functor.PushoutObjObj.ofHasPushout (Functor.curry.obj grayTensorBifunctor.{u}) _ _)
    (Functor.PushoutObjObj.ofHasPushout _ _ _) e₂.symm
  exact ⟨e₃ ≪≫ e₄ ≪≫ e⟩

theorem saturation_hornInclusions_pushoutProduct {X₁ Y₁ X₂ Y₂ : DiagSet.{u}} (f₁ : X₁ ⟶ Y₁)
    (f₂ : X₂ ⟶ Y₂) [Mono f₁] [Mono f₂]
    (h : saturation.{u} hornInclusions.{u} f₁ ∨ saturation.{u} hornInclusions.{u} f₂) :
    saturation.{u} hornInclusions.{u} (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj grayTensorBifunctor.{u}) f₁ f₂).ι := by
  have hf (Z Z' : DiagSet.{u}) (f : Z ⟶ Z') [Mono f] : saturation.{u} sphereInclusions f := by
    rw [← monomorphisms_eq_saturation_sphereInclusions]
    exact ‹Mono f›
  rcases h with h | h
  · refine pushoutObjObj_ι_mem_of_saturation (Functor.curry.obj grayTensorBifunctor.{u})
      (saturation.{u} hornInclusions.{u}) hornInclusions sphereInclusions ?_ h (hf _ _ f₂)
      (hB := fun _ _ _ _ ↦ inferInstance) (hB' := fun _ _ _ _ ↦ inferInstance)
    rintro _ _ _ _ _ _ ⟨h⟩ ⟨U⟩
    obtain ⟨e⟩ := nonempty_arrowIso_pushoutProduct_hornInclusion_sphereInclusion.{u} h U
    exact ((saturation hornInclusions).arrow_mk_iso_iff e).2 (le_saturation _ _ (ofHoms.mk _))
  · refine pushoutObjObj_ι_mem_of_saturation (Functor.curry.obj grayTensorBifunctor.{u})
      (saturation.{u} hornInclusions.{u}) sphereInclusions hornInclusions ?_ (hf _ _ f₁) h
      (hB := fun _ _ _ _ ↦ inferInstance) (hB' := fun _ _ _ _ ↦ inferInstance)
    rintro _ _ _ _ _ _ ⟨U⟩ ⟨h⟩
    obtain ⟨e⟩ := nonempty_arrowIso_pushoutProduct_sphereInclusion_hornInclusion.{u} U h
    exact ((saturation hornInclusions).arrow_mk_iso_iff e).2 (le_saturation _ _ (ofHoms.mk _))

namespace DiagSet.modelCategoryCisinski

open HomotopicalAlgebra

private theorem saturation_hornInclusions_iff {X Y : DiagSet.{u}} (f : X ⟶ Y) [Mono f] :
    saturation.{u} hornInclusions.{u} f ↔ WeakEquivalence f := by
  rw [← monomorphisms_inf_hornWeak_eq_saturation_hornInclusions, hornWeak_eq_infinityEquivalences,
    weakEquivalence_iff]
  exact ⟨fun h => h.2, fun h => ⟨monomorphisms.infer_property f, h⟩⟩

theorem weakEquivalence_pushoutProduct {X₁ Y₁ X₂ Y₂ : DiagSet.{u}} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    [Mono f₁] [Mono f₂] (h : WeakEquivalence f₁ ∨ WeakEquivalence f₂) :
    WeakEquivalence (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj grayTensorBifunctor.{u}) f₁ f₂).ι := by
  have := mono_pushoutProduct f₁ f₂
  rw [← saturation_hornInclusions_iff, ← saturation_hornInclusions_iff] at h
  exact (saturation_hornInclusions_iff _).1 (saturation_hornInclusions_pushoutProduct f₁ f₂ h)

theorem weakEquivalence_ofGray_map_pushoutProduct (f g : Arrow GrayDiagSet.{u})
    [Mono (GrayDiagSet.ofGray.map f.hom)] [Mono (GrayDiagSet.ofGray.map g.hom)]
    (h : WeakEquivalence (GrayDiagSet.ofGray.map f.hom) ∨
      WeakEquivalence (GrayDiagSet.ofGray.map g.hom)) :
    WeakEquivalence (GrayDiagSet.ofGray.map (f □ g).hom) :=
  weakEquivalence_pushoutProduct (GrayDiagSet.ofGray.map f.hom) (GrayDiagSet.ofGray.map g.hom) h

theorem isQuillen_grayTensorLeftAdjunction (X : DiagSet.{u}) :
    (grayTensorLeftAdjunction X).IsQuillen where
  cofibrations_le A B f hf := by
    have : Mono f := hf
    exact (mono_grayTensorBifunctor_map (𝟙 X) f : _)
  trivialCofibrations_le A B f hf := by
    rw [mem_trivialCofibrations_iff] at hf
    obtain ⟨hc, hw⟩ := hf
    have : Mono f := (cofibration_iff f).1 hc
    rw [inverseImage_iff, mem_trivialCofibrations_iff, cofibration_iff]
    refine ⟨mono_grayTensorBifunctor_map (𝟙 X) f, ?_⟩
    have := weakEquivalence_pushoutProduct (initial.to X) f (Or.inr hw)
    have : IsIso (((Functor.curry.obj grayTensorBifunctor.{u}).obj (⊥_ _)).map f) :=
      isIso_of_isInitial (IsInitial.isInitialObj (grayTensorRight A) _ initialIsInitial)
        (IsInitial.isInitialObj (grayTensorRight B) _ initialIsInitial) _
    have : IsIso (Functor.PushoutObjObj.ofHasPushout (Functor.curry.obj grayTensorBifunctor.{u})
        (initial.to X) f).inl :=
      inferInstanceAs (IsIso (pushout.inl (((Functor.curry.obj grayTensorBifunctor.{u}).map
        (initial.to X)).app A) (((Functor.curry.obj grayTensorBifunctor.{u}).obj (⊥_ _)).map f)))
    rw [← (Functor.PushoutObjObj.ofHasPushout _ (initial.to X) f).inl_ι]
    infer_instance

theorem weakEquivalence_grayTensorBifunctor_map_id (X : DiagSet.{u}) {Y Y' : DiagSet.{u}}
    (f : Y ⟶ Y') [WeakEquivalence f] :
    WeakEquivalence (grayTensorBifunctor.map ((𝟙 X, f) : (X, Y) ⟶ (X, Y'))) :=
  (isQuillen_grayTensorLeftAdjunction X).weakEquivalence_map f

theorem isQuillen_grayTensorRightAdjunction (Y : DiagSet.{u}) :
    (grayTensorRightAdjunction Y).IsQuillen where
  cofibrations_le A B f hf := by
    have : Mono f := hf
    exact (mono_grayTensorBifunctor_map f (𝟙 Y) : _)
  trivialCofibrations_le A B f hf := by
    rw [mem_trivialCofibrations_iff] at hf
    obtain ⟨hc, hw⟩ := hf
    have : Mono f := (cofibration_iff f).1 hc
    rw [inverseImage_iff, mem_trivialCofibrations_iff, cofibration_iff]
    refine ⟨mono_grayTensorBifunctor_map f (𝟙 Y), ?_⟩
    have := weakEquivalence_pushoutProduct f (initial.to Y) (Or.inl hw)
    have : IsIso (((Functor.curry.obj grayTensorBifunctor.{u}).map f).app (⊥_ _)) :=
      isIso_of_isInitial (IsInitial.isInitialObj (grayTensorLeft A) _ initialIsInitial)
        (IsInitial.isInitialObj (grayTensorLeft B) _ initialIsInitial) _
    have : IsIso (Functor.PushoutObjObj.ofHasPushout (Functor.curry.obj grayTensorBifunctor.{u})
        f (initial.to Y)).inr :=
      inferInstanceAs (IsIso (pushout.inr (((Functor.curry.obj grayTensorBifunctor.{u}).map
        f).app (⊥_ _)) (((Functor.curry.obj grayTensorBifunctor.{u}).obj A).map (initial.to Y))))
    have e := (Functor.PushoutObjObj.ofHasPushout (Functor.curry.obj grayTensorBifunctor.{u}) f
      (initial.to Y)).inr_ι
    change WeakEquivalence (((Functor.curry.obj grayTensorBifunctor.{u}).map f).app Y)
    rw [← e]
    infer_instance

theorem weakEquivalence_grayTensorBifunctor_map_id_right {X X' : DiagSet.{u}} (f : X ⟶ X')
    (Y : DiagSet.{u}) [WeakEquivalence f] :
    WeakEquivalence (grayTensorBifunctor.map ((f, 𝟙 Y) : (X, Y) ⟶ (X', Y))) :=
  (isQuillen_grayTensorRightAdjunction Y).weakEquivalence_map f

theorem weakEquivalence_grayTensorBifunctor_map {A A' B B' : DiagSet.{u}} (a : A ⟶ A')
    (b : B ⟶ B') [WeakEquivalence a] [WeakEquivalence b] :
    WeakEquivalence (grayTensorBifunctor.map ((a, b) : (A, B) ⟶ (A', B'))) := by
  have e : grayTensorBifunctor.map ((a, b) : (A, B) ⟶ (A', B')) =
      grayTensorBifunctor.map ((a, 𝟙 B) : (A, B) ⟶ (A', B)) ≫
        grayTensorBifunctor.map ((𝟙 A', b) : (A', B) ⟶ (A', B')) := by
    rw [← Functor.map_comp, prod_comp, Category.comp_id, Category.id_comp]
  have := weakEquivalence_grayTensorBifunctor_map_id_right a B
  have := weakEquivalence_grayTensorBifunctor_map_id A' b
  rw [e]
  infer_instance

end DiagSet.modelCategoryCisinski

end Atoms.Diagrammatic
