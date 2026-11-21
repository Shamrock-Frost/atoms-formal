import Atoms.Diagrammatic.Marked.CylinderTensor

open CategoryTheory Limits Atoms.Homotopical

universe u

namespace Atoms.Diagrammatic
open HomotopicalAlgebra

private theorem endpoint_comm (pseudo ε : Bool) (K : MarkedDiagSet.{u}) :
    (markedExactCylinder.endpoint ε).app K ≫ (markedCylinderIsoTensorLeft pseudo).hom.app K =
      (markedTensorLeftUnitor pseudo K).symm.hom ≫
        ((Functor.curry.obj (markedTensorBifunctor pseudo)).map (markedIntervalVertex ε)).app K :=
  markedExactCylinder_endpoint_app_comp_markedCylinderIsoTensorLeft_hom_app pseudo ε K

private theorem unitor_inv_comm (pseudo : Bool) {K X : MarkedDiagSet.{u}} (i : K ⟶ X) :
    i ≫ (markedTensorLeftUnitor pseudo X).inv =
      (markedTensorLeftUnitor pseudo K).inv ≫ markedTensorMap pseudo (𝟙 markedTensorUnit) i := by
  rw [Iso.eq_inv_comp, ← Category.assoc, ← markedTensorLeftUnitor_naturality, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

noncomputable def markedEndpointBoxPushoutObjObj (pseudo ε : Bool) {K X : MarkedDiagSet.{u}}
    (i : K ⟶ X) :
    (Functor.curry.obj (markedTensorBifunctor pseudo)).PushoutObjObj
      (markedIntervalVertex ε) i where
  pt := markedExactCylinder.endpointBoxSource ε i
  inl := (markedCylinderIsoTensorLeft pseudo).inv.app K ≫ pushout.inl _ _
  inr := (markedTensorLeftUnitor pseudo X).hom ≫ pushout.inr _ _
  isPushout := (IsPushout.of_hasPushout ((markedExactCylinder.endpoint ε).app K) i).of_iso
    (markedTensorLeftUnitor pseudo K).symm ((markedCylinderIsoTensorLeft pseudo).app K)
    (markedTensorLeftUnitor pseudo X).symm (Iso.refl _) (endpoint_comm pseudo ε K)
    (unitor_inv_comm pseudo i)
    ((Category.comp_id _).trans
      ((markedCylinderIsoTensorLeft pseudo).hom_inv_id_app_assoc K _).symm)
    ((Category.comp_id _).trans ((markedTensorLeftUnitor pseudo X).inv_hom_id_assoc _).symm)
  ι := markedExactCylinder.endpointBox ε i ≫ (markedCylinderIsoTensorLeft pseudo).hom.app X
  inl_ι := (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
    (markedExactCylinder.inl_endpointBox_assoc ε i _)).trans (NatIso.naturality_1 _ i))
  inr_ι := (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
    ((markedExactCylinder.inr_endpointBox_assoc ε i _).trans (endpoint_comm pseudo ε X))).trans
      ((markedTensorLeftUnitor pseudo X).hom_inv_id_assoc _))

theorem markedEndpointBoxPushoutObjObj_pt (pseudo ε : Bool) {K X : MarkedDiagSet.{u}}
    (i : K ⟶ X) :
    (markedEndpointBoxPushoutObjObj pseudo ε i).pt = markedExactCylinder.endpointBoxSource ε i :=
  rfl

theorem markedEndpointBoxPushoutObjObj_ι (pseudo ε : Bool) {K X : MarkedDiagSet.{u}}
    (i : K ⟶ X) :
    (markedEndpointBoxPushoutObjObj pseudo ε i).ι =
      markedExactCylinder.endpointBox ε i ≫ (markedCylinderIsoTensorLeft pseudo).hom.app X :=
  rfl

noncomputable def markedEndpointBoxArrowIso (pseudo ε : Bool) {K X : MarkedDiagSet.{u}}
    (i : K ⟶ X) :
    Arrow.mk (markedExactCylinder.endpointBox ε i) ≅
      Arrow.mk (Functor.PushoutObjObj.ofHasPushout
        (Functor.curry.obj (markedTensorBifunctor pseudo)) (markedIntervalVertex ε) i).ι :=
  Arrow.isoMk (g := Arrow.mk (markedEndpointBoxPushoutObjObj pseudo ε i).ι) (Iso.refl _)
      ((markedCylinderIsoTensorLeft pseudo).app X)
      (Category.id_comp _).symm ≪≫
    Functor.PushoutObjObj.ι_iso_of_iso_left (f₁ := Arrow.mk (markedIntervalVertex ε))
      (f₂ := Arrow.mk i) (markedEndpointBoxPushoutObjObj pseudo ε i) _ (Iso.refl _)

noncomputable def markedIntervalBoundaryι :
    markedTensorUnit.{u} ⨿ markedTensorUnit.{u} ⟶ markedInterval.{u} :=
  coprod.desc (markedIntervalVertex false) (markedIntervalVertex true)

private noncomputable def boundaryTensorIso (pseudo : Bool) (K : MarkedDiagSet.{u}) :
    K ⨿ K ≅ ((Functor.curry.obj (markedTensorBifunctor pseudo)).obj
      (markedTensorUnit.{u} ⨿ markedTensorUnit.{u})).obj K :=
  coprod.mapIso (markedTensorLeftUnitor pseudo K).symm (markedTensorLeftUnitor pseudo K).symm ≪≫
    PreservesColimitPair.iso (tensorRight pseudo K) _ _

private theorem inl_boundaryTensorIso_hom (pseudo : Bool) (K : MarkedDiagSet.{u}) :
    coprod.inl ≫ (boundaryTensorIso pseudo K).hom = (markedTensorLeftUnitor pseudo K).inv ≫
      ((Functor.curry.obj (markedTensorBifunctor pseudo)).map coprod.inl).app K :=
  (coprod.inl_map_assoc _ _ _).trans (congrArg (_ ≫ ·) (coprod.inl_desc _ _))

private theorem inr_boundaryTensorIso_hom (pseudo : Bool) (K : MarkedDiagSet.{u}) :
    coprod.inr ≫ (boundaryTensorIso pseudo K).hom = (markedTensorLeftUnitor pseudo K).inv ≫
      ((Functor.curry.obj (markedTensorBifunctor pseudo)).map coprod.inr).app K :=
  (coprod.inr_map_assoc _ _ _).trans (congrArg (_ ≫ ·) (coprod.inr_desc _ _))

private theorem endpoints_comm (pseudo : Bool) (K : MarkedDiagSet.{u}) :
    markedExactCylinder.endpoints K ≫ (markedCylinderIsoTensorLeft pseudo).hom.app K =
      (boundaryTensorIso pseudo K).hom ≫
        ((Functor.curry.obj (markedTensorBifunctor pseudo)).map markedIntervalBoundaryι).app K := by
  let F := Functor.curry.obj (markedTensorBifunctor.{u} pseudo)
  have hl : (F.map coprod.inl).app K ≫ (F.map markedIntervalBoundaryι).app K =
      (F.map (markedIntervalVertex false)).app K :=
    (NatTrans.comp_app _ _ K).symm.trans (congrArg (fun f => NatTrans.app f K)
      ((F.map_comp _ _).symm.trans (congrArg F.map (coprod.inl_desc _ _))))
  have hr : (F.map coprod.inr).app K ≫ (F.map markedIntervalBoundaryι).app K =
      (F.map (markedIntervalVertex true)).app K :=
    (NatTrans.comp_app _ _ K).symm.trans (congrArg (fun f => NatTrans.app f K)
      ((F.map_comp _ _).symm.trans (congrArg F.map (coprod.inr_desc _ _))))
  refine coprod.hom_ext ?_ ?_
  · exact ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
      (markedExactCylinder.inl_endpoints K)).trans (endpoint_comm pseudo false K))).trans
      ((congrArg (_ ≫ ·) hl.symm).trans (((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ _) (inl_boundaryTensorIso_hom pseudo K).symm)).trans
          (Category.assoc _ _ _)))
  · exact ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
      (markedExactCylinder.inr_endpoints K)).trans (endpoint_comm pseudo true K))).trans
      ((congrArg (_ ≫ ·) hr.symm).trans (((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ _) (inr_boundaryTensorIso_hom pseudo K).symm)).trans
          (Category.assoc _ _ _)))

private theorem boundaryTensorIso_naturality (pseudo : Bool) {K X : MarkedDiagSet.{u}}
    (i : K ⟶ X) :
    coprod.map i i ≫ (boundaryTensorIso pseudo X).hom =
      (boundaryTensorIso pseudo K).hom ≫ ((Functor.curry.obj (markedTensorBifunctor pseudo)).obj
        (markedTensorUnit.{u} ⨿ markedTensorUnit.{u})).map i := by
  let F := Functor.curry.obj (markedTensorBifunctor.{u} pseudo)
  have key : ∀ c : markedTensorUnit.{u} ⟶ markedTensorUnit.{u} ⨿ markedTensorUnit.{u},
      i ≫ (markedTensorLeftUnitor pseudo X).inv ≫ (F.map c).app X =
        (markedTensorLeftUnitor pseudo K).inv ≫ (F.map c).app K ≫ (F.obj _).map i := fun c =>
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (unitor_inv_comm pseudo i)).trans
      ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((F.map c).naturality i))))
  refine coprod.hom_ext ?_ ?_
  · exact (coprod.inl_map_assoc _ _ _).trans ((congrArg (_ ≫ ·)
      (inl_boundaryTensorIso_hom pseudo X)).trans ((key _).trans (((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ _) (inl_boundaryTensorIso_hom pseudo K).symm)).trans
          (Category.assoc _ _ _))))
  · exact (coprod.inr_map_assoc _ _ _).trans ((congrArg (_ ≫ ·)
      (inr_boundaryTensorIso_hom pseudo X)).trans ((key _).trans (((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ _) (inr_boundaryTensorIso_hom pseudo K).symm)).trans
          (Category.assoc _ _ _))))

private noncomputable def markedBothBoxPushoutObjObj (pseudo : Bool) {K X : MarkedDiagSet.{u}}
    (i : K ⟶ X) :
    (Functor.curry.obj (markedTensorBifunctor pseudo)).PushoutObjObj markedIntervalBoundaryι i where
  pt := markedExactCylinder.bothBoxSource i
  inl := (markedCylinderIsoTensorLeft pseudo).inv.app K ≫ pushout.inl _ _
  inr := (boundaryTensorIso pseudo X).inv ≫ pushout.inr _ _
  isPushout := (IsPushout.of_hasPushout (markedExactCylinder.endpoints K) (coprod.map i i)).of_iso
    (boundaryTensorIso pseudo K) ((markedCylinderIsoTensorLeft pseudo).app K)
    (boundaryTensorIso pseudo X) (Iso.refl _) (endpoints_comm pseudo K)
    (boundaryTensorIso_naturality pseudo i)
    ((Category.comp_id _).trans
      ((markedCylinderIsoTensorLeft pseudo).hom_inv_id_app_assoc K _).symm)
    ((Category.comp_id _).trans ((boundaryTensorIso pseudo X).hom_inv_id_assoc _).symm)
  ι := markedExactCylinder.bothBox i ≫ (markedCylinderIsoTensorLeft pseudo).hom.app X
  inl_ι := (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
    (markedExactCylinder.inl_bothBox_assoc i _)).trans (NatIso.naturality_1 _ i))
  inr_ι := (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
    ((markedExactCylinder.inr_bothBox_assoc i _).trans (endpoints_comm pseudo X))).trans
      ((boundaryTensorIso pseudo X).inv_hom_id_assoc _))

noncomputable def markedBothBoxArrowIso (pseudo : Bool) {K X : MarkedDiagSet.{u}} (i : K ⟶ X) :
    Arrow.mk (markedExactCylinder.bothBox i) ≅
      Arrow.mk (Functor.PushoutObjObj.ofHasPushout
        (Functor.curry.obj (markedTensorBifunctor pseudo)) markedIntervalBoundaryι i).ι :=
  Arrow.isoMk (g := Arrow.mk (markedBothBoxPushoutObjObj pseudo i).ι) (Iso.refl _)
      ((markedCylinderIsoTensorLeft pseudo).app X) (Category.id_comp _).symm ≪≫
    Functor.PushoutObjObj.ι_iso_of_iso_left (f₁ := Arrow.mk markedIntervalBoundaryι)
      (f₂ := Arrow.mk i) (markedBothBoxPushoutObjObj pseudo i) _ (Iso.refl _)

private theorem grayToPseudo_markedInterval_eq (X : MarkedDiagSet.{u}) :
    grayToPseudo markedInterval.{u} X =
      (markedCylinderIsoTensorLeft false).inv.app X ≫
        (markedCylinderIsoTensorLeft true).hom.app X := by
  refine MarkedPresheaf.hom_ext ((forget_map_grayToPseudo _ _).trans ?_)
  have h : MarkedPresheaf.forget.map ((markedCylinderIsoTensorLeft true).hom.app X) =
      MarkedPresheaf.forget.map ((markedCylinderIsoTensorLeft false).hom.app X) := rfl
  refine Eq.symm ((MarkedPresheaf.forget.map_comp _ _).trans ?_)
  exact (congrArg (_ ≫ ·) h).trans ((MarkedPresheaf.forget.map_comp _ _).symm.trans
    ((congrArg MarkedPresheaf.forget.map
      ((markedCylinderIsoTensorLeft false).inv_hom_id_app X)).trans
      (MarkedPresheaf.forget.map_id _)))

theorem isIso_grayToPseudo_markedInterval (X : MarkedDiagSet.{u}) :
    IsIso (grayToPseudo markedInterval.{u} X) := by
  rw [grayToPseudo_markedInterval_eq]
  exact (((markedCylinderIsoTensorLeft false).app X).symm ≪≫
    (markedCylinderIsoTensorLeft true).app X).isIso_hom

end Atoms.Diagrammatic
