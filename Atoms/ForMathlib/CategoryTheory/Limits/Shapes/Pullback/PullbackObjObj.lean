import Atoms.ForMathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj
import Mathlib.CategoryTheory.MorphismProperty.Limits

namespace CategoryTheory.Functor.PushoutObjObj

open Limits

variable {C₁ C₂ C₃ D₁ D₂ D₃ : Type*} [Category C₁] [Category C₂] [Category C₃] [Category D₁]
  [Category D₂] [Category D₃] {F : C₁ ⥤ C₂ ⥤ C₃} {F' : D₁ ⥤ D₂ ⥤ D₃} {G₁ : C₁ ⥤ D₁}
  {G₂ : C₂ ⥤ D₂} {G₃ : C₃ ⥤ D₃}
  {X₁ Y₁ : C₁} {f₁ : X₁ ⟶ Y₁} {X₂ Y₂ : C₂} {f₂ : X₂ ⟶ Y₂}

@[simps]
def map (sq : F.PushoutObjObj f₁ f₂)
    (e : F ⋙ (whiskeringRight C₂ C₃ D₃).obj G₃ ≅ G₁ ⋙ F' ⋙ (whiskeringLeft C₂ D₂ D₃).obj G₂)
    [PreservesColimit (span ((F.map f₁).app X₂) ((F.obj X₁).map f₂)) G₃] :
    F'.PushoutObjObj (G₁.map f₁) (G₂.map f₂) where
  pt := G₃.obj sq.pt
  inl := (e.inv.app Y₁).app X₂ ≫ G₃.map sq.inl
  inr := (e.inv.app X₁).app Y₂ ≫ G₃.map sq.inr
  isPushout := (sq.isPushout.map G₃).of_iso ((e.app X₁).app X₂) ((e.app Y₁).app X₂)
    ((e.app X₁).app Y₂) (Iso.refl _)
    (by simpa using congr_app (e.hom.naturality f₁) X₂)
    (by simpa using (e.hom.app X₁).naturality f₂) (by simp) (by simp)
  ι := G₃.map sq.ι ≫ (e.hom.app Y₁).app Y₂
  inl_ι := by
    have h := (e.hom.app Y₁).naturality f₂
    simp only [Functor.comp_obj, whiskeringRight_obj_obj, whiskeringLeft_obj_obj,
      Functor.comp_map] at h
    rw [Category.assoc, ← Functor.map_comp_assoc, sq.inl_ι, h, Iso.inv_hom_id_app_app_assoc]
  inr_ι := by
    have h := congr_app (e.hom.naturality f₁) Y₂
    simp only [Functor.comp_obj, whiskeringRight_obj_obj, whiskeringLeft_obj_obj,
      NatTrans.comp_app, Functor.comp_map, whiskeringRight_obj_map, Functor.whiskerRight_app,
      whiskeringLeft_obj_map, Functor.whiskerLeft_app] at h
    rw [Category.assoc, ← Functor.map_comp_assoc, sq.inr_ι, h, Iso.inv_hom_id_app_app_assoc]

noncomputable def mapArrowIso (sq : F.PushoutObjObj f₁ f₂)
    (sq' : F'.PushoutObjObj (G₁.map f₁) (G₂.map f₂))
    (e : F ⋙ (whiskeringRight C₂ C₃ D₃).obj G₃ ≅ G₁ ⋙ F' ⋙ (whiskeringLeft C₂ D₂ D₃).obj G₂)
    [PreservesColimit (span ((F.map f₁).app X₂) ((F.obj X₁).map f₂)) G₃] :
    G₃.mapArrow.obj (Arrow.mk sq.ι) ≅ Arrow.mk sq'.ι :=
  (Arrow.isoMk (Iso.refl _) ((e.app Y₁).app Y₂) (Category.id_comp _) :
    G₃.mapArrow.obj (Arrow.mk sq.ι) ≅ Arrow.mk (sq.map e).ι) ≪≫
    ι_iso_of_iso_left (f₁ := Arrow.mk (G₁.map f₁)) (f₂ := Arrow.mk (G₂.map f₂)) (sq.map e) sq'
      (Iso.refl _)

def ofArrowIsoRight (sq : F.PushoutObjObj f₁ f₂) {X₂' Y₂' : C₂} {f₂' : X₂' ⟶ Y₂'}
    (α : Arrow.mk f₂ ≅ Arrow.mk f₂') : F.PushoutObjObj f₁ f₂' where
  pt := sq.pt
  inl := (F.obj Y₁).map α.inv.left ≫ sq.inl
  inr := (F.obj X₁).map α.inv.right ≫ sq.inr
  isPushout := sq.isPushout.of_iso ((F.obj X₁).mapIso (Comma.leftIso α))
    ((F.obj Y₁).mapIso (Comma.leftIso α)) ((F.obj X₁).mapIso (Comma.rightIso α))
    (Iso.refl _) ((F.map f₁).naturality α.hom.left).symm
    (((F.obj X₁).map_comp _ _).symm.trans ((congrArg (F.obj X₁).map (Arrow.w α.hom).symm).trans
      ((F.obj X₁).map_comp _ _)))
    (by
      rw [Iso.refl_hom, Category.comp_id, ← Category.assoc]
      exact (Category.id_comp _).symm.trans
        (congrArg (· ≫ sq.inl) ((F.obj Y₁).mapIso (Comma.leftIso α)).hom_inv_id.symm))
    (by
      rw [Iso.refl_hom, Category.comp_id, ← Category.assoc]
      exact (Category.id_comp _).symm.trans
        (congrArg (· ≫ sq.inr) ((F.obj X₁).mapIso (Comma.rightIso α)).hom_inv_id.symm))
  ι := sq.ι ≫ (F.obj Y₁).map α.hom.right
  inl_ι := by
    have h := Arrow.w α.inv
    simp only [Arrow.mk_hom] at h
    rw [Category.assoc, sq.inl_ι_assoc, ← Functor.map_comp, ← Functor.map_comp, reassoc_of% h,
      Arrow.inv_hom_id_right, Category.comp_id]
  inr_ι := by
    rw [Category.assoc, sq.inr_ι_assoc, ← NatTrans.naturality, ← Functor.map_comp_assoc,
      Arrow.inv_hom_id_right]
    exact (congrArg (· ≫ (F.map f₁).app Y₂') ((F.obj X₁).map_id Y₂')).trans (Category.id_comp _)

section Comp

variable {F : C₁ ⥤ C₂ ⥤ C₃} {Z₁ : C₁} {g : Y₁ ⟶ Z₁} {j : X₂ ⟶ Y₂}

noncomputable def compLeftMap (sfg : F.PushoutObjObj (f₁ ≫ g) j) (sg : F.PushoutObjObj g j) :
    sfg.pt ⟶ sg.pt :=
  sfg.isPushout.desc sg.inl ((F.map f₁).app Y₂ ≫ sg.inr) (by
    rw [Functor.map_comp, NatTrans.comp_app, Category.assoc, sg.isPushout.w,
      ← NatTrans.naturality_assoc])

@[reassoc]
theorem compLeftMap_ι (sfg : F.PushoutObjObj (f₁ ≫ g) j) (sg : F.PushoutObjObj g j) :
    compLeftMap sfg sg ≫ sg.ι = sfg.ι := by
  refine sfg.isPushout.hom_ext ?_ ?_
  · rw [compLeftMap, IsPushout.inl_desc_assoc, sg.inl_ι, sfg.inl_ι]
  · rw [compLeftMap, IsPushout.inr_desc_assoc, Category.assoc, sg.inr_ι, sfg.inr_ι,
      Functor.map_comp, NatTrans.comp_app]

theorem isPushout_compLeftMap (sf : F.PushoutObjObj f₁ j) (sfg : F.PushoutObjObj (f₁ ≫ g) j)
    (sg : F.PushoutObjObj g j) :
    IsPushout (sf.isPushout.desc ((F.map g).app X₂ ≫ sfg.inl) sfg.inr (by
        rw [← Category.assoc, ← NatTrans.comp_app, ← Functor.map_comp, sfg.isPushout.w]))
      sf.ι (compLeftMap sfg sg) sg.inr := by
  set φ := sf.isPushout.desc ((F.map g).app X₂ ≫ sfg.inl) sfg.inr (by
    rw [← Category.assoc, ← NatTrans.comp_app, ← Functor.map_comp, sfg.isPushout.w])
  have hB : IsPushout ((F.map g).app X₂) sf.inl sfg.inl φ := by
    refine (sf.isPushout.paste_horiz_iff (sf.isPushout.inl_desc _ _ _).symm).1 ?_
    have h := sfg.isPushout
    rw [Functor.map_comp, NatTrans.comp_app] at h
    rwa [sf.isPushout.inr_desc]
  refine (hB.paste_vert_iff ?_).1 ?_
  · refine sf.isPushout.hom_ext ?_ ?_
    · rw [sf.isPushout.inl_desc_assoc, Category.assoc, compLeftMap, IsPushout.inl_desc,
        sf.inl_ι_assoc, ← sg.isPushout.w]
    · rw [sf.isPushout.inr_desc_assoc, compLeftMap, IsPushout.inr_desc, sf.inr_ι_assoc]
  · rw [sf.inl_ι, compLeftMap, IsPushout.inl_desc]
    exact sg.isPushout

end Comp

section MapIso

variable {D : Type*} [Category D]

theorem isIso_map_ι_of_left (sq : F.PushoutObjObj f₁ f₂) (G : C₃ ⥤ D)
    [PreservesColimit (span ((F.map f₁).app X₂) ((F.obj X₁).map f₂)) G]
    (h₁ : IsIso (G.map ((F.map f₁).app X₂))) (h₂ : IsIso (G.map ((F.map f₁).app Y₂))) :
    IsIso (G.map sq.ι) :=
  G.isIso_map_of_isPushout sq.isPushout h₁ sq.ι (sq.inr_ι ▸ h₂)

theorem isIso_map_ι_of_right (sq : F.PushoutObjObj f₁ f₂) (G : C₃ ⥤ D)
    [PreservesColimit (span ((F.map f₁).app X₂) ((F.obj X₁).map f₂)) G]
    (h₁ : IsIso (G.map ((F.obj X₁).map f₂))) (h₂ : IsIso (G.map ((F.obj Y₁).map f₂))) :
    IsIso (G.map sq.ι) :=
  G.isIso_map_of_isPushout' sq.isPushout h₁ sq.ι (sq.inl_ι ▸ h₂)

end MapIso

end CategoryTheory.Functor.PushoutObjObj

namespace CategoryTheory.MorphismProperty

variable {C₁ C₂ C₃ : Type*} [Category C₁] [Category C₂] [Category C₃] {F : C₁ ⥤ C₂ ⥤ C₃}
  {X₁ Y₁ Z₁ : C₁} {f : X₁ ⟶ Y₁} {g : Y₁ ⟶ Z₁} {X₂ Y₂ : C₂} {j : X₂ ⟶ Y₂}

theorem pushoutObjObj_ι_comp_left_mem {P W : MorphismProperty C₃} [P.IsStableUnderCobaseChange]
    [W.IsStableUnderComposition] (hPW : P ≤ W) (sf : F.PushoutObjObj f j)
    (sfg : F.PushoutObjObj (f ≫ g) j) (sg : F.PushoutObjObj g j) (hf : P sf.ι) (hg : W sg.ι) :
    W sfg.ι := by
  rw [← Functor.PushoutObjObj.compLeftMap_ι sfg sg]
  exact W.comp_mem _ _ (hPW _ (P.of_isPushout
    (Functor.PushoutObjObj.isPushout_compLeftMap sf sfg sg) hf)) hg

end CategoryTheory.MorphismProperty
