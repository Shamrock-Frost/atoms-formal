import Atoms.Diagrammatic.GrayTensor.Realization
import Atoms.ForMathlib.CategoryTheory.Adhesive.Basic
import Atoms.ForMathlib.CategoryTheory.MorphismProperty.Leibniz
import Atoms.ForMathlib.CategoryTheory.Subfunctor.Colimits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj

open CategoryTheory Limits Opposite MorphismProperty Atoms.Molecule Atoms.Molecule.OGP
  Atoms.Shape

universe u

namespace Atoms.Diagrammatic

theorem injective_grayProductRDCMap {P P' Q Q' : RDCpx.{0}} {f : P ⟶ P'} {g : Q ⟶ Q'}
    (hf : Function.Injective (ConcreteCategory.hom f.hom))
    (hg : Function.Injective (ConcreteCategory.hom g.hom)) :
    Function.Injective (ConcreteCategory.hom (grayProductRDCMap f g).hom) := fun _ _ h =>
  Prod.ext (hf (congrArg Prod.fst h)) (hg (congrArg Prod.snd h))

section

variable (P Q : RDCpx.{0}) (S : LowerSet P.obj.toOGP) (T : LowerSet Q.obj.toOGP)

private theorem isPullback_realize_grayProductRDCMap :
    IsPullback
      (realize.{u}.map (grayProductRDCMap (P.restrictIncl S) (𝟙 (Q.restrict T))))
      (realize.map (grayProductRDCMap (𝟙 (P.restrict S)) (Q.restrictIncl T)))
      (realize.map (grayProductRDCMap (𝟙 P) (Q.restrictIncl T)))
      (realize.map (grayProductRDCMap (P.restrictIncl S) (𝟙 Q))) := by
  refine IsPullback.of_forall_isPullback_app fun A => ?_
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · rw [← NatTrans.comp_app, ← NatTrans.comp_app, ← realize.map_comp, ← realize.map_comp,
      grayProductRDCMap_comp, grayProductRDCMap_comp, Category.comp_id, Category.id_comp,
      Category.id_comp, Category.comp_id]
  · rintro ⟨x⟩ ⟨y⟩ ⟨h, -⟩
    refine ULift.ext _ _ (WideSubcategory.hom_ext _ (ConcreteCategory.hom_ext _ _ fun t => ?_))
    have h' := congrArg (fun k : atomToRDCpx.obj A.unop ⟶ grayProductRDC P (Q.restrict T) =>
      ConcreteCategory.hom k.hom t)
      (ULift.up_inj.1 h : x ≫ grayProductRDCMap (P.restrictIncl S) (𝟙 _) =
        y ≫ grayProductRDCMap (P.restrictIncl S) (𝟙 _))
    exact injective_grayProductRDCMap (Subtype.val_injective) (fun _ _ h => h) h'
  · rintro ⟨x₂⟩ ⟨x₃⟩ h
    have h' : ∀ t, (ConcreteCategory.hom x₂.hom t).1 = (ConcreteCategory.hom x₃.hom t).1.1 ∧
        (ConcreteCategory.hom x₂.hom t).2.1 = (ConcreteCategory.hom x₃.hom t).2 := fun t =>
      Prod.mk.inj (congrArg (fun k : atomToRDCpx.obj A.unop ⟶ grayProductRDC P Q =>
        ConcreteCategory.hom k.hom t)
        (ULift.up_inj.1 h : x₂ ≫ grayProductRDCMap (𝟙 P) (Q.restrictIncl T) =
          x₃ ≫ grayProductRDCMap (P.restrictIncl S) (𝟙 Q)))
    let x₁ : atomToRDCpx.obj A.unop ⟶ grayProductRDC (P.restrict S) (Q.restrict T) :=
      RDCpx.codRestrict (x₃ ≫ grayProductRDCMap (P.restrictIncl S) (𝟙 Q)) (S ×ˢ T)
          (fun t => ⟨(ConcreteCategory.hom x₃.hom t).1.2,
            (h' t).2 ▸ (ConcreteCategory.hom x₂.hom t).2.2⟩) ≫
        (RDCpx.isoOfIso (grayProductRestrictIso S T)).hom
    refine ⟨ULift.up x₁, ULift.ext _ _ (WideSubcategory.hom_ext _
      (ConcreteCategory.hom_ext _ _ fun t => ?_)), ULift.ext _ _ (WideSubcategory.hom_ext _
      (ConcreteCategory.hom_ext _ _ fun t => rfl))⟩
    exact Prod.ext (h' t).1.symm (Subtype.ext (h' t).2.symm)

private theorem isPullback_grayTensor_realize_restrictIncl :
    IsPullback
      (((Functor.curry.obj grayTensorBifunctor.{u}).map (realize.map (P.restrictIncl S))).app
        (realize.obj (Q.restrict T)))
      (((Functor.curry.obj grayTensorBifunctor.{u}).obj (realize.obj (P.restrict S))).map
        (realize.map (Q.restrictIncl T)))
      (((Functor.curry.obj grayTensorBifunctor.{u}).obj (realize.obj P)).map
        (realize.map (Q.restrictIncl T)))
      (((Functor.curry.obj grayTensorBifunctor.{u}).map (realize.map (P.restrictIncl S))).app
        (realize.obj Q)) := by
  refine (isPullback_realize_grayProductRDCMap.{u} P Q S T).of_iso
    (realizeGrayProductIso _ _) (realizeGrayProductIso _ _) (realizeGrayProductIso _ _)
    (realizeGrayProductIso _ _) ?_ ?_ ?_ ?_ <;>
  · refine (realize_map_grayProductRDCMap_comp_realizeGrayProductIso_hom _ _).trans ?_
    rw [realize.map_id]
    rfl

private theorem grayTensor_map_realize_restrictIncl_right :
    ((Functor.curry.obj grayTensorBifunctor.{u}).obj (realize.obj P)).map
        (realize.map (Q.restrictIncl T)) =
      (realizeGrayProductIso P (Q.restrict T)).inv ≫
        realize.map (grayProductRDCMap (𝟙 P) (Q.restrictIncl T)) ≫
          (realizeGrayProductIso P Q).hom := by
  rw [realize_map_grayProductRDCMap_comp_realizeGrayProductIso_hom, Iso.inv_hom_id_assoc,
    realize.map_id]
  rfl

private theorem grayTensor_map_realize_restrictIncl_left :
    ((Functor.curry.obj grayTensorBifunctor.{u}).map (realize.map (P.restrictIncl S))).app
        (realize.obj Q) =
      (realizeGrayProductIso (P.restrict S) Q).inv ≫
        realize.map (grayProductRDCMap (P.restrictIncl S) (𝟙 Q)) ≫
          (realizeGrayProductIso P Q).hom := by
  rw [realize_map_grayProductRDCMap_comp_realizeGrayProductIso_hom, Iso.inv_hom_id_assoc,
    realize.map_id]
  rfl

theorem mono_pushoutProduct_realize_restrictIncl :
    Mono (Functor.PushoutObjObj.ofHasPushout (Functor.curry.obj grayTensorBifunctor.{u})
      (realize.map (P.restrictIncl S)) (realize.map (Q.restrictIncl T))).ι := by
  have : Mono (realize.{u}.map (grayProductRDCMap (𝟙 P) (Q.restrictIncl T))) :=
    mono_realize_map _ (injective_grayProductRDCMap (fun _ _ h => h) Subtype.val_injective)
  have : Mono (realize.{u}.map (grayProductRDCMap (P.restrictIncl S) (𝟙 Q))) :=
    mono_realize_map _ (injective_grayProductRDCMap Subtype.val_injective (fun _ _ h => h))
  have ha : Mono (((Functor.curry.obj grayTensorBifunctor.{u}).obj (realize.obj P)).map
      (realize.map (Q.restrictIncl T))) := by
    rw [grayTensor_map_realize_restrictIncl_right]
    infer_instance
  have hb : Mono (((Functor.curry.obj grayTensorBifunctor.{u}).map
      (realize.map (P.restrictIncl S))).app (realize.obj Q)) := by
    rw [grayTensor_map_realize_restrictIncl_left]
    infer_instance
  exact HasEffectiveUnions.mono_pushoutDesc (isPullback_grayTensor_realize_restrictIncl.{u} P Q S T)

theorem range_pushoutProduct_realize_restrictIncl :
    Subfunctor.range ((Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj grayTensorBifunctor.{u})
      (realize.map (P.restrictIncl S)) (realize.map (Q.restrictIncl T))).ι ≫
        (realizeGrayProductIso P Q).inv) =
      realizeSubset (grayProductRDC P Q)
        (S ×ˢ (⊤ : LowerSet Q.obj.toOGP) ⊔ (⊤ : LowerSet P.obj.toOGP) ×ˢ T) := by
  have hiso {X Y Z : DiagSet.{u}} (e : X ≅ Y) (g : Y ⟶ Z) :
      Subfunctor.range (e.hom ≫ g) = Subfunctor.range g := by
    refine le_antisymm (Subfunctor.range_comp_le _ _) ?_
    conv_lhs => rw [← Iso.inv_hom_id_assoc e g]
    exact Subfunctor.range_comp_le _ _
  have hfac {X Y Z : RDCpx.{0}} (g : X ⟶ Z) (g' : Y ⟶ Z) (k : X ⟶ Y) (k' : Y ⟶ X)
      (hk : k ≫ g' = g) (hk' : k' ≫ g = g') :
      Subfunctor.range (realize.{u}.map g) = Subfunctor.range (realize.{u}.map g') :=
    le_antisymm (hk ▸ realize.map_comp k g' ▸ Subfunctor.range_comp_le _ _)
      (hk' ▸ realize.map_comp k' g ▸ Subfunctor.range_comp_le _ _)
  have hP : Subfunctor.range (realize.{u}.map (grayProductRDCMap (P.restrictIncl S) (𝟙 Q))) =
      realizeSubset (grayProductRDC P Q) (S ×ˢ (⊤ : LowerSet Q.obj.toOGP)) := by
    rw [← range_realize_map_grayProductRDCMap_restrictIncl]
    exact hfac _ _ (grayProductRDCMap (𝟙 _) (RDCpx.codRestrict (𝟙 Q) ⊤ fun _ => LowerSet.mem_top))
      (grayProductRDCMap (𝟙 _) (Q.restrictIncl ⊤)) (by rw [grayProductRDCMap_comp,
        Category.id_comp, RDCpx.codRestrict_restrictIncl]) (by rw [grayProductRDCMap_comp,
        Category.id_comp, Category.comp_id])
  have hQ : Subfunctor.range (realize.{u}.map (grayProductRDCMap (𝟙 P) (Q.restrictIncl T))) =
      realizeSubset (grayProductRDC P Q) ((⊤ : LowerSet P.obj.toOGP) ×ˢ T) := by
    rw [← range_realize_map_grayProductRDCMap_restrictIncl]
    exact hfac _ _ (grayProductRDCMap (RDCpx.codRestrict (𝟙 P) ⊤ fun _ => LowerSet.mem_top) (𝟙 _))
      (grayProductRDCMap (P.restrictIncl ⊤) (𝟙 _)) (by rw [grayProductRDCMap_comp,
        Category.id_comp, RDCpx.codRestrict_restrictIncl]) (by rw [grayProductRDCMap_comp,
        Category.id_comp, Category.comp_id])
  refine (Subfunctor.range_pushout_desc_comp _ _ _ _ _ _).trans ?_
  rw [grayTensor_map_realize_restrictIncl_right, grayTensor_map_realize_restrictIncl_left,
    Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.assoc,
    Category.assoc, Iso.hom_inv_id, Category.comp_id, ← Iso.symm_hom, hiso, ← Iso.symm_hom,
    hiso, hP, hQ]
  exact (sup_comm _ _).trans (realizeSubset_union _ _ _).symm

end

theorem range_pushoutProduct_realize_hornSet_bdryFull {V U : Atom} {α : Bool}
    {W : LowerSet V.ogp} (hW : V.ogp.IsRewritableSubmolecule W (V.ogp.bdry ⊤ α)) :
    Subfunctor.range ((Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj grayTensorBifunctor.{u})
      (realize.map ((atomToRDCpx.obj V).restrictIncl
        (hW.hornSet V.isAtom.isMoleculeIn V.isAtom.isRound)))
      (realize.map ((atomToRDCpx.obj U).restrictIncl (U.ogp.bdryFull ⊤)))).ι ≫
        (realizeGrayProductIso _ _).inv) =
      realizeSubset (grayProductRDC (atomToRDCpx.obj V) (atomToRDCpx.obj U))
        ((isRewritableSubmolecule_prod_left V.isAtom U.isAtom hW).hornSet
          (isMolecule_grayProduct V.isAtom.isMoleculeIn U.isAtom.isMoleculeIn)
          (isAtom_grayProduct V.isAtom U.isAtom).isRound) := by
  rw [range_pushoutProduct_realize_restrictIncl]
  exact congrArg (realizeSubset _) (hornSet_prod_left V.isAtom U.isAtom hW).symm

theorem range_pushoutProduct_realize_bdryFull_hornSet {U V : Atom} {α : Bool}
    {W : LowerSet V.ogp} (hW : V.ogp.IsRewritableSubmolecule W (V.ogp.bdry ⊤ α)) :
    Subfunctor.range ((Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj grayTensorBifunctor.{u})
      (realize.map ((atomToRDCpx.obj U).restrictIncl (U.ogp.bdryFull ⊤)))
      (realize.map ((atomToRDCpx.obj V).restrictIncl
        (hW.hornSet V.isAtom.isMoleculeIn V.isAtom.isRound)))).ι ≫
        (realizeGrayProductIso _ _).inv) =
      realizeSubset (grayProductRDC (atomToRDCpx.obj U) (atomToRDCpx.obj V))
        ((isRewritableSubmolecule_prod_right U.isAtom U.krullDim_eq_dimension V.isAtom hW).hornSet
          (isMolecule_grayProduct U.isAtom.isMoleculeIn V.isAtom.isMoleculeIn)
          (isAtom_grayProduct U.isAtom V.isAtom).isRound) := by
  rw [range_pushoutProduct_realize_restrictIncl]
  exact congrArg (realizeSubset _)
    (hornSet_prod_right U.isAtom U.krullDim_eq_dimension V.isAtom hW).symm

theorem nonempty_arrowIso_realize_restrictIncl_bdryFull (U : Atom) :
    Nonempty (Arrow.mk (realize.{u}.map ((atomToRDCpx.obj U).restrictIncl (U.ogp.bdryFull ⊤))) ≅
      Arrow.mk (sphereInclusion.{u} U)) := by
  have key : ∀ G : Subfunctor (ball.{u} U), G = Homotopical.EZCategory.uliftBoundary.{u} U →
      Nonempty (Arrow.mk G.ι ≅ Arrow.mk (sphereInclusion.{u} U)) := by
    rintro G rfl
    exact ⟨Iso.refl _⟩
  obtain ⟨e⟩ := key _ (closedSubpresheaf_univ_erase_top U)
  let e' : Arrow.mk (realize.{u}.map ((atomToRDCpx.obj U).restrictIncl (U.ogp.bdryFull ⊤))) ≅
      Arrow.mk (closedSubpresheaf.{u} U (U.ogp.bdryFull ⊤)).ι :=
    Arrow.isoMk (realizeRestrictIso _ _ _ rfl ≪≫ realizeSubsetAtomIso U _) (realizeAtomIso U)
      (by ext T f; rfl)
  exact ⟨e' ≪≫ e⟩

theorem mono_pushoutProduct {X₁ Y₁ X₂ Y₂ : DiagSet.{u}} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    [Mono f₁] [Mono f₂] :
    Mono (Functor.PushoutObjObj.ofHasPushout (Functor.curry.obj grayTensorBifunctor.{u})
      f₁ f₂).ι := by
  have : IsSaturated.{u} (monomorphisms DiagSet.{u}) := by
    rw [monomorphisms_eq_saturation_sphereInclusions]
    infer_instance
  have hf (Z Z' : DiagSet.{u}) (f : Z ⟶ Z') [Mono f] : saturation.{u} sphereInclusions f := by
    rw [← monomorphisms_eq_saturation_sphereInclusions]
    exact ‹Mono f›
  refine pushoutObjObj_ι_mem_of_saturation (Functor.curry.obj grayTensorBifunctor.{u})
    (monomorphisms _) sphereInclusions sphereInclusions ?_ (hf _ _ f₁) (hf _ _ f₂)
    (hB := fun _ _ _ _ ↦ inferInstance) (hB' := fun _ _ _ _ ↦ inferInstance)
  rintro _ _ _ _ _ _ ⟨U⟩ ⟨V⟩
  obtain ⟨e₁⟩ := nonempty_arrowIso_realize_restrictIncl_bdryFull.{u} U
  obtain ⟨e₂⟩ := nonempty_arrowIso_realize_restrictIncl_bdryFull.{u} V
  exact ((monomorphisms _).arrow_mk_iso_iff
    (Functor.PushoutObjObj.ι_iso_of_iso_left (.ofHasPushout _ _ _) (.ofHasPushout _ _ _) e₁ ≪≫
      Functor.PushoutObjObj.ι_iso_of_iso_right (.ofHasPushout _ _ _) (.ofHasPushout _ _ _) e₂)).1
    (mono_pushoutProduct_realize_restrictIncl.{u} _ _ _ _)

instance mono_grayTensorBifunctor_map {X Y X' Y' : DiagSet.{u}} (f : X ⟶ X') (g : Y ⟶ Y')
    [Mono f] [Mono g] : Mono (grayTensorBifunctor.map ((f, g) : (X, Y) ⟶ (X', Y'))) := by
  have h₁ : Mono (((Functor.curry.obj grayTensorBifunctor.{u}).map f).app Y) :=
    have := mono_pushoutProduct f (initial.to Y)
    have : IsIso (((Functor.curry.obj grayTensorBifunctor.{u}).map f).app (⊥_ _)) :=
      isIso_of_isInitial (IsInitial.isInitialObj (grayTensorLeft X) _ initialIsInitial)
        (IsInitial.isInitialObj (grayTensorLeft X') _ initialIsInitial) _
    (Functor.PushoutObjObj.ofHasPushout _ f (initial.to Y)).mono_map_app_of_mono_ι
  have h₂ : Mono (((Functor.curry.obj grayTensorBifunctor.{u}).obj X').map g) :=
    have := mono_pushoutProduct (initial.to X') g
    have : IsIso (((Functor.curry.obj grayTensorBifunctor.{u}).obj (⊥_ _)).map g) :=
      isIso_of_isInitial (IsInitial.isInitialObj (grayTensorRight Y) _ initialIsInitial)
        (IsInitial.isInitialObj (grayTensorRight Y') _ initialIsInitial) _
    (Functor.PushoutObjObj.ofHasPushout _ (initial.to X') g).mono_obj_map_of_mono_ι
  have e : grayTensorBifunctor.map ((f, g) : (X, Y) ⟶ (X', Y')) =
      grayTensorBifunctor.map ((f, 𝟙 Y) : (X, Y) ⟶ (X', Y)) ≫
        grayTensorBifunctor.map ((𝟙 X', g) : (X', Y) ⟶ (X', Y')) := by
    rw [← Functor.map_comp, prod_comp, Category.comp_id, Category.id_comp]
  rw [e]
  exact @mono_comp _ _ _ _ _ _ h₁ _ h₂

end Atoms.Diagrammatic
