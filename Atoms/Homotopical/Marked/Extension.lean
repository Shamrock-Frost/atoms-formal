import Atoms.Homotopical.Marked.Basic

open CategoryTheory Limits Opposite

namespace Atoms.Homotopical

universe w v u' v₁ u₁

variable {A : Type v} [SmallCategory A] (D : MarkingData A)

theorem MarkedSite.isSeparated_yoneda_obj (x : MarkedSite D) :
    Presieve.IsSeparated (MarkedSite.topology D) (uliftYoneda.{w}.obj x) :=
  MarkedSite.isSeparated_iff.2 fun _ _ _ h => ULift.ext _ _ (MarkedSite.hom_ext
    ((Category.id_comp _).symm.trans ((congrArg (fun f => f.down.1) h).trans
      (Category.id_comp _))))

def MarkedPresheaf.yoneda : MarkedSite D ⥤ MarkedPresheaf.{w} D :=
  ObjectProperty.lift _ uliftYoneda.{max w v} (MarkedSite.isSeparated_yoneda_obj.{max w v} D)

variable {D} {E : Type u'} [Category.{max w v} E]

theorem MarkedPresheaf.isSeparated_comp_yoneda_obj_iff (F : MarkedSite D ⥤ E) :
    (∀ e : E, Presieve.IsSeparated (MarkedSite.topology D)
      (F.op ⋙ CategoryTheory.yoneda.obj e)) ↔
      ∀ x : MarkedSite D, Epi (F.map (MarkedSite.toSelf x)) :=
  ⟨fun h x => ⟨fun _ _ hgk => MarkedSite.isSeparated_iff.1 (h _) x hgk⟩,
    fun h _ => MarkedSite.isSeparated_iff.2 fun x g k hgk => (h x).left_cancellation g k hgk⟩

def MarkedPresheaf.nerve (F : MarkedSite D ⥤ E)
    (hF : ∀ x : MarkedSite D, Epi (F.map (MarkedSite.toSelf x))) : E ⥤ MarkedPresheaf.{w} D :=
  ObjectProperty.lift _ (CategoryTheory.yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj F.op)
    ((MarkedPresheaf.isSeparated_comp_yoneda_obj_iff F).2 hF)

variable (D) in
noncomputable def MarkedPresheaf.isColimitιMapCoconeAt (Y : MarkedPresheaf.{w} D) :
    IsColimit ((ObjectProperty.ι _).mapCocone
      ((Functor.LeftExtension.mk (𝟭 _)
        (MarkedPresheaf.yoneda.{w} D).rightUnitor.inv).coconeAt Y)) :=
  (IsColimit.whiskerEquivalence (uliftYoneda.{max w v}.denseAt Y.obj)
    (CostructuredArrow.post (MarkedPresheaf.yoneda D) (ObjectProperty.ι _)
      Y).asEquivalence).ofIsoColimit
    (Cocone.ext (Iso.refl _) (fun _ => by
      simp [Functor.LeftExtension.mk, Functor.asEquivalence]; rfl))

variable (D) in
instance MarkedPresheaf.isDense_yoneda : (MarkedPresheaf.yoneda.{w} D).IsDense where
  isDenseAt Y := ⟨isColimitOfReflects (ObjectProperty.ι _) (isColimitιMapCoconeAt D Y)⟩

def MarkedPresheaf.isPointwiseLeftKanExtensionOfIsColimit
    (G : MarkedPresheaf.{w} D ⥤ E) (h : ∀ Y : MarkedPresheaf.{w} D, IsColimit (G.mapCocone
      ((Functor.LeftExtension.mk (𝟭 _) (MarkedPresheaf.yoneda D).rightUnitor.inv).coconeAt Y))) :
    (Functor.LeftExtension.mk G (𝟙 (MarkedPresheaf.yoneda D ⋙ G))).IsPointwiseLeftKanExtension :=
  fun Y => (h Y).ofIsoColimit (Cocone.ext (Iso.refl _) (fun _ => (Category.comp_id _).trans
    ((G.congr_map (Category.id_comp _)).trans (Category.id_comp _).symm)))

theorem MarkedPresheaf.isLeftKanExtension_of_preservesColimits (G : MarkedPresheaf.{w} D ⥤ E)
    [PreservesColimitsOfSize.{v, max w v} G] :
    G.IsLeftKanExtension (𝟙 (MarkedPresheaf.yoneda D ⋙ G)) :=
  (isPointwiseLeftKanExtensionOfIsColimit G fun Y =>
    isColimitOfPreserves G ((MarkedPresheaf.yoneda D).denseAt Y)).isLeftKanExtension

theorem MarkedPresheaf.hom_ext_of_preservesColimits {G H : MarkedPresheaf.{w} D ⥤ E}
    [PreservesColimitsOfSize.{v, max w v} G] {α β : G ⟶ H}
    (h : Functor.whiskerLeft (MarkedPresheaf.yoneda D) α =
      Functor.whiskerLeft (MarkedPresheaf.yoneda D) β) : α = β :=
  have := isLeftKanExtension_of_preservesColimits G
  G.hom_ext_of_isLeftKanExtension (𝟙 _) α β (by rw [h])

noncomputable def MarkedPresheaf.isoOfPreservesColimits {G H : MarkedPresheaf.{w} D ⥤ E}
    [PreservesColimitsOfSize.{v, max w v} G] [PreservesColimitsOfSize.{v, max w v} H]
    (e : MarkedPresheaf.yoneda D ⋙ G ≅ MarkedPresheaf.yoneda D ⋙ H) : G ≅ H :=
  have := isLeftKanExtension_of_preservesColimits G
  have := isLeftKanExtension_of_preservesColimits H
  Functor.leftKanExtensionUniqueOfIso G (𝟙 _) e H (𝟙 _)

theorem MarkedPresheaf.whiskerLeft_yoneda_isoOfPreservesColimits_hom
    {G H : MarkedPresheaf.{w} D ⥤ E} [PreservesColimitsOfSize.{v, max w v} G]
    [PreservesColimitsOfSize.{v, max w v} H]
    (e : MarkedPresheaf.yoneda D ⋙ G ≅ MarkedPresheaf.yoneda D ⋙ H) :
    Functor.whiskerLeft (MarkedPresheaf.yoneda D) (isoOfPreservesColimits e).hom = e.hom := by
  have := isLeftKanExtension_of_preservesColimits G
  have := isLeftKanExtension_of_preservesColimits H
  have h := G.descOfIsLeftKanExtension_fac (𝟙 _) H (e.hom ≫ 𝟙 _)
  simpa [isoOfPreservesColimits] using h

variable [HasColimitsOfSize.{v, max w v} E]

noncomputable def MarkedPresheaf.extend (F : MarkedSite D ⥤ E) : MarkedPresheaf.{w} D ⥤ E :=
  ObjectProperty.ι _ ⋙ uliftYoneda.{max w v}.leftKanExtension F

noncomputable def MarkedPresheaf.yonedaCompExtendIso (F : MarkedSite D ⥤ E) :
    MarkedPresheaf.yoneda.{w} D ⋙ MarkedPresheaf.extend F ≅ F :=
  (Functor.associator _ _ _).symm ≪≫ Presheaf.isExtensionAlongULiftYoneda F

theorem MarkedPresheaf.isColimit_extend_mapCocone (F : MarkedSite D ⥤ E) {J : Type u₁}
    [Category.{v₁} J] {K : J ⥤ MarkedPresheaf.{w} D} {c : Cocone K}
    (hc : IsColimit ((ObjectProperty.ι _).mapCocone c)) :
    Nonempty (IsColimit ((MarkedPresheaf.extend F).mapCocone c)) :=
  ⟨isColimitOfPreserves (uliftYoneda.{max w v}.leftKanExtension F) hc⟩

private def restrictedULiftYonedaIsoNerveCompι (F : MarkedSite D ⥤ E)
    (hF : ∀ x : MarkedSite D, Epi (F.map (MarkedSite.toSelf x))) :
    𝟭 E ⋙ Presheaf.restrictedULiftYoneda.{max w v} F ≅
      MarkedPresheaf.nerve.{w} F hF ⋙ ObjectProperty.ι _ :=
  Functor.leftUnitor _ ≪≫
    Functor.isoWhiskerRight (uliftYonedaIsoYoneda.{max w v} (C := E)) _

noncomputable def MarkedPresheaf.extendAdjunction (F : MarkedSite D ⥤ E)
    (hF : ∀ x : MarkedSite D, Epi (F.map (MarkedSite.toSelf x))) :
    MarkedPresheaf.extend F ⊣ MarkedPresheaf.nerve F hF :=
  Adjunction.restrictFullyFaithful
    (Presheaf.uliftYonedaAdjunction _ (uliftYoneda.{max w v}.leftKanExtensionUnit F))
    (ObjectProperty.fullyFaithfulι _) (Functor.FullyFaithful.id E)
    (Functor.rightUnitor _).symm (restrictedULiftYonedaIsoNerveCompι F hF)

instance MarkedPresheaf.isLeftKanExtension_extend (F : MarkedSite D ⥤ E) :
    (MarkedPresheaf.extend F).IsLeftKanExtension (MarkedPresheaf.yonedaCompExtendIso F).inv := by
  have := (isPointwiseLeftKanExtensionOfIsColimit (MarkedPresheaf.extend F) fun Y =>
    isColimitOfPreserves (uliftYoneda.{max w v}.leftKanExtension F)
      (isColimitιMapCoconeAt D Y)).isLeftKanExtension
  exact (Functor.isLeftKanExtension_iff_of_iso₂ (𝟙 _) (yonedaCompExtendIso F).inv
    (yonedaCompExtendIso F) (Iso.refl _) (by simp)).1 this

noncomputable def MarkedPresheaf.extendMap {F G : MarkedSite D ⥤ E} (α : F ⟶ G) :
    MarkedPresheaf.extend F ⟶ MarkedPresheaf.extend G :=
  (MarkedPresheaf.extend F).descOfIsLeftKanExtension (yonedaCompExtendIso F).inv _
    (α ≫ (yonedaCompExtendIso G).inv)

theorem MarkedPresheaf.whiskerLeft_yoneda_extendMap {F G : MarkedSite D ⥤ E} (α : F ⟶ G) :
    Functor.whiskerLeft (MarkedPresheaf.yoneda D) (MarkedPresheaf.extendMap α) =
      (MarkedPresheaf.yonedaCompExtendIso F).hom ≫ α ≫
        (MarkedPresheaf.yonedaCompExtendIso G).inv := by
  rw [← (MarkedPresheaf.extend F).descOfIsLeftKanExtension_fac (yonedaCompExtendIso F).inv _
    (α ≫ (yonedaCompExtendIso G).inv), Iso.hom_inv_id_assoc]
  rfl

theorem MarkedPresheaf.extendMap_app_yoneda_obj {F G : MarkedSite D ⥤ E} (α : F ⟶ G)
    (x : MarkedSite D) :
    (MarkedPresheaf.extendMap α).app ((MarkedPresheaf.yoneda D).obj x) =
      (MarkedPresheaf.yonedaCompExtendIso F).hom.app x ≫ α.app x ≫
        (MarkedPresheaf.yonedaCompExtendIso G).inv.app x :=
  NatTrans.congr_app (whiskerLeft_yoneda_extendMap α) x

theorem MarkedPresheaf.extendMap_id (F : MarkedSite D ⥤ E) :
    MarkedPresheaf.extendMap (𝟙 F) = 𝟙 _ :=
  (MarkedPresheaf.extend F).hom_ext_of_isLeftKanExtension (yonedaCompExtendIso F).inv _ _ (by
    rw [whiskerLeft_yoneda_extendMap, Iso.inv_hom_id_assoc]
    simp)

theorem MarkedPresheaf.extendMap_comp {F G H : MarkedSite D ⥤ E} (α : F ⟶ G) (β : G ⟶ H) :
    MarkedPresheaf.extendMap (α ≫ β) =
      MarkedPresheaf.extendMap α ≫ MarkedPresheaf.extendMap β :=
  (MarkedPresheaf.extend F).hom_ext_of_isLeftKanExtension (yonedaCompExtendIso F).inv _ _ (by
    rw [Functor.whiskerLeft_comp, whiskerLeft_yoneda_extendMap, whiskerLeft_yoneda_extendMap,
      whiskerLeft_yoneda_extendMap]
    simp)

noncomputable def MarkedPresheaf.adjunctionOfPreservesColimits (G : MarkedPresheaf.{w} D ⥤ E)
    [PreservesColimitsOfSize.{v, max w v} G]
    (hG : ∀ x : MarkedSite D,
      Epi (G.map ((MarkedPresheaf.yoneda D).map (MarkedSite.toSelf x)))) :
    G ⊣ MarkedPresheaf.nerve (MarkedPresheaf.yoneda D ⋙ G) hG :=
  have := isLeftKanExtension_of_preservesColimits G
  (extendAdjunction (MarkedPresheaf.yoneda D ⋙ G) hG).ofNatIsoLeft
    (Functor.leftKanExtensionUnique _ (yonedaCompExtendIso (MarkedPresheaf.yoneda D ⋙ G)).inv G
      (𝟙 _))

private theorem homEquiv_restrictFullyFaithful_hom {C : Type*} {E : Type*} [Category C]
    [Category E] (Q : ObjectProperty C) {L : C ⥤ E} {R : E ⥤ C} (adj : L ⊣ R)
    {R' : E ⥤ Q.FullSubcategory} (comm : 𝟭 E ⋙ R ≅ R' ⋙ Q.ι) (P : Q.FullSubcategory) (Y : E)
    (f : L.obj P.obj ⟶ Y) :
    ((adj.restrictFullyFaithful (L := Q.ι ⋙ L) (ObjectProperty.fullyFaithfulι Q)
      (Functor.FullyFaithful.id E) (Functor.rightUnitor (Q.ι ⋙ L)).symm comm).homEquiv
        P Y f).hom = adj.unit.app P.obj ≫ R.map f ≫ comm.hom.app Y := by
  rw [Adjunction.restrictFullyFaithful_homEquiv_apply]
  simp

theorem MarkedPresheaf.homEquiv_adjunctionOfPreservesColimits_app
    (G : MarkedPresheaf.{w} D ⥤ E) [PreservesColimitsOfSize.{v, max w v} G]
    (hG : ∀ x : MarkedSite D,
      Epi (G.map ((MarkedPresheaf.yoneda D).map (MarkedSite.toSelf x))))
    {P : MarkedPresheaf.{w} D} {Y : E} (f : G.obj P ⟶ Y) (x : MarkedSite D)
    (z : P.obj.obj (op x)) :
    ((MarkedPresheaf.adjunctionOfPreservesColimits G hG).homEquiv P Y f).hom.app (op x) z =
      G.map (ObjectProperty.homMk (uliftYonedaEquiv.symm z) :
        (MarkedPresheaf.yoneda D).obj x ⟶ P) ≫ f := by
  have := MarkedPresheaf.isLeftKanExtension_of_preservesColimits G
  let F := MarkedPresheaf.yoneda D ⋙ G
  let e := (MarkedPresheaf.extend F).leftKanExtensionUnique
    (MarkedPresheaf.yonedaCompExtendIso F).inv G (𝟙 F)
  have hfac : (uliftYoneda.{max w v}.leftKanExtensionUnit F).app x ≫
      e.hom.app ((MarkedPresheaf.yoneda D).obj x) = 𝟙 _ := by
    have h := (MarkedPresheaf.extend F).descOfIsLeftKanExtension_fac_app
      (MarkedPresheaf.yonedaCompExtendIso F).inv G ((Iso.refl F).hom ≫ 𝟙 F) x
    exact (congrArg (· ≫ _) (Category.comp_id _)).symm.trans (h.trans (by simp))
  have hn := e.hom.naturality (ObjectProperty.homMk (uliftYonedaEquiv.symm z) :
    (MarkedPresheaf.yoneda D).obj x ⟶ P)
  have h' : ((MarkedPresheaf.extendAdjunction F hG).homEquiv P Y (e.hom.app P ≫ f)).hom = _ :=
    homEquiv_restrictFullyFaithful_hom _ _ _ P Y (e.hom.app P ≫ f)
  rw [MarkedPresheaf.adjunctionOfPreservesColimits, Adjunction.homEquiv_ofNatIsoLeft_apply, h',
    ← Adjunction.homEquiv_id]
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply]
  rw [Presheaf.uliftYonedaAdjunction_homEquiv_app]
  refine Eq.trans (?_ : _ = ((uliftYoneda.{max w v}.leftKanExtensionUnit F).app x ≫
    (MarkedPresheaf.extend F).map (ObjectProperty.homMk (uliftYonedaEquiv.symm z) :
      (MarkedPresheaf.yoneda D).obj x ⟶ P)) ≫ e.hom.app P ≫ f) ?_
  · exact congrArg (fun k => ((uliftYoneda.{max w v}.leftKanExtensionUnit F).app x ≫ k) ≫
      e.hom.app P ≫ f) (Category.comp_id _)
  · exact (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·) (Category.assoc _ _ _).symm).trans <|
      (congrArg (fun k => _ ≫ k ≫ f) hn).trans <| (congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans <|
      (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) hfac).trans (Category.id_comp _)

noncomputable def MarkedPresheaf.extendYonedaIso (D : MarkingData A) :
    MarkedPresheaf.extend (MarkedPresheaf.yoneda.{w} D) ≅ 𝟭 (MarkedPresheaf.{w} D) :=
  Functor.leftKanExtensionUnique _ (yonedaCompExtendIso (MarkedPresheaf.yoneda D)).inv _
    (MarkedPresheaf.yoneda D).rightUnitor.inv

theorem MarkedPresheaf.whiskerLeft_yoneda_extendYonedaIso_hom (D : MarkingData A) :
    Functor.whiskerLeft (MarkedPresheaf.yoneda.{w} D) (MarkedPresheaf.extendYonedaIso D).hom =
      (MarkedPresheaf.yonedaCompExtendIso (MarkedPresheaf.yoneda D)).hom := by
  have h := (MarkedPresheaf.extend (MarkedPresheaf.yoneda D)).descOfIsLeftKanExtension_fac
    (yonedaCompExtendIso (MarkedPresheaf.yoneda D)).inv _
    (MarkedPresheaf.yoneda D).rightUnitor.inv
  rw [Iso.inv_comp_eq] at h
  exact h.trans (by ext; simp)

theorem MarkedPresheaf.extendYonedaIso_inv_app_yoneda_obj (D : MarkingData A) (x : MarkedSite D) :
    (MarkedPresheaf.extendYonedaIso D).inv.app ((MarkedPresheaf.yoneda.{w} D).obj x) =
      (MarkedPresheaf.yonedaCompExtendIso (MarkedPresheaf.yoneda D)).inv.app x := by
  rw [← cancel_epi ((MarkedPresheaf.extendYonedaIso D).hom.app _), Iso.hom_inv_id_app]
  have h := NatTrans.congr_app (whiskerLeft_yoneda_extendYonedaIso_hom D) x
  rw [Functor.whiskerLeft_app] at h
  rw [h, Iso.hom_inv_id_app]
  rfl

end Atoms.Homotopical
