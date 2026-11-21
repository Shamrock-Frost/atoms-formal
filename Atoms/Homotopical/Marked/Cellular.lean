import Atoms.ForMathlib.CategoryTheory.SmallObject.Basic
import Atoms.Homotopical.Marked.Extension

open CategoryTheory Limits Opposite MorphismProperty

namespace Atoms.Homotopical

universe w v

variable {A : Type v} [SmallCategory A] (D : MarkingData A)

namespace MarkedPresheaf

open MarkedSite

inductive markingMaps : MorphismProperty (MarkedPresheaf.{w} D)
  | mk (a : A) (h : D.markable a) :
      markingMaps ((MarkedPresheaf.yoneda.{w} D).map (MarkedSite.toSelf (MarkedSite.marked a h)))

variable {D}

instance mono_yoneda_map_toSelf (x : MarkedSite D) :
    Mono ((MarkedPresheaf.yoneda.{w} D).map (toSelf x)) := by
  rw [mono_iff, NatTrans.mono_iff_mono_app]
  rintro ⟨b⟩
  rw [mono_iff_injective]
  rintro ⟨k⟩ ⟨k'⟩ h
  exact ULift.ext _ _ (MarkedSite.hom_ext ((Category.comp_id _).symm.trans
    ((congrArg (fun g => g.down.1) h).trans (Category.comp_id _))))

instance epi_yoneda_map_toSelf (x : MarkedSite D) :
    Epi ((MarkedPresheaf.yoneda.{w} D).map (toSelf x)) where
  left_cancellation {Z} f g h := hom_ext (by
    ext ⟨b⟩ ⟨s⟩
    have hs : ((unmarked D).map s.1 : (unmarked D).obj b ⟶ (unmarked D).obj x.obj) ≫ toSelf x
        = s := MarkedSite.hom_ext (Category.comp_id _)
    have := congrArg (fun k : (MarkedPresheaf.yoneda.{w} D).obj ((unmarked D).obj x.obj) ⟶ Z =>
      (forget.map k).app (op b)
        (ULift.up ((unmarked D).map s.1 : (unmarked D).obj b ⟶ (unmarked D).obj x.obj))) h
    change (forget.map f).app (op b) ⟨s⟩ = (forget.map g).app (op b) ⟨s⟩
    rw [← hs]
    exact this)

instance isIso_forget_map_yoneda_map_toSelf (x : MarkedSite D) :
    IsIso (forget.map ((MarkedPresheaf.yoneda.{w} D).map (toSelf x))) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro c
  rw [isIso_iff_bijective]
  refine ⟨fun a b h ↦ ?_, fun b ↦ ⟨⟨⟨b.down.1, fun h ↦ absurd h Bool.false_ne_true⟩⟩, ?_⟩⟩
  · have : a.down.1 ≫ (toSelf x).1 = b.down.1 ≫ (toSelf x).1 :=
      congrArg (fun z : ULift _ ↦ z.down.1) h
    exact ULift.ext _ _ (MarkedSite.hom_ext
      ((Category.comp_id _).symm.trans (this.trans (Category.comp_id _))))
  · exact ULift.ext _ _ (MarkedSite.hom_ext (Category.comp_id _))

private theorem yoneda_hom_ext {x : MarkedSite D} {Z : MarkedPresheaf.{w} D}
    {u u' : (MarkedPresheaf.yoneda.{w} D).obj x ⟶ Z}
    (h : uliftYonedaEquiv u.hom = uliftYonedaEquiv u'.hom) : u = u' :=
  ObjectProperty.hom_ext _ (uliftYonedaEquiv.injective h)

private def yonedaHomMk {x : MarkedSite D} {Z : MarkedPresheaf.{w} D}
    (z : Z.obj.obj (op x)) :
    (MarkedPresheaf.yoneda.{w} D).obj x ⟶ Z :=
  ObjectProperty.homMk (uliftYonedaEquiv.symm z)

noncomputable def isColimitOfForget {J : Type*} [Category J] {F : J ⥤ MarkedPresheaf.{w} D}
    (c : Cocone F) (hc : IsColimit (forget.mapCocone c))
    (hm : ∀ (a : A) (y : c.pt.underlying.obj (op a)), y ∈ c.pt.marked a →
      ∃ (j : J) (x : (F.obj j).underlying.obj (op a)), x ∈ (F.obj j).marked a ∧
        (forget.map (c.ι.app j)).app (op a) x = y) :
    IsColimit c where
  desc s := homMk (hc.desc (forget.mapCocone s)) fun a y hy => by
    obtain ⟨j, x, hx, rfl⟩ := hm a y hy
    have h := congrArg (fun φ => φ.app (op a) x) (hc.fac (forget.mapCocone s) j)
    exact h ▸ map_mem_marked (s.ι.app j) hx
  fac s j := hom_ext ((forget.map_comp _ _).trans (hc.fac (forget.mapCocone s) j))
  uniq s m hm := hom_ext (hc.uniq (forget.mapCocone s) (forget.map m) fun j =>
    (forget.map_comp _ _).symm.trans (congrArg forget.map (hm j)))

variable (D) in
noncomputable def yonedaCompFlatIso :
    uliftYoneda.{w} ⋙ flat.{w} D ≅ unmarked D ⋙ MarkedPresheaf.yoneda.{w} D :=
  NatIso.ofComponents (fun a =>
    { hom := homMk (X := (flat.{w} D).obj (uliftYoneda.{w}.obj a))
        { app _ := ↾fun g => ⟨(unmarked D).map g.down⟩ } fun b g hg => by
          obtain ⟨c, p, hp, q, rfl⟩ := (mem_marked_flat D _ b g).1 hg
          exact ⟨D.markable_of_degeneracy p hp,
            ⟨⟨p ≫ q.down, fun _ => Or.inr ⟨c, p, q.down, hp, rfl⟩⟩⟩,
            ULift.ext _ _ (MarkedSite.hom_ext (Category.id_comp _))⟩
      inv := homMk (Y := (flat.{w} D).obj (uliftYoneda.{w}.obj a))
        { app _ := ↾fun g => ⟨g.down.1⟩ } fun b g hg => by
          obtain ⟨h, ⟨z⟩, rfl⟩ := hg
          rcases z.2 rfl with ⟨hf, -⟩ | ⟨c, p, q, hp, hpq⟩
          · exact absurd hf Bool.false_ne_true
          · exact (mem_marked_flat D _ b _).2
              ⟨c, p, hp, ⟨q⟩, ULift.ext _ _ (hpq.trans (Category.id_comp _).symm)⟩
      hom_inv_id := hom_ext rfl
      inv_hom_id := hom_ext rfl }) fun _ => hom_ext rfl

section Factorization

variable {X Y : MarkedPresheaf.{w} D} (f : X ⟶ Y)

private def imageMarking : Marking D Y.underlying where
  marked a := {y | (∃ x ∈ X.marked a, (forget.map f).app (op a) x = y) ∨
    y ∈ (flatMarking D Y.underlying).marked a}
  markable a y := by
    rintro (⟨x, hx, -⟩ | hy)
    · exact X.markable a x hx
    · exact (flatMarking D _).markable a y hy
  degenerate _ _ p hp y := Or.inr ((flatMarking D _).degenerate p hp y)
  transport a b e y := by
    constructor
    · rintro (⟨x, hx, rfl⟩ | hy)
      · exact Or.inl ⟨X.underlying.map e.hom.op x, (X.transport e x).1 hx,
          NatTrans.naturality_apply (forget.map f) e.hom.op x⟩
      · exact Or.inr (((flatMarking D _).transport e y).1 hy)
    · rintro (⟨x, hx, hxy⟩ | hy)
      · refine Or.inl ⟨X.underlying.map e.inv.op x, (X.transport e.symm x).1 hx, ?_⟩
        refine (NatTrans.naturality_apply (forget.map f) e.inv.op x).trans ?_
        change Y.underlying.map e.inv.op ((forget.map f).app (op a) x) = y
        rw [hxy, ← Functor.map_comp_apply, ← op_comp, e.inv_hom_id, op_id, Functor.map_id_apply]
      · exact Or.inr (((flatMarking D _).transport e y).2 hy)

private noncomputable def toImage : X ⟶ ofMarking Y.underlying (imageMarking f) :=
  homMk (Y := ofMarking Y.underlying (imageMarking f)) (forget.map f) fun a x hx =>
    (mem_marked_ofMarking _ _ a _).2 (Or.inl ⟨x, hx, rfl⟩)

private noncomputable def fromImage : ofMarking Y.underlying (imageMarking f) ⟶ Y :=
  homMk (X := ofMarking Y.underlying (imageMarking f)) (𝟙 _) fun a y hy => by
    rcases (mem_marked_ofMarking _ _ a _).1 hy with ⟨x, hx, rfl⟩ | ⟨b, p, hp, z, rfl⟩
    · exact map_mem_marked f hx
    · exact Y.degenerate p hp z

private theorem toImage_comp_fromImage : toImage f ≫ fromImage f = f :=
  hom_ext rfl

variable (X) in
private noncomputable def fromFlat : (flat D).obj X.underlying ⟶ X :=
  homMk (X := (flat D).obj X.underlying) (𝟙 _) fun a x hx => by
    obtain ⟨b, p, hp, y, rfl⟩ := (mem_marked_flat D _ a x).1 hx
    exact X.degenerate p hp y

private noncomputable def flatToImage :
    (flat D).obj Y.underlying ⟶ ofMarking Y.underlying (imageMarking f) :=
  homMk (X := (flat D).obj Y.underlying) (Y := ofMarking Y.underlying (imageMarking f)) (𝟙 _)
    fun a y hy => (mem_marked_ofMarking _ _ a _).2 (Or.inr ((mem_marked_flat D _ a y).1 hy))

private theorem forget_map_inl (s : PushoutCocone (fromFlat X) ((flat D).map (forget.map f))) :
    forget.map s.inl =
      forget.map f ≫ (forget (D := D)).map (X := (flat D).obj Y.underlying) s.inr := by
  have := congrArg forget.map s.condition
  rw [forget.map_comp, forget.map_comp] at this
  exact (Category.id_comp _).symm.trans this

private theorem isPushout_toImage :
    IsPushout (fromFlat X) ((flat D).map (forget.map f)) (toImage f) (flatToImage f) := by
  refine IsPushout.of_isColimit' ⟨hom_ext rfl⟩ (PushoutCocone.IsColimit.mk _
    (fun s => homMk (X := ofMarking Y.underlying (imageMarking f))
      ((forget (D := D)).map (X := (flat D).obj Y.underlying) s.inr)
      fun a y hy => ?_) (fun s => ?_)
    (fun s => hom_ext ((forget.map_comp _ _).trans (Category.id_comp _)))
    (fun s m _ hm => hom_ext ((Category.id_comp _).symm.trans
      ((forget.map_comp _ _).symm.trans (congrArg forget.map hm)))))
  · have hs := forget_map_inl f s
    rcases (mem_marked_ofMarking _ _ a _).1 hy with ⟨x, hx, rfl⟩ | hy
    · have := map_mem_marked s.inl hx
      rwa [hs] at this
    · exact map_mem_marked s.inr ((mem_marked_flat D _ a y).2 hy)
  · exact hom_ext (forget_map_inl f s).symm

variable (Y) in
private abbrev MarkedCell : Type (max w v) :=
  Σ a : A, Σ' h : D.markable a, Y.obj.obj (op (MarkedSite.marked a h))

private abbrev markingMap (j : MarkedCell Y) :
    (MarkedPresheaf.yoneda.{w} D).obj ((unmarked D).obj j.1) ⟶
      (MarkedPresheaf.yoneda D).obj (MarkedSite.marked j.1 j.2.1) :=
  (MarkedPresheaf.yoneda D).map (toSelf (MarkedSite.marked j.1 j.2.1))

private def restrictToImage (j : MarkedCell Y) :
    (MarkedPresheaf.yoneda D).obj ((unmarked D).obj j.1) ⟶
      ofMarking Y.underlying (imageMarking f) :=
  yonedaHomMk (Z := ofMarking Y.underlying (imageMarking f))
    (Y.obj.map (toSelf (MarkedSite.marked j.1 j.2.1)).op j.2.2)

private theorem restrictToImage_comp_fromImage (j : MarkedCell Y) :
    restrictToImage f j ≫ fromImage f = markingMap j ≫ yonedaHomMk j.2.2 := by
  refine yoneda_hom_ext ?_
  change (fromImage f).hom.app _ (uliftYonedaEquiv ((uliftYonedaEquiv (X := (unmarked D).obj j.1)
      (F := (ofMarking Y.underlying (imageMarking f)).obj)).symm
        (Y.obj.map (toSelf (MarkedSite.marked j.1 j.2.1)).op j.2.2))) =
    (uliftYonedaEquiv.symm j.2.2).app _
      (uliftYonedaEquiv (uliftYoneda.{max w v}.map (toSelf _)))
  refine (congrArg ((fromImage f).hom.app _) (Equiv.apply_symm_apply _ _)).trans ?_
  exact congrArg (fun g => Y.obj.map (Quiver.Hom.op g) j.2.2)
    (Category.id_comp (toSelf (MarkedSite.marked j.1 j.2.1))).symm

private theorem isPushout_fromImage :
    IsPushout (Sigma.desc (restrictToImage f)) (Limits.Sigma.map (markingMap (Y := Y)))
      (fromImage f) (Sigma.desc fun j => yonedaHomMk j.2.2) := by
  have hsq : Sigma.desc (restrictToImage f) ≫ fromImage f =
      Limits.Sigma.map (markingMap (Y := Y)) ≫ Sigma.desc fun j => yonedaHomMk j.2.2 :=
    Sigma.hom_ext _ _ fun j => by
      rw [Sigma.ι_desc_assoc, Sigma.ι_map_assoc, Sigma.ι_desc]
      exact restrictToImage_comp_fromImage f j
  have hj : ∀ (s : PushoutCocone (Sigma.desc (restrictToImage f))
      (Limits.Sigma.map (markingMap (Y := Y)))) (j : MarkedCell Y),
      restrictToImage f j ≫ s.inl = markingMap j ≫ Sigma.ι (fun j : MarkedCell Y =>
        (MarkedPresheaf.yoneda D).obj (MarkedSite.marked j.1 j.2.1)) j ≫ s.inr := fun s j => by
    have := Sigma.ι _ j ≫= s.condition
    rwa [Sigma.ι_desc_assoc, Sigma.ι_map_assoc] at this
  have hl : ∀ (s : PushoutCocone (Sigma.desc (restrictToImage f))
      (Limits.Sigma.map (markingMap (Y := Y)))) (hs : _),
      fromImage f ≫ homMk (X := Y)
        ((forget (D := D)).map (X := ofMarking Y.underlying (imageMarking f)) s.inl) hs =
        s.inl := fun s _ => hom_ext ((forget.map_comp _ _).trans (Category.id_comp _))
  refine IsPushout.of_isColimit' ⟨hsq⟩ (PushoutCocone.IsColimit.mk _
    (fun s => homMk (X := Y)
      ((forget (D := D)).map (X := ofMarking Y.underlying (imageMarking f)) s.inl)
      fun a y hy => ?_) (fun s => hl s _) (fun s => ?_) (fun s m hm _ => ?_))
  · obtain ⟨h, z, rfl⟩ := hy
    have e := congrArg (fun k => uliftYonedaEquiv k.hom) (hj s ⟨a, h, z⟩)
    let w := Sigma.ι (fun j : MarkedCell Y =>
      (MarkedPresheaf.yoneda D).obj (MarkedSite.marked j.1 j.2.1)) ⟨a, h, z⟩ ≫ s.inr
    refine ⟨h, w.hom.app _ ⟨𝟙 (MarkedSite.marked a h)⟩, ?_⟩
    refine (NatTrans.naturality_apply w.hom (toSelf (MarkedSite.marked a h)).op
      (⟨𝟙 (MarkedSite.marked a h)⟩ : ULift.{max w v} _)).symm.trans ?_
    refine (congrArg (w.hom.app _)
      (ULift.ext _ _ ((Category.comp_id _).trans (Category.id_comp _).symm))).trans ?_
    refine e.symm.trans ?_
    exact congrArg (s.inl.hom.app _) (Equiv.apply_symm_apply (uliftYonedaEquiv
      (X := (unmarked D).obj a) (F := (ofMarking Y.underlying (imageMarking f)).obj))
      (Y.obj.map (toSelf (MarkedSite.marked a h)).op z))
  · refine Sigma.hom_ext _ _ fun j => ?_
    rw [Sigma.ι_desc_assoc]
    refine (@cancel_epi _ _ _ _ _ (markingMap j) (epi_yoneda_map_toSelf _) _ _).1 ?_
    rw [← Category.assoc, ← restrictToImage_comp_fromImage, Category.assoc, hl, hj]
  · exact hom_ext ((Category.id_comp _).symm.trans
      ((forget.map_comp _ _).symm.trans (congrArg forget.map hm)))

end Factorization
variable (D) in
theorem saturation_functorImage_flat_sup_markingMaps
    {I : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))}
    (hI : saturation.{max w v} I = monomorphisms (Aᵒᵖ ⥤ Type (max w v))) :
    saturation.{max w v}
        (functorImage (MarkedPresheaf.flat D) I ⊔ MarkedPresheaf.markingMaps.{w} D) =
      monomorphisms (MarkedPresheaf.{w} D) := by
  refine le_antisymm (saturation_le _ _ ?_) fun X Y f hf => ?_
  · rintro _ _ g (⟨K, L, t, ht, e⟩ | ⟨a, h⟩)
    · have : Mono t := (hI ▸ le_saturation I t ht : monomorphisms _ t)
      have : Mono ((flat D).map t) := (mono_iff _).2 this
      exact ((monomorphisms _).arrow_mk_iso_iff (eqToIso e)).1 this
    · exact monomorphisms.infer_property _
  · have hmono : Mono f := hf
    have : PreservesColimitsOfSize.{max w v, max w v} (flat.{w} D) :=
      (flatForgetAdjunction D).leftAdjoint_preservesColimits
    have hle : saturation.{max w v} (functorImage (flat D) I) ≤
        saturation.{max w v} (functorImage (flat D) I ⊔ markingMaps D) :=
      saturation_le _ _ ((le_sup_left).trans (le_saturation _))
    have hflat : saturation.{max w v} I ≤
        (saturation.{max w v} (functorImage (flat D) I ⊔ markingMaps D)).inverseImage (flat D) :=
      saturation_le _ _ fun _ _ t ht => hle _ (le_saturation _ _ ⟨_, _, t, ht, rfl⟩)
    have h₁ : saturation.{max w v} (functorImage (flat D) I ⊔ markingMaps D) (toImage f) :=
      MorphismProperty.of_isPushout (isPushout_toImage f)
        (hflat _ (by rw [hI]; exact (mono_iff f).1 hmono))
    have := IsCellularlyClosed.isStableUnderCoproducts.{max w v}
      (saturation.{max w v} (functorImage (flat D) I ⊔ markingMaps D))
    have h₂ : saturation.{max w v} (functorImage (flat D) I ⊔ markingMaps D) (fromImage f) :=
      MorphismProperty.of_isPushout (isPushout_fromImage f)
        (MorphismProperty.colimMap _ fun j => le_saturation _ _
          (Or.inr (markingMaps.mk j.as.1 j.as.2.1)))
    rw [← toImage_comp_fromImage f]
    exact comp_mem _ _ _ h₁ h₂

end MarkedPresheaf

end Atoms.Homotopical
