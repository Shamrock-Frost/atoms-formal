import Atoms.Homotopical.HomotopyColimit.CatWeakEquivalence

open CategoryTheory Limits MorphismProperty

namespace Atoms.Homotopical

universe v

variable {A : Type v} [SmallCategory A] {V : MorphismProperty (Aᵒᵖ ⥤ Type v)}

theorem IsALocalizer.isRegularALocalizer_of_generatedALocalizer_bot [IsALocalizer V]
    [h : IsRegularALocalizer
      (generatedALocalizer.{v, v} (⊥ : MorphismProperty (Aᵒᵖ ⥤ Type v)))] :
    IsRegularALocalizer V :=
  ⟨fun X ↦ generatedALocalizer_le bot_le _ (h.isRegular X)⟩

section ElementsSieve

variable {X Y : Aᵒᵖ ⥤ Type v} (m : X ⟶ Y)

def elementsSieve : ObjectProperty (CostructuredArrow yoneda Y) :=
  fun c ↦ ∃ x : yoneda.obj c.left ⟶ X, x ≫ m = c.hom

theorem elementsSieve_of_hom {c c' : CostructuredArrow yoneda Y} (φ : c ⟶ c')
    (h : elementsSieve m c') : elementsSieve m c := by
  obtain ⟨x, hx⟩ := h
  exact ⟨yoneda.map φ.left ≫ x, by rw [Category.assoc, hx, CostructuredArrow.w]⟩

def toElementsSieve :
    CostructuredArrow yoneda X ⥤ (elementsSieve m).FullSubcategory :=
  ObjectProperty.lift _ (CostructuredArrow.map m) fun c ↦ ⟨c.hom, by simp⟩

instance faithful_toElementsSieve : (toElementsSieve m).Faithful where
  map_injective h :=
    CostructuredArrow.hom_ext _ _ (congrArg (fun φ ↦ φ.hom.left) h :)

instance full_toElementsSieve [Mono m] : (toElementsSieve m).Full where
  map_surjective {c c'} ψ := by
    refine ⟨CostructuredArrow.homMk ψ.hom.left ?_, ?_⟩
    · rw [← cancel_mono m, Category.assoc]
      exact CostructuredArrow.w ψ.hom
    · ext
      rfl

instance essSurj_toElementsSieve : (toElementsSieve m).EssSurj where
  mem_essImage s := by
    obtain ⟨x, hx⟩ := s.property
    exact ⟨CostructuredArrow.mk x,
      ⟨ObjectProperty.isoMk _ (CostructuredArrow.isoMk (Iso.refl s.obj.left) (by
        change yoneda.map (𝟙 s.obj.left) ≫ s.obj.hom = x ≫ m
        rw [yoneda.map_id, Category.id_comp, hx]))⟩⟩

instance isEquivalence_toElementsSieve [Mono m] : (toElementsSieve m).IsEquivalence where

end ElementsSieve

theorem IsALocalizer.isRegular_yoneda [hV : IsALocalizer V] (a : A) :
    IsRegular V (yoneda.obj a) := by
  let t : CostructuredArrow yoneda (yoneda.obj a) := CostructuredArrow.mk (𝟙 (yoneda.obj a))
  have ht : IsTerminal t := CostructuredArrow.mkIdTerminal
  let Q := (projectiveReplacement A (CostructuredArrow yoneda (yoneda.obj a))).obj
    (representablesOver (yoneda.obj a))
  have hι : IsIso (colimit.ι Q t) := (colimit.isColimit Q).isIso_ι_app_of_isTerminal t ht
  have e : colimit.ι Q t ≫ regularizationMap (yoneda.obj a) =
      ((projectiveReplacementπ A _).app (representablesOver (yoneda.obj a))).app t := by
    exact (ι_regularizationMap _ t).trans (Category.comp_id _)
  have h₁ : V (colimit.ι Q t ≫ regularizationMap (yoneda.obj a)) :=
    e ▸ hV.rlp_monomorphisms_le _ (rlp_monomorphisms_projectiveReplacementπ_app _ t)
  exact hV.hasTwoOutOfThreeProperty.of_precomp _ _
    (hV.isomorphisms_le _ (isomorphisms.infer_property _)) h₁

section SievePushout

variable {C : Type v} [SmallCategory C]

noncomputable def sievePre {P P' : ObjectProperty C} (h : P ≤ P') (F : C ⥤ Aᵒᵖ ⥤ Type v) :
    colimit (P.ι ⋙ F) ⟶ colimit (P'.ι ⋙ F) :=
  colimit.pre (P'.ι ⋙ F) (ObjectProperty.ιOfLE h)

@[reassoc]
theorem ι_sievePre {P P' : ObjectProperty C} (h : P ≤ P') (F : C ⥤ Aᵒᵖ ⥤ Type v)
    (x : P.FullSubcategory) :
    colimit.ι (P.ι ⋙ F) x ≫ sievePre h F =
      colimit.ι (P'.ι ⋙ F) ((ObjectProperty.ιOfLE h).obj x) :=
  colimit.ι_pre (P'.ι ⋙ F) (ObjectProperty.ιOfLE h) x

end SievePushout

section Glue

variable {J : Type v} [SmallCategory J] (T : J → Prop)
  (hT : ∀ ⦃j j' : J⦄, (j ⟶ j') → T j' → T j) {E B : Aᵒᵖ ⥤ Type v} (p : E ⟶ B)

def sieveGlue : J ⥤ Aᵒᵖ ⥤ Type v where
  obj j :=
    { obj a := {z : B.obj a × (T j → E.obj a) // ∀ t, p.app a (z.2 t) = z.1}
      map f := ↾fun z ↦ ⟨(B.map f z.1.1, fun t ↦ E.map f (z.1.2 t)), fun t ↦ by
        rw [← z.2 t]
        exact NatTrans.naturality_apply p f _⟩
      map_id a := by
        refine ConcreteCategory.hom_ext _ _ fun z ↦ Subtype.ext (Prod.ext ?_ ?_)
        · simp
        · funext t
          simp
      map_comp f g := by
        refine ConcreteCategory.hom_ext _ _ fun z ↦ Subtype.ext (Prod.ext ?_ ?_)
        · simp
        · funext t
          simp }
  map φ :=
    { app a := ↾fun z ↦ ⟨(z.1.1, fun t ↦ z.1.2 (hT φ t)), fun t ↦ z.2 _⟩
      naturality a a' f := rfl }
  map_id j := rfl
  map_comp φ ψ := rfl

def toSieveGlue : (Functor.const J).obj E ⟶ sieveGlue T hT p where
  app j :=
    { app a := ↾fun e ↦ ⟨(p.app a e, fun _ ↦ e), fun _ ↦ rfl⟩
      naturality a a' f := by
        refine ConcreteCategory.hom_ext _ _ fun e ↦ ?_
        apply Subtype.ext
        apply Prod.ext
        · exact NatTrans.naturality_apply p f e
        · rfl }
  naturality j j' φ := rfl

theorem toSieveGlue_app_app_apply (j : J) (a : Aᵒᵖ) (e : E.obj a) :
    ((toSieveGlue T hT p).app j).app a e = ⟨(p.app a e, fun _ ↦ e), fun _ ↦ rfl⟩ :=
  rfl

theorem rlp_toSieveGlue_app (hp : (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v)).rlp p)
    (j : J) :
    (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v)).rlp ((toSieveGlue T hT p).app j) := by
  by_cases hj : T j
  · have : ∀ a, IsIso (((toSieveGlue T hT p).app j).app a) := by
      intro a
      rw [isIso_iff_bijective]
      refine ⟨fun e e' he ↦ ?_, fun z ↦ ⟨z.1.2 hj, ?_⟩⟩
      · rw [toSieveGlue_app_app_apply, toSieveGlue_app_app_apply] at he
        exact congrArg (fun z ↦ z.1.2 hj) he
      · rw [toSieveGlue_app_app_apply]
        apply Subtype.ext
        apply Prod.ext
        · exact z.2 hj
        · funext t
          rfl
    have := NatIso.isIso_of_isIso_app ((toSieveGlue T hT p).app j)
    exact MorphismProperty.rlp_of_isIso _ _
  · let ψ : B ⟶ (sieveGlue T hT p).obj j :=
      { app a := ↾fun b ↦ ⟨(b, fun t ↦ (hj t).elim), fun t ↦ (hj t).elim⟩
        naturality a a' f := by
          refine ConcreteCategory.hom_ext _ _ fun b ↦ ?_
          apply Subtype.ext
          apply Prod.ext
          · rfl
          · funext t
            exact (hj t).elim }
    have hψ : ∀ a b, ψ.app a b = ⟨(b, fun t ↦ (hj t).elim), fun t ↦ (hj t).elim⟩ :=
      fun _ _ ↦ rfl
    have : ∀ a, IsIso (ψ.app a) := by
      intro a
      rw [isIso_iff_bijective]
      refine ⟨fun b b' hb ↦ ?_, fun z ↦ ⟨z.1.1, ?_⟩⟩
      · rw [hψ, hψ] at hb
        exact congrArg (fun z ↦ z.1.1) hb
      · rw [hψ]
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · funext t
          exact (hj t).elim
    have := NatIso.isIso_of_isIso_app ψ
    have e : (toSieveGlue T hT p).app j = p ≫ ψ := by
      refine NatTrans.ext (funext fun a ↦ ConcreteCategory.hom_ext _ _ fun x ↦ ?_)
      simp only [NatTrans.comp_app, types_comp_apply]
      rw [hψ, toSieveGlue_app_app_apply]
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · funext t
        exact (hj t).elim
    rw [e]
    exact (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v)).rlp.comp_mem _ _ hp
      (MorphismProperty.rlp_of_isIso _ _)

end Glue

section SieveMono

variable {C : Type v} [SmallCategory C] {P₀ P₁ : ObjectProperty C} (h : P₀ ≤ P₁)
  (hP₀ : ∀ ⦃c c' : C⦄, (c ⟶ c') → P₀ c' → P₀ c) (F : C ⥤ Aᵒᵖ ⥤ Type v)
  {E B : Aᵒᵖ ⥤ Type v} (p : E ⟶ B)

noncomputable def sieveGlueOfSquare (u : colimit (P₀.ι ⋙ F) ⟶ E)
    (v : colimit (P₁.ι ⋙ F) ⟶ B) (w : u ≫ p = sievePre h F ≫ v) :
    P₁.ι ⋙ F ⟶
      sieveGlue (fun s : P₁.FullSubcategory ↦ P₀ s.obj) (fun _ _ φ ↦ hP₀ (P₁.ι.map φ)) p where
  app s :=
    { app a := ↾fun y ↦ ⟨((colimit.ι (P₁.ι ⋙ F) s ≫ v).app a y,
        fun t ↦ (colimit.ι (P₀.ι ⋙ F) ⟨s.obj, t⟩ ≫ u).app a y), fun t ↦ by
          have hι : colimit.ι (P₀.ι ⋙ F) ⟨s.obj, t⟩ ≫ sievePre h F = colimit.ι (P₁.ι ⋙ F) s :=
            ι_sievePre h F _
          have hw : colimit.ι (P₀.ι ⋙ F) ⟨s.obj, t⟩ ≫ u ≫ p = colimit.ι (P₁.ι ⋙ F) s ≫ v := by
            rw [w, ← Category.assoc, hι]
          simpa using congr_arg (fun k ↦ k.app a y) hw⟩
      naturality a a' f := by
        refine ConcreteCategory.hom_ext _ _ fun y ↦ ?_
        apply Subtype.ext
        apply Prod.ext
        · exact NatTrans.naturality_apply (colimit.ι (P₁.ι ⋙ F) s ≫ v) f y
        · funext t
          exact NatTrans.naturality_apply (colimit.ι (P₀.ι ⋙ F) ⟨s.obj, t⟩ ≫ u) f y }
  naturality s s' φ := by
    refine NatTrans.ext (funext fun a ↦ ConcreteCategory.hom_ext _ _ fun y ↦ ?_)
    apply Subtype.ext
    apply Prod.ext
    · exact congr_arg (fun k ↦ (k ≫ v).app a y) (colimit.w (P₁.ι ⋙ F) φ)
    · funext t
      exact congr_arg (fun k ↦ (k ≫ u).app a y) (colimit.w (P₀.ι ⋙ F)
        (ObjectProperty.homMk (P₁.ι.map φ) :
          (⟨s.obj, hP₀ (P₁.ι.map φ) t⟩ : P₀.FullSubcategory) ⟶ ⟨s'.obj, t⟩))

theorem sieveGlueOfSquare_app_app_apply (u : colimit (P₀.ι ⋙ F) ⟶ E)
    (v : colimit (P₁.ι ⋙ F) ⟶ B) (w : u ≫ p = sievePre h F ≫ v) (s : P₁.FullSubcategory)
    (a : Aᵒᵖ) (y : (F.obj s.obj).obj a) :
    (((sieveGlueOfSquare h hP₀ F p u v w).app s).app a y).1 =
      ((colimit.ι (P₁.ι ⋙ F) s ≫ v).app a y,
        fun t ↦ (colimit.ι (P₀.ι ⋙ F) ⟨s.obj, t⟩ ≫ u).app a y) :=
  rfl

include hP₀ in
theorem mono_sievePre
    (hF : projectiveCofibrations A P₁.FullSubcategory (initial.to (P₁.ι ⋙ F))) :
    Mono (sievePre h F) := by
  have H : (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v)).rlp.llp (sievePre h F) := by
    intro E B p hp
    constructor
    intro u v sq
    obtain ⟨l, -, hl⟩ := exists_lift_of_projectiveCofibrations hF
      (rlp_toSieveGlue_app _ (fun _ _ φ ↦ hP₀ (P₁.ι.map φ)) p hp) (initial.to _)
      (sieveGlueOfSquare h hP₀ F p u v sq.w) (initial.hom_ext _ _)
    have hl' : ∀ s a y,
        ((toSieveGlue _ (fun _ _ φ ↦ hP₀ (P₁.ι.map φ)) p).app s).app a ((l.app s).app a y) =
          ((sieveGlueOfSquare h hP₀ F p u v sq.w).app s).app a y := fun s a y ↦ by
      rw [← hl]
      rfl
    refine ⟨⟨{ l := colimit.desc _ (Cocone.mk E l), fac_left := ?_, fac_right := ?_ }⟩⟩
    · refine colimit.hom_ext fun x ↦ ?_
      rw [ι_sievePre_assoc, colimit.ι_desc]
      refine NatTrans.ext (funext fun a ↦ ConcreteCategory.hom_ext _ _ fun y ↦ ?_)
      have := congr_arg (fun z ↦ z.1.2 x.property) (hl' ((ObjectProperty.ιOfLE h).obj x) a y)
      beta_reduce at this
      rw [toSieveGlue_app_app_apply, sieveGlueOfSquare_app_app_apply] at this
      exact this
    · refine colimit.hom_ext fun s ↦ ?_
      rw [colimit.ι_desc_assoc]
      refine NatTrans.ext (funext fun a ↦ ConcreteCategory.hom_ext _ _ fun y ↦ ?_)
      have := congr_arg (fun z ↦ z.1.1) (hl' s a y)
      beta_reduce at this
      rw [toSieveGlue_app_app_apply, sieveGlueOfSquare_app_app_apply] at this
      exact this
  rw [← monomorphisms_eq_llp_rlp_monomorphisms] at H
  exact H

end SieveMono

section Comparison

variable {X Z : Aᵒᵖ ⥤ Type v}

theorem IsAccessibleALocalizer.mem_of_isRegular_resolution
    [hV : IsAccessibleALocalizer V] (hZ : IsRegular V Z)
    {G : CostructuredArrow yoneda Z ⥤ Aᵒᵖ ⥤ Type v}
    (hG : projectiveCofibrations A _ (initial.to G))
    (π : G ⟶ representablesOver Z) (hπ : ∀ c, V (π.app c))
    (d : colimit G ⟶ Z)
    (hd : ∀ c, colimit.ι G c ≫ d = π.app c ≫ c.hom) : V d := by
  obtain ⟨ℓ, hℓ, -, hℓc⟩ := hV.exists_lift_projectiveReplacementπ hG π hπ
  have he : d = colimMap ℓ ≫ regularizationMap Z := by
    refine colimit.hom_ext fun c => ?_
    rw [hd, ι_colimMap_assoc, ι_regularizationMap]
    exact ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ c.hom) (congr_app hℓ c))).symm
  rw [he]
  exact MorphismProperty.comp_mem _ _ _ hℓc hZ

variable (m : Z ⟶ X) (G : CostructuredArrow yoneda X ⥤ Aᵒᵖ ⥤ Type v)
  (π : G ⟶ representablesOver X)

noncomputable def elementsSieve.lift (s : (elementsSieve m).FullSubcategory) :
    (representablesOver X).obj s.obj ⟶ Z :=
  (show ∃ x : yoneda.obj s.obj.left ⟶ Z, x ≫ m = s.obj.hom from s.property).choose

@[reassoc (attr := simp)]
theorem elementsSieve.lift_comp (s : (elementsSieve m).FullSubcategory) :
    elementsSieve.lift m s ≫ m = s.obj.hom :=
  (show ∃ x : yoneda.obj s.obj.left ⟶ Z, x ≫ m = s.obj.hom from s.property).choose_spec

variable [Mono m]

noncomputable def sieveComparison : colimit ((elementsSieve m).ι ⋙ G) ⟶ Z :=
  colimit.desc _
    { pt := Z
      ι :=
        { app s := π.app s.obj ≫ elementsSieve.lift m s
          naturality s s' φ := by
            refine (cancel_mono m).1 ?_
            simp only [Functor.comp_obj, ObjectProperty.ι_obj, Functor.const_obj_obj,
              Functor.comp_map, ObjectProperty.ι_map, NatTrans.naturality_assoc,
              CostructuredArrow.proj_map, Category.assoc, elementsSieve.lift_comp,
              Functor.const_obj_map, Category.comp_id]
            exact congrArg (π.app s.obj ≫ ·) (CostructuredArrow.w φ.hom) } }

@[reassoc]
theorem ι_sieveComparison_comp (s : (elementsSieve m).FullSubcategory) :
    colimit.ι ((elementsSieve m).ι ⋙ G) s ≫ sieveComparison m G π ≫ m =
      π.app s.obj ≫ s.obj.hom := by
  rw [sieveComparison, colimit.ι_desc_assoc]
  exact (Category.assoc _ _ _).trans (congrArg (π.app s.obj ≫ ·) (elementsSieve.lift_comp m s))

end Comparison

theorem IsAccessibleALocalizer.sieveComparison_mem [hV : IsAccessibleALocalizer V]
    {X Z : Aᵒᵖ ⥤ Type v} (m : Z ⟶ X) [Mono m] (hZ : IsRegular V Z) :
    V (sieveComparison m ((projectiveReplacement A _).obj (representablesOver X))
      ((projectiveReplacementπ A _).app (representablesOver X))) := by
  let Q := (projectiveReplacement A (CostructuredArrow yoneda X)).obj (representablesOver X)
  let π := (projectiveReplacementπ A (CostructuredArrow yoneda X)).app (representablesOver X)
  have := (toElementsSieve m).asEquivalence.isRightAdjoint_functor
  have he : IsIso (colimit.pre ((elementsSieve m).ι ⋙ Q) (toElementsSieve m)) :=
    inferInstance
  have hπ : ∀ c, V (π.app c) := fun c ↦ hV.isALocalizer.rlp_monomorphisms_le _
    (rlp_monomorphisms_projectiveReplacementπ_app _ c)
  have hQ : projectiveCofibrations A (CostructuredArrow yoneda Z)
      (initial.to (CostructuredArrow.map m ⋙ Q)) :=
    projectiveCofibrations_initial_to_comp _ (projectiveCofibrations_whiskerLeft_map m
      (projectiveCofibrations_initial_to_projectiveReplacement _))
  have hd := hV.mem_of_isRegular_resolution hZ hQ
    (Functor.whiskerLeft (CostructuredArrow.map m) π) (fun c ↦ hπ _)
    (colimit.pre ((elementsSieve m).ι ⋙ Q) (toElementsSieve m) ≫ sieveComparison m Q π)
    fun c ↦ (cancel_mono m).1 (by
      have := colimit.ι_pre_assoc ((elementsSieve m).ι ⋙ Q) (toElementsSieve m) c
        (sieveComparison m Q π ≫ m)
      rw [ι_sieveComparison_comp] at this
      exact (Category.assoc _ _ _).trans
        ((congrArg (colimit.ι (CostructuredArrow.map m ⋙ Q) c ≫ ·)
          (Category.assoc _ _ _)).trans (this.trans (Category.assoc _ _ _).symm)))
  exact hV.isALocalizer.hasTwoOutOfThreeProperty.of_precomp
    (colimit.pre ((elementsSieve m).ι ⋙ Q) (toElementsSieve m)) _
    (hV.isALocalizer.isomorphisms_le _ (isomorphisms.infer_property _)) hd

end Atoms.Homotopical
