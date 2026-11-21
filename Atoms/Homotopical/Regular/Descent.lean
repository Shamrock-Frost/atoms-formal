import Atoms.Homotopical.Regular.Slice
import Atoms.Homotopical.Localizer.RightProper

open CategoryTheory Limits Opposite Atoms Atoms.Homotopical MorphismProperty

namespace Atoms.Homotopical

universe v

section Comma

variable {A : Type v} [SmallCategory A] {B : Aᵒᵖ ⥤ Type v}
  {D : CostructuredArrow yoneda B ⥤ Aᵒᵖ ⥤ Type v} (s : Cocone D) (p : s.pt ⟶ B)
  (t : D ⟶ representablesOver B) (c : CostructuredArrow yoneda B)
  (hc : IsPullback (t.app c : D.obj c ⟶ yoneda.obj c.left) (s.ι.app c) c.hom p)

noncomputable def pullbackCommaFunctor :
    CostructuredArrow yoneda (D.obj c) ⥤
      CostructuredArrow (CostructuredArrow.map p) c where
  obj x :=
    let e : CostructuredArrow yoneda s.pt :=
      CostructuredArrow.mk (x.hom ≫ s.ι.app c)
    let k : x.left ⟶ c.left := yoneda.preimage (x.hom ≫ t.app c)
    let h : (CostructuredArrow.map p).obj e ⟶ c := CostructuredArrow.homMk k (by
      change yoneda.map k ≫ c.hom = e.hom ≫ p
      rw [yoneda.map_preimage]
      simp only [e, CostructuredArrow.mk_hom_eq_self, Category.assoc]
      exact congrArg (x.hom ≫ ·) hc.w)
    CostructuredArrow.mk h
  map {x y} f := CostructuredArrow.homMk
    (CostructuredArrow.homMk f.left (by
      change yoneda.map f.left ≫ (y.hom ≫ s.ι.app c) =
        x.hom ≫ s.ι.app c
      rw [← Category.assoc, CostructuredArrow.w f]))
    (by
      apply CostructuredArrow.hom_ext
      change f.left ≫ yoneda.preimage (y.hom ≫ t.app c) =
        yoneda.preimage (x.hom ≫ t.app c)
      apply yoneda.map_injective
      simp only [yoneda.map_comp, yoneda.map_preimage]
      rw [← Category.assoc, CostructuredArrow.w f])
  map_id x := by
    ext
    rfl
  map_comp f g := by
    ext
    rfl

noncomputable def pullbackCommaInverse :
    CostructuredArrow (CostructuredArrow.map p) c ⥤
      CostructuredArrow yoneda (D.obj c) where
  obj j := CostructuredArrow.mk
    (hc.lift (yoneda.map j.hom.left) j.left.hom (by
      exact CostructuredArrow.w j.hom))
  map {j k} f := CostructuredArrow.homMk f.left.left (by
    have hf : f.left.left ≫ k.hom.left = j.hom.left :=
      congrArg CommaMorphism.left (CostructuredArrow.w f)
    have hk₁ : hc.lift (yoneda.map k.hom.left) k.left.hom
        (CostructuredArrow.w k.hom) ≫ t.app c = yoneda.map k.hom.left :=
      hc.lift_fst _ _ _
    have hj₁ : hc.lift (yoneda.map j.hom.left) j.left.hom
        (CostructuredArrow.w j.hom) ≫ t.app c = yoneda.map j.hom.left :=
      hc.lift_fst _ _ _
    have hk₂ : hc.lift (yoneda.map k.hom.left) k.left.hom
        (CostructuredArrow.w k.hom) ≫ s.ι.app c = k.left.hom :=
      hc.lift_snd _ _ _
    have hj₂ : hc.lift (yoneda.map j.hom.left) j.left.hom
        (CostructuredArrow.w j.hom) ≫ s.ι.app c = j.left.hom :=
      hc.lift_snd _ _ _
    apply hc.hom_ext
    · dsimp only [CostructuredArrow.mk_hom_eq_self]
      rw [Category.assoc, hk₁, hj₁]
      exact (yoneda.map_comp f.left.left k.hom.left).symm.trans
        (congrArg yoneda.map hf)
    · dsimp only [CostructuredArrow.mk_hom_eq_self]
      rw [Category.assoc, hk₂, hj₂]
      exact CostructuredArrow.w f.left)
  map_id j := by
    ext
    rfl
  map_comp f g := by
    ext
    rfl

private theorem pullbackCommaFunctor_faithful :
    (pullbackCommaFunctor s p t c hc).Faithful := by
  refine ⟨fun {x y} f g h => ?_⟩
  apply CostructuredArrow.ext f g
  exact congrArg (fun z => z.left.left) h

private theorem pullbackCommaFunctor_full :
    (pullbackCommaFunctor s p t c hc).Full := by
  refine ⟨fun {x y} m => ?_⟩
  have hm : m.left.left ≫ yoneda.preimage (y.hom ≫ t.app c) =
      yoneda.preimage (x.hom ≫ t.app c) := by
    exact congrArg CommaMorphism.left (CostructuredArrow.w m)
  have ht : yoneda.map m.left.left ≫ (y.hom ≫ t.app c) = x.hom ≫ t.app c := by
    have h := congrArg yoneda.map hm
    rw [yoneda.map_comp, yoneda.map_preimage] at h
    exact h.trans (yoneda.map_preimage _)
  have hs : yoneda.map m.left.left ≫ (y.hom ≫ s.ι.app c) =
      x.hom ≫ s.ι.app c := by
    exact CostructuredArrow.w m.left
  have hxy : yoneda.map m.left.left ≫ y.hom = x.hom := by
    apply hc.hom_ext
    · exact (Category.assoc _ _ _).trans ht
    · exact (Category.assoc _ _ _).trans hs
  refine ⟨CostructuredArrow.homMk m.left.left hxy, ?_⟩
  apply CostructuredArrow.ext
  apply CostructuredArrow.ext
  rfl

private theorem pullbackCommaFunctor_essSurj :
    (pullbackCommaFunctor s p t c hc).EssSurj := by
  let K := pullbackCommaFunctor s p t c hc
  refine ⟨fun j => ?_⟩
  let x := (pullbackCommaInverse s p t c hc).obj j
  let h₁ : (K.obj x).left ≅ j.left := CostructuredArrow.isoMk
    (Iso.refl j.left.left) (by
      change yoneda.map (𝟙 j.left.left) ≫ j.left.hom = x.hom ≫ s.ι.app c
      rw [yoneda.map_id, Category.id_comp]
      exact (hc.lift_snd _ _ _).symm)
  have h₂ : K.obj x ≅ j := CostructuredArrow.isoMk h₁ (by
    apply CostructuredArrow.ext
    change (𝟙 j.left.left) ≫ j.hom.left =
      yoneda.preimage (x.hom ≫ t.app c)
    rw [Category.id_comp]
    have hfst : x.hom ≫ (t.app c : D.obj c ⟶ yoneda.obj c.left) =
        yoneda.map j.hom.left := hc.lift_fst _ _ _
    rw [hfst]
    exact (yoneda.preimage_map _).symm)
  exact ⟨x, ⟨h₂⟩⟩

theorem isEquivalence_pullbackCommaFunctor :
    (pullbackCommaFunctor s p t c hc).IsEquivalence :=
  ⟨pullbackCommaFunctor_faithful s p t c hc,
    pullbackCommaFunctor_full s p t c hc,
    pullbackCommaFunctor_essSurj s p t c hc⟩

end Comma

noncomputable def pullbackRepresentablesUnit {A : Type v} [SmallCategory A]
    {B : Aᵒᵖ ⥤ Type v} {D : CostructuredArrow yoneda B ⥤ Aᵒᵖ ⥤ Type v}
    (s : Cocone D) (p : s.pt ⟶ B) (t : D ⟶ representablesOver B)
    (hpb : ∀ c, IsPullback (t.app c : D.obj c ⟶ yoneda.obj c.left)
      (s.ι.app c) c.hom p) :
    representablesOver s.pt ⟶ CostructuredArrow.map p ⋙ D where
  app d := (hpb ((CostructuredArrow.map p).obj d)).lift (𝟙 _) d.hom (by cat_disch)
  naturality d e f := by
    let u : CostructuredArrow yoneda s.pt ⥤ CostructuredArrow yoneda B :=
      CostructuredArrow.map p
    let Ld : yoneda.obj d.left ⟶ D.obj (u.obj d) :=
      (hpb (u.obj d)).lift (𝟙 _) d.hom (by cat_disch)
    let Le : yoneda.obj e.left ⟶ D.obj (u.obj e) :=
      (hpb (u.obj e)).lift (𝟙 _) e.hom (by cat_disch)
    have hd₁ : Ld ≫ t.app (u.obj d) = 𝟙 _ := (hpb (u.obj d)).lift_fst _ _ _
    have he₁ : Le ≫ t.app (u.obj e) = 𝟙 _ := (hpb (u.obj e)).lift_fst _ _ _
    have hd₂ : Ld ≫ s.ι.app (u.obj d) = d.hom := (hpb (u.obj d)).lift_snd _ _ _
    have he₂ : Le ≫ s.ι.app (u.obj e) = e.hom := (hpb (u.obj e)).lift_snd _ _ _
    change yoneda.map f.left ≫ Le = Ld ≫ D.map (u.map f)
    apply (hpb (u.obj e)).hom_ext
    · have hl : (yoneda.map f.left ≫ Le) ≫ t.app (u.obj e) =
          yoneda.map f.left := by
        rw [Category.assoc, he₁]
        exact Category.comp_id _
      have hr : (Ld ≫ D.map (u.map f)) ≫ t.app (u.obj e) =
          yoneda.map f.left := by
        rw [Category.assoc, t.naturality, ← Category.assoc, hd₁]
        exact Category.id_comp _
      exact hl.trans hr.symm
    · have hl : (yoneda.map f.left ≫ Le) ≫ s.ι.app (u.obj e) =
          d.hom := by
        rw [Category.assoc, he₂]
        exact CostructuredArrow.w f
      have hr : (Ld ≫ D.map (u.map f)) ≫ s.ι.app (u.obj e) =
          d.hom := by
        rw [Category.assoc, s.w]
        exact hd₂
      exact hl.trans hr.symm

noncomputable def lanToPullback {A : Type v} [SmallCategory A]
    {B : Aᵒᵖ ⥤ Type v} {D : CostructuredArrow yoneda B ⥤ Aᵒᵖ ⥤ Type v}
    (s : Cocone D) (p : s.pt ⟶ B) (t : D ⟶ representablesOver B)
    (hpb : ∀ c, IsPullback (t.app c : D.obj c ⟶ yoneda.obj c.left)
      (s.ι.app c) c.hom p) :
    (CostructuredArrow.map p).pointwiseLeftKanExtension
      ((projectiveReplacement A (CostructuredArrow yoneda s.pt)).obj
        (representablesOver s.pt)) ⟶ D :=
  let Q := (projectiveReplacement A (CostructuredArrow yoneda s.pt)).obj
    (representablesOver s.pt)
  let u : CostructuredArrow yoneda s.pt ⥤ CostructuredArrow yoneda B :=
    CostructuredArrow.map p
  (u.pointwiseLeftKanExtension Q).descOfIsLeftKanExtension
    (u.pointwiseLeftKanExtensionUnit Q) D
      ((projectiveReplacementπ A _).app (representablesOver s.pt) ≫
        pullbackRepresentablesUnit s p t hpb)

@[reassoc]
theorem ι_lanToPullback_app {A : Type v} [SmallCategory A]
    {B : Aᵒᵖ ⥤ Type v} {D : CostructuredArrow yoneda B ⥤ Aᵒᵖ ⥤ Type v}
    (s : Cocone D) (p : s.pt ⟶ B) (t : D ⟶ representablesOver B)
    (hpb : ∀ c, IsPullback (t.app c : D.obj c ⟶ yoneda.obj c.left)
      (s.ι.app c) c.hom p) (c : CostructuredArrow yoneda B)
    (j : CostructuredArrow (CostructuredArrow.map p) c) :
    colimit.ι (CostructuredArrow.proj (CostructuredArrow.map p) c ⋙
      (projectiveReplacement A (CostructuredArrow yoneda s.pt)).obj
        (representablesOver s.pt)) j ≫ (lanToPullback s p t hpb).app c =
      ((projectiveReplacementπ A _).app (representablesOver s.pt)).app j.left ≫
        (hpb c).lift (yoneda.map j.hom.left) j.left.hom
          (CostructuredArrow.w j.hom) := by
  let u : CostructuredArrow yoneda s.pt ⥤ CostructuredArrow yoneda B :=
    CostructuredArrow.map p
  let L : yoneda.obj j.left.left ⟶ D.obj (u.obj j.left) :=
    (hpb (u.obj j.left)).lift (𝟙 _) j.left.hom (by cat_disch)
  have hunit : L ≫ D.map j.hom =
      (hpb c).lift (yoneda.map j.hom.left) j.left.hom
        (CostructuredArrow.w j.hom) := by
    apply (hpb c).hom_ext
    · have hr : (hpb c).lift (yoneda.map j.hom.left) j.left.hom
          (CostructuredArrow.w j.hom) ≫ t.app c =
          yoneda.map j.hom.left := (hpb c).lift_fst _ _ _
      rw [hr, Category.assoc, t.naturality, ← Category.assoc]
      have h₁ : L ≫ t.app (u.obj j.left) = 𝟙 _ :=
        (hpb (u.obj j.left)).lift_fst _ _ _
      change (L ≫ t.app (u.obj j.left)) ≫ yoneda.map j.hom.left = _
      rw [h₁]
      exact Category.id_comp _
    · have hr : (hpb c).lift (yoneda.map j.hom.left) j.left.hom
          (CostructuredArrow.w j.hom) ≫ s.ι.app c =
          j.left.hom := (hpb c).lift_snd _ _ _
      rw [hr, Category.assoc, s.w]
      exact (hpb (u.obj j.left)).lift_snd _ _ _
  rw [lanToPullback, Functor.pointwiseLeftKanExtension_desc_app]
  erw [colimit.ι_desc]
  simp only [Functor.costructuredArrowMapCocone_ι_app, NatTrans.comp_app]
  change _ ≫ (L ≫ D.map j.hom) = _
  rw [hunit]
  rfl

private theorem mem_of_isRegular_resolution_of_final {A : Type v} [SmallCategory A]
    {V : MorphismProperty (Aᵒᵖ ⥤ Type v)} [hV : IsAccessibleALocalizer V] {Z : Aᵒᵖ ⥤ Type v}
    (hZ : IsRegular V Z) {J : Type v} [SmallCategory J]
    (κ : CostructuredArrow yoneda Z ⥤ J) [κ.Final] {G : J ⥤ Aᵒᵖ ⥤ Type v}
    (hG : projectiveCofibrations A _ (initial.to (κ ⋙ G)))
    (ρ : κ ⋙ G ⟶ representablesOver Z) (hρ : ∀ c, V (ρ.app c)) (d : colimit G ⟶ Z)
    (hd : ∀ c, colimit.ι G (κ.obj c) ≫ d = ρ.app c ≫ c.hom) : V d := by
  have h := hV.mem_of_isRegular_resolution hZ hG ρ hρ (colimit.pre G κ ≫ d) (by
    intro c
    rw [colimit.ι_pre_assoc, hd])
  exact MorphismProperty.of_precomp _ _ _
    (hV.isALocalizer.isomorphisms_le _ (isomorphisms.infer_property _)) h

theorem IsAccessibleALocalizer.lanToPullback_app_mem
    {A : Type v} [SmallCategory A] {V : MorphismProperty (Aᵒᵖ ⥤ Type v)}
    [hV : IsAccessibleALocalizer V] [hR : IsRegularALocalizer V]
    {B : Aᵒᵖ ⥤ Type v} {D : CostructuredArrow yoneda B ⥤ Aᵒᵖ ⥤ Type v}
    (s : Cocone D) (p : s.pt ⟶ B) (t : D ⟶ representablesOver B)
    (hpb : ∀ c, IsPullback (t.app c : D.obj c ⟶ yoneda.obj c.left)
      (s.ι.app c) c.hom p) (c : CostructuredArrow yoneda B) :
    V ((lanToPullback s p t hpb).app c) := by
  let u : CostructuredArrow yoneda s.pt ⥤ CostructuredArrow yoneda B :=
    CostructuredArrow.map p
  let P := (projectiveReplacement A (CostructuredArrow yoneda s.pt)).obj
    (representablesOver s.pt)
  let πP := (projectiveReplacementπ A _).app (representablesOver s.pt)
  let κ := pullbackCommaFunctor s p t c (hpb c)
  let G := CostructuredArrow.proj u c ⋙ P
  let ρ : κ ⋙ G ⟶ representablesOver (D.obj c) :=
    { app := fun x => πP.app (κ.obj x).left
      naturality := by
        intro x y f
        exact πP.naturality (κ.map f).left }
  let : κ.IsEquivalence := isEquivalence_pullbackCommaFunctor s p t c (hpb c)
  have hProj : projectiveCofibrations A _ (initial.to G) :=
    projectiveCofibrations_initial_to_comp (CostructuredArrow.proj u c)
      (projectiveCofibrations_whiskerLeft_proj u c
        (projectiveCofibrations_initial_to_projectiveReplacement _))
  have hG : projectiveCofibrations A _ (initial.to (κ ⋙ G)) :=
    projectiveCofibrations_initial_to_comp κ
      (projectiveCofibrations_whiskerLeft_of_isRightAdjoint κ hProj)
  apply mem_of_isRegular_resolution_of_final (hR.isRegular (D.obj c)) κ hG ρ
    (fun x => hV.projectiveReplacementπ_app_mem _ (κ.obj x).left)
    ((lanToPullback s p t hpb).app c)
  intro x
  rw [ι_lanToPullback_app]
  have h₁ : yoneda.map (κ.obj x).hom.left = x.hom ≫ t.app c := by
    change yoneda.map (yoneda.preimage (x.hom ≫ t.app c)) = _
    exact yoneda.map_preimage _
  have h₂ : (κ.obj x).left.hom = x.hom ≫ s.ι.app c := rfl
  have hl : (hpb c).lift (yoneda.map (κ.obj x).hom.left)
      (κ.obj x).left.hom (CostructuredArrow.w (κ.obj x).hom) = x.hom := by
    apply (hpb c).hom_ext
    · exact ((hpb c).lift_fst _ _ _).trans h₁
    · exact ((hpb c).lift_snd _ _ _).trans h₂
  change πP.app (κ.obj x).left ≫ _ = πP.app (κ.obj x).left ≫ x.hom
  exact congrArg (πP.app (κ.obj x).left ≫ ·) hl

theorem colimitIsoOfIsLeftKanExtension_inv_comp_lanToPullback
    {A : Type v} [SmallCategory A]
    {B : Aᵒᵖ ⥤ Type v} {D : CostructuredArrow yoneda B ⥤ Aᵒᵖ ⥤ Type v}
    (s : Cocone D) (p : s.pt ⟶ B) (t : D ⟶ representablesOver B)
    (hpb : ∀ c, IsPullback (t.app c : D.obj c ⟶ yoneda.obj c.left)
      (s.ι.app c) c.hom p) :
    (((CostructuredArrow.map p).pointwiseLeftKanExtension
      ((projectiveReplacement A (CostructuredArrow yoneda s.pt)).obj
        (representablesOver s.pt))).colimitIsoOfIsLeftKanExtension
        ((CostructuredArrow.map p).pointwiseLeftKanExtensionUnit
          ((projectiveReplacement A (CostructuredArrow yoneda s.pt)).obj
            (representablesOver s.pt)))).inv ≫
      colimMap (lanToPullback s p t hpb) ≫ colimit.desc D s =
      regularizationMap s.pt := by
  let u : CostructuredArrow yoneda s.pt ⥤ CostructuredArrow yoneda B :=
    CostructuredArrow.map p
  let P := (projectiveReplacement A (CostructuredArrow yoneda s.pt)).obj
    (representablesOver s.pt)
  let j (d : CostructuredArrow yoneda s.pt) : CostructuredArrow u (u.obj d) :=
    CostructuredArrow.mk (𝟙 (u.obj d))
  apply colimit.hom_ext
  intro d
  rw [Functor.ι_colimitIsoOfIsLeftKanExtension_inv_assoc,
    Functor.pointwiseLeftKanExtensionUnit_app,
    ι_colimMap_assoc]
  simp only [colimit.ι_desc, ι_regularizationMap]
  have hfac : (u.pointwiseLeftKanExtensionUnit P).app d ≫
      (lanToPullback s p t hpb).app (u.obj d) =
      ((projectiveReplacementπ A _).app (representablesOver s.pt)).app d ≫
        (pullbackRepresentablesUnit s p t hpb).app d := by
    exact (u.pointwiseLeftKanExtension P).descOfIsLeftKanExtension_fac_app
      (u.pointwiseLeftKanExtensionUnit P) D
        ((projectiveReplacementπ A _).app (representablesOver s.pt) ≫
          pullbackRepresentablesUnit s p t hpb) d
  have hsnd : (pullbackRepresentablesUnit s p t hpb).app d ≫
      s.ι.app (u.obj d) = d.hom :=
    (hpb (u.obj d)).lift_snd _ _ _
  change (u.pointwiseLeftKanExtensionUnit P).app d ≫
    ((lanToPullback s p t hpb).app (u.obj d) ≫ s.ι.app (u.obj d)) = _
  rw [← Category.assoc, hfac, Category.assoc, hsnd]

theorem IsAccessibleALocalizer.colimMap_desc_mem_of_comparison
    {A I : Type v} [SmallCategory A] [SmallCategory I]
    {V : MorphismProperty (Aᵒᵖ ⥤ Type v)} [hV : IsAccessibleALocalizer V]
    {D G H : I ⥤ Aᵒᵖ ⥤ Type v} (s : Cocone D)
    (hG : projectiveCofibrations A I (initial.to G))
    (hH : projectiveCofibrations A I (initial.to H))
    (α : G ⟶ D) (hα : ∀ i, V (α.app i))
    (β : H ⟶ D) (hβ : ∀ i, V (β.app i))
    (hβs : V (colimMap β ≫ colimit.desc D s)) :
    V (colimMap α ≫ colimit.desc D s) := by
  let π : (projectiveReplacement A I).obj D ⟶ D := (projectiveReplacementπ A I).app D
  obtain ⟨ℓH, hℓH, -, hcolH⟩ := hV.exists_lift_projectiveReplacementπ hH β hβ
  have hcompH : colimMap ℓH ≫ colimMap π = colimMap β := by
    rw [colimMap_eq, colimMap_eq, colimMap_eq, ← Functor.map_comp, hℓH]
  have hQaug : V (colimMap π ≫ colimit.desc D s) := by
    apply MorphismProperty.of_precomp _ _ _ hcolH
    rw [← Category.assoc, hcompH]
    exact hβs
  obtain ⟨ℓG, hℓG, -, hcolG⟩ := hV.exists_lift_projectiveReplacementπ hG α hα
  have hcompG : colimMap ℓG ≫ colimMap π = colimMap α := by
    rw [colimMap_eq, colimMap_eq, colimMap_eq, ← Functor.map_comp, hℓG]
  rw [← hcompG, Category.assoc]
  exact MorphismProperty.comp_mem _ _ _ hcolG hQaug

theorem IsAccessibleALocalizer.colimMap_desc_mem_of_isPullback
    {A : Type v} [SmallCategory A] {V : MorphismProperty (Aᵒᵖ ⥤ Type v)}
    [hV : IsAccessibleALocalizer V] [hR : IsRegularALocalizer V]
    {B : Aᵒᵖ ⥤ Type v}
    (D : CostructuredArrow yoneda B ⥤ Aᵒᵖ ⥤ Type v) (s : Cocone D)
    (p : s.pt ⟶ B) (t : D ⟶ representablesOver B)
    (hpb : ∀ c, IsPullback (t.app c : D.obj c ⟶ yoneda.obj c.left)
      (s.ι.app c) c.hom p)
    {G : CostructuredArrow yoneda B ⥤ Aᵒᵖ ⥤ Type v}
    (hG : projectiveCofibrations A _ (initial.to G))
    (α : G ⟶ D) (hα : ∀ c, V (α.app c)) :
    V (colimMap α ≫ colimit.desc D s) := by
  let u : CostructuredArrow yoneda s.pt ⥤ CostructuredArrow yoneda B :=
    CostructuredArrow.map p
  let P := (projectiveReplacement A (CostructuredArrow yoneda s.pt)).obj
    (representablesOver s.pt)
  let H := u.pointwiseLeftKanExtension P
  let β : H ⟶ D := lanToPullback s p t hpb
  let ξ := H.colimitIsoOfIsLeftKanExtension (u.pointwiseLeftKanExtensionUnit P)
  have hH : projectiveCofibrations A _ (initial.to H) :=
    projectiveCofibrations_initial_to_pointwiseLeftKanExtension u
      (projectiveCofibrations_initial_to_projectiveReplacement _)
  have hξ : V ξ.inv :=
    hV.isALocalizer.isomorphisms_le _ (isomorphisms.infer_property _)
  have hβs : V (colimMap β ≫ colimit.desc D s) := by
    apply MorphismProperty.of_precomp _ _ _ hξ
    rw [colimitIsoOfIsLeftKanExtension_inv_comp_lanToPullback]
    exact hR.isRegular s.pt
  exact hV.colimMap_desc_mem_of_comparison s hG hH α hα β
    (hV.lanToPullback_app_mem s p t hpb) hβs

theorem IsAccessibleALocalizer.colimMap_projectiveReplacementπ_desc_mem_of_isPullback
    {A : Type v} [SmallCategory A] {V : MorphismProperty (Aᵒᵖ ⥤ Type v)}
    [hV : IsAccessibleALocalizer V] [IsRegularALocalizer V]
    {B : Aᵒᵖ ⥤ Type v}
    (D : CostructuredArrow yoneda B ⥤ Aᵒᵖ ⥤ Type v) (s : Cocone D)
    (p : s.pt ⟶ B) (t : D ⟶ representablesOver B)
    (hpb : ∀ c, IsPullback (t.app c : D.obj c ⟶ yoneda.obj c.left)
      (s.ι.app c) c.hom p) :
    V (colimMap ((projectiveReplacementπ A _).app D) ≫ colimit.desc D s) := by
  exact hV.colimMap_desc_mem_of_isPullback D s p t hpb
    (projectiveCofibrations_initial_to_projectiveReplacement D)
    ((projectiveReplacementπ A _).app D)
    (hV.projectiveReplacementπ_app_mem D)

noncomputable def pullbackRepresentables {A : Type v} [SmallCategory A]
    {E B : Aᵒᵖ ⥤ Type v} (p : E ⟶ B) : CostructuredArrow yoneda B ⥤ (Aᵒᵖ ⥤ Type v) where
  obj b := pullback b.hom p
  map f := baseChangeLift.{v, v} (yoneda.map f.left) _ p f.w
  map_id b := by
    apply pullback.hom_ext <;> simp
  map_comp {b c d} f g := by
    have hf : yoneda.map f.left ≫ c.hom = b.hom := by simp [f.w]
    have hg : yoneda.map g.left ≫ d.hom = c.hom := by simp [g.w]
    have hfg : yoneda.map (f ≫ g).left ≫ d.hom = b.hom := by
      simp
    change baseChangeLift.{v, v} (yoneda.map (f ≫ g).left) d.hom p hfg =
      baseChangeLift.{v, v} (yoneda.map f.left) c.hom p hf ≫
        baseChangeLift.{v, v} (yoneda.map g.left) d.hom p hg
    apply pullback.hom_ext
    · simp only [baseChangeLift, Category.assoc, pullback.lift_fst]
      rw [← Category.assoc, pullback.lift_fst]
      simp
    · simp only [baseChangeLift, Category.assoc, pullback.lift_snd]

noncomputable def pullbackRepresentablesCocone {A : Type v} [SmallCategory A]
    {E B : Aᵒᵖ ⥤ Type v} (p : E ⟶ B) : Cocone (pullbackRepresentables p) where
  pt := E
  ι :=
    { app := fun b => pullback.snd b.hom p
      naturality := by
        intro b c f
        exact baseChangeLift_snd.{v, v} (yoneda.map f.left) _ p f.w }

noncomputable def pullbackResolutionMap {A : Type v} [SmallCategory A]
    {E B : Aᵒᵖ ⥤ Type v} (p : E ⟶ B) :
    colimit ((projectiveReplacement A (CostructuredArrow yoneda B)).obj
      (pullbackRepresentables p)) ⟶ E :=
  colimMap ((projectiveReplacementπ A _).app _) ≫ colimit.desc _ (pullbackRepresentablesCocone p)

noncomputable def pullbackRepresentablesFst {A : Type v} [SmallCategory A]
    {E B : Aᵒᵖ ⥤ Type v} (p : E ⟶ B) :
    pullbackRepresentables p ⟶ representablesOver B where
  app c := pullback.fst c.hom p
  naturality _ _ f := baseChangeLift_fst.{v, v} (yoneda.map f.left) _ p f.w

theorem pullbackResolutionMap_mem {A : Type v} [SmallCategory A]
    (V : MorphismProperty (Aᵒᵖ ⥤ Type v)) [hV : IsAccessibleALocalizer V]
    [IsRegularALocalizer V] {E B : Aᵒᵖ ⥤ Type v} (p : E ⟶ B) :
    V (pullbackResolutionMap p) := by
  exact hV.colimMap_projectiveReplacementπ_desc_mem_of_isPullback
    (pullbackRepresentables p) (pullbackRepresentablesCocone p) p
    (pullbackRepresentablesFst p)
    (fun c => IsPullback.of_hasPullback c.hom p)

noncomputable def fibreMap {A : Type v} [SmallCategory A]
    {X Y S K : Aᵒᵖ ⥤ Type v} (f : X ⟶ Y) (q : Y ⟶ S) (b : K ⟶ S) :
    pullback b (f ≫ q) ⟶ pullback b q :=
  pullback.lift (pullback.fst b (f ≫ q)) (pullback.snd b (f ≫ q) ≫ f)
    (by simpa only [Category.assoc] using pullback.condition (f := b) (g := f ≫ q))

@[reassoc (attr := simp)]
theorem fibreMap_fst {A : Type v} [SmallCategory A]
    {X Y S K : Aᵒᵖ ⥤ Type v} (f : X ⟶ Y) (q : Y ⟶ S) (b : K ⟶ S) :
    fibreMap f q b ≫ pullback.fst b q = pullback.fst b (f ≫ q) :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem fibreMap_snd {A : Type v} [SmallCategory A]
    {X Y S K : Aᵒᵖ ⥤ Type v} (f : X ⟶ Y) (q : Y ⟶ S) (b : K ⟶ S) :
    fibreMap f q b ≫ pullback.snd b q = pullback.snd b (f ≫ q) ≫ f :=
  pullback.lift_snd _ _ _

noncomputable def pullbackRepresentablesFibreMap {A : Type v} [SmallCategory A]
    {X Y S : Aᵒᵖ ⥤ Type v} (f : X ⟶ Y) (q : Y ⟶ S) :
    pullbackRepresentables (f ≫ q) ⟶ pullbackRepresentables q where
  app b := fibreMap f q b.hom
  naturality b c g := by
    have hg : yoneda.map g.left ≫ c.hom = b.hom := by simp [g.w]
    change baseChangeLift.{v, v} (yoneda.map g.left) c.hom (f ≫ q) hg ≫ fibreMap f q c.hom =
      fibreMap f q b.hom ≫ baseChangeLift.{v, v} (yoneda.map g.left) c.hom q hg
    apply pullback.hom_ext <;> simp

theorem colimMap_projectiveReplacement_map_comp_pullbackResolutionMap {A : Type v}
    [SmallCategory A] {X Y S : Aᵒᵖ ⥤ Type v} (f : X ⟶ Y) (q : Y ⟶ S) :
    colimMap ((projectiveReplacement A (CostructuredArrow yoneda S)).map
        (pullbackRepresentablesFibreMap f q)) ≫ pullbackResolutionMap q =
      pullbackResolutionMap (f ≫ q) ≫ f := by
  have key : ∀ {F F' G G' : CostructuredArrow yoneda S ⥤ Aᵒᵖ ⥤ Type v} (φ : F ⟶ F')
      (α : F ⟶ G) (α' : F' ⟶ G') (τ : G ⟶ G') (_ : φ ≫ α' = α ≫ τ) (c : Cocone G)
      (c' : Cocone G') (u : c.pt ⟶ c'.pt) (_ : ∀ b, τ.app b ≫ c'.ι.app b = c.ι.app b ≫ u),
      colimMap φ ≫ colimMap α' ≫ colimit.desc G' c' = (colimMap α ≫ colimit.desc G c) ≫ u := by
    intro F F' G G' φ α α' τ h c c' u hc
    apply colimit.hom_ext
    intro b
    have hb := congrArg (fun σ => σ.app b) h
    simp only [NatTrans.comp_app] at hb
    simp [reassoc_of% hb, hc]
  exact key _ _ _ (pullbackRepresentablesFibreMap f q)
    ((projectiveReplacementπ A _).naturality _) (pullbackRepresentablesCocone (f ≫ q))
    (pullbackRepresentablesCocone q) f (fun b => fibreMap_snd f q b.hom)

theorem IsAccessibleALocalizer.mem_of_forall_fibreMap_mem {A : Type v} [SmallCategory A]
    {V : MorphismProperty (Aᵒᵖ ⥤ Type v)} [hV : IsAccessibleALocalizer V]
    [IsRegularALocalizer V] {X Y S : Aᵒᵖ ⥤ Type v} (f : X ⟶ Y) (q : Y ⟶ S)
    (hf : ∀ (a : A) (b : yoneda.obj a ⟶ S), V (fibreMap f q b)) : V f := by
  let τ := pullbackRepresentablesFibreMap f q
  let π := projectiveReplacementπ A (CostructuredArrow yoneda S)
  have hQ : ∀ b, V (((projectiveReplacement A _).map τ).app b) := fun b => by
    refine V.of_postcomp _ ((π.app _).app b) (hV.projectiveReplacementπ_app_mem _ b) ?_
    rw [← NatTrans.comp_app, π.naturality τ, NatTrans.comp_app]
    exact V.comp_mem _ _ (hV.projectiveReplacementπ_app_mem _ b) (hf b.left b.hom)
  have hc := hV.colimMap_mem (projectiveCofibrations_initial_to_projectiveReplacement _)
    (projectiveCofibrations_initial_to_projectiveReplacement _) _ hQ
  have h := V.comp_mem _ _ hc (pullbackResolutionMap_mem V q)
  rw [colimMap_projectiveReplacement_map_comp_pullbackResolutionMap] at h
  exact V.of_precomp _ _ (pullbackResolutionMap_mem V (f ≫ q)) h

theorem IsAccessibleALocalizer.mem_of_forall_pullback_fst_mem {A : Type v} [SmallCategory A]
    {V : MorphismProperty (Aᵒᵖ ⥤ Type v)} [hV : IsAccessibleALocalizer V]
    [IsRegularALocalizer V] {E B : Aᵒᵖ ⥤ Type v} (p : E ⟶ B)
    (hp : ∀ (a : A) (b : yoneda.obj a ⟶ B), V (pullback.fst b p)) : V p := by
  refine hV.mem_of_forall_fibreMap_mem p (𝟙 B) fun a b => ?_
  refine V.of_postcomp _ (pullback.fst b (𝟙 B))
    (hV.isALocalizer.isomorphisms_le _ (isomorphisms.infer_property _)) ?_
  rw [fibreMap_fst]
  have h : ∀ p' : E ⟶ B, p' = p → V (pullback.fst b p') := by
    rintro _ rfl
    exact hp a b
  exact h _ (Category.comp_id p)

end Atoms.Homotopical
