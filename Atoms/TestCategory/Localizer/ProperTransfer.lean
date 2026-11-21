import Atoms.TestCategory.Localizer.FibrantProductWeakness

open CategoryTheory Limits Opposite
open Atoms.Homotopical Simplicial MorphismProperty

namespace Atoms.TestCategory

universe u

namespace BasicLocalizer

theorem isTest_of_le {𝒲₀ 𝒲 : BasicLocalizer.{u}} (h : 𝒲₀.W ≤ 𝒲.W) (A : Type u)
    [SmallCategory A] [𝒲₀.IsTest A] : 𝒲.IsTest A :=
  𝒲.isTest_of_rlp_le A (h _ 𝒲₀.aspherical_of_isWeakTest)
    fun _ _ f hf ↦ h _ (𝒲₀.rlp_monomorphisms_le_wPsh_of_isLocalTest A f hf)

variable (𝒲 : BasicLocalizer.{u})

private theorem W_of_aspherical_of_isEmpty (E : Cat.{u, u}) [IsEmpty E]
    (hE : 𝒲.Aspherical E) {C D : Cat.{u, u}} (F : C ⟶ D) : 𝒲.W F := by
  let G : Cat.of (C × E) ⟶ Cat.of (D × E) := (F.toFunctor.prod (𝟭 E)).toCatHom
  have : G.toFunctor.IsEquivalence :=
    { faithful := ⟨fun {X} ↦ isEmptyElim X.2⟩
      full := ⟨fun {X} ↦ isEmptyElim X.2⟩
      essSurj := ⟨fun Y ↦ isEmptyElim Y.2⟩ }
  exact 𝒲.W.of_precomp _ F (𝒲.W_fst C hE)
    (𝒲.W.comp_mem G _ (𝒲.W_of_isEquivalence G) (𝒲.W_fst D hE))

theorem wSSet_of_wPsh_rightAdjoint_map (A : Type u) [SmallCategory A] [𝒲.IsTest A]
    {K L : SSet.{u}} (f : K ⟶ L) (hf : 𝒲.wPsh A ((ordinaryNerveElementsRightAdjoint A).map f)) :
    𝒲.wSSet f := by
  rcases isEmpty_or_nonempty A with hA | ⟨⟨a₀⟩⟩
  · have : IsEmpty (Cat.of A) := hA
    exact 𝒲.W_of_aspherical_of_isEmpty (Cat.of A) 𝒲.aspherical_of_isWeakTest _
  let kJ := bisimplicialShape A
  let P := simplicialRestriction (CategoryTheory.Prod.fst A (AsSmall.{u} SimplexCategory) ⋙
    Over.mapFunctor A ⋙ CategoryTheory.nerveFunctor)
  let J := simplicialRestriction kJ
  let Q := simplicialRestriction (CategoryTheory.Prod.snd A (AsSmall.{u} SimplexCategory) ⋙
    AsSmall.down ⋙ SSet.stdSimplex)
  let θP := simplicialRestrictionMap (bisimplicialShapeFst A)
  let θQ := simplicialRestrictionMap (bisimplicialShapeSnd A)
  let V := 𝒲.wPsh (A × (AsSmall.{u} SimplexCategory))
  have hP : V (P.map f) := 𝒲.wPsh_prod_of_forall_sectL _ fun _ ↦ hf
  have hJ : V (J.map f) := by
    apply V.of_precomp _ _ (𝒲.wPsh_bisimplicialShapeFst A K)
    rw [← θP.naturality f]
    exact V.comp_mem _ _ hP (𝒲.wPsh_bisimplicialShapeFst A L)
  have hQ : V (Q.map f) := by
    apply V.of_postcomp _ _ (𝒲.wPsh_bisimplicialShapeSnd A L)
    rw [θQ.naturality f]
    exact V.comp_mem _ _ (𝒲.wPsh_bisimplicialShapeSnd A K) hJ
  rw [← 𝒲.wPsh_simplicialRestriction_stdSimplex_map_iff]
  refine 𝒲.wPsh_of_wPsh_whiskerLeft_fst a₀ _ ?_
  rw [𝒲.wPsh_eq_inverseImage_presheafEquivalence
    (CategoryTheory.Prod.braiding (AsSmall.{u} SimplexCategory) A)]
  exact hQ

theorem wSSet_eq_inverseImage_rightAdjoint (A : Type u) [SmallCategory A] [𝒲.IsTest A] :
    𝒲.wSSet = (𝒲.wPsh A).inverseImage (ordinaryNerveElementsRightAdjoint A) := by
  ext K L f
  exact ⟨𝒲.ordinaryNerveElementsRightAdjoint_map_mem A f, 𝒲.wSSet_of_wPsh_rightAdjoint_map A f⟩

theorem rlp_rightAdjoint_map (A : Type u) [SmallCategory A] {K L : SSet.{u}} (p : K ⟶ L)
    (hp : (MorphismProperty.monomorphisms _ ⊓ 𝒲.wSSet).rlp p) :
    (MorphismProperty.monomorphisms _ ⊓ 𝒲.wPsh A).rlp
      ((ordinaryNerveElementsRightAdjoint A).map p) := by
  intro U V i ⟨hm, hw⟩
  have : Mono i := hm
  exact ((ordinaryNerveElementsAdjunction A).hasLiftingProperty_iff i _).1
    (hp _ ⟨mono_nerveMap_of_faithful _ (injective_elementsFunctor_map_obj A i),
      (𝒲.W_iff_wSSet_nerveMap ((elementsFunctor A).map i)).1 hw⟩)

theorem isRightProper_wSSet_of_isRightProper_wPsh (A : Type u) [SmallCategory A] [𝒲.IsTest A]
    [IsRightProper (𝒲.wPsh A)] :
    IsRightProper 𝒲.wSSet := by
  rw [𝒲.wSSet_eq_inverseImage_rightAdjoint A]
  refine isRightProper_inverseImage_of_rlp_map _ _ fun q hq ↦ ?_
  rw [← 𝒲.wSSet_eq_inverseImage_rightAdjoint A] at hq
  exact 𝒲.rlp_rightAdjoint_map A q hq

end BasicLocalizer

instance mono_ordinaryNerveElementsAdjunction_unit_app (A : Type u) [SmallCategory A]
    (X : Aᵒᵖ ⥤ Type u) : Mono ((ordinaryNerveElementsAdjunction A).unit.app X) :=
  have : (ordinaryNerveElements A).Faithful :=
    ⟨fun {X Y} α β h ↦ by
      ext a x
      have h := congrArg (fun F : (elementsFunctor A).obj X ⟶ (elementsFunctor A).obj Y ↦
        (F.toFunctor.obj (op ⟨a, x⟩)).unop) (CategoryTheory.nerveFunctor.map_injective h)
      exact eq_of_heq (Sigma.mk.inj_iff.1 h).2⟩
  inferInstance

namespace BasicLocalizer

variable (𝒲 : BasicLocalizer.{u})

theorem minimal_wPsh_le_baseChangeClass (A : Type u) [SmallCategory A]
    [IsRightProper (minimalBasicLocalizer.{u}.wPsh A)] {E B : Aᵒᵖ ⥤ Type u} (p : E ⟶ B)
    (hp : (MorphismProperty.monomorphisms _ ⊓ 𝒲.wPsh A).rlp p) :
    minimalBasicLocalizer.{u}.wPsh A ≤ baseChangeClass (𝒲.wPsh A) p := by
  have hle : minimalBasicLocalizer.{u}.wPsh A ≤ 𝒲.wPsh A :=
    fun _ _ f hf ↦ (minimalBasicLocalizer_W_iff _).1 hf 𝒲
  intro K L f hf b
  exact hle _ (IsRightProper.weakFibration_of_rlp p
    (antitone_rlp (inf_le_inf_left _ hle) _ hp) f b hf)

theorem baseChangeClass_unit (A : Type u) [SmallCategory A]
    [minimalBasicLocalizer.{u}.IsTest A] [IsRightProper (minimalBasicLocalizer.{u}.wPsh A)]
    (X : Aᵒᵖ ⥤ Type u) {E : Aᵒᵖ ⥤ Type u}
    (p : E ⟶ (ordinaryNerveElementsRightAdjoint A).obj ((ordinaryNerveElements A).obj X))
    (hp : (MorphismProperty.monomorphisms _ ⊓ 𝒲.wPsh A).rlp p) :
    baseChangeClass (𝒲.wPsh A) p ((ordinaryNerveElementsAdjunction A).unit.app X) :=
  𝒲.minimal_wPsh_le_baseChangeClass A p hp _
    (minimalBasicLocalizer.ordinaryNerveElements_unit_mem A X)

theorem weakFibration_rightAdjoint_map (A : Type u) [SmallCategory A]
    [minimalBasicLocalizer.{u}.IsTest A] [IsRightProper (minimalBasicLocalizer.{u}.wPsh A)]
    [IsRightProper 𝒲.wSSet] {K L : SSet.{u}} (p : K ⟶ L)
    (hp : (MorphismProperty.monomorphisms _ ⊓ 𝒲.wSSet).rlp p) :
    WeakFibration (𝒲.wPsh A) ((ordinaryNerveElementsRightAdjoint A).map p) := by
  have : 𝒲.IsTest A := isTest_of_le (fun _ _ F hF ↦ (minimalBasicLocalizer_W_iff F).1 hF 𝒲) A
  let R := ordinaryNerveElementsRightAdjoint A
  let N := ordinaryNerveElements A
  let η := (ordinaryNerveElementsAdjunction A).unit
  let V := 𝒲.wPsh A
  have hRp := 𝒲.rlp_rightAdjoint_map A p hp
  have hη : ∀ (X : Aᵒᵖ ⥤ Type u) (c : R.obj (N.obj X) ⟶ R.obj L),
      V (baseChangeMap (η.app X) c (R.map p)) := fun X c ↦
    𝒲.minimal_wPsh_le_baseChangeClass A _ hRp _
      (minimalBasicLocalizer.ordinaryNerveElements_unit_mem A X) c
  have hR : ∀ {X Y : Aᵒᵖ ⥤ Type u} (g : X ⟶ Y), V g → ∀ c : N.obj Y ⟶ L,
      V (baseChangeMap (R.map (N.map g)) (R.map c) (R.map p)) := by
    intro X Y g hg c
    have hw : 𝒲.wSSet (baseChangeMap (N.map g) c p) :=
      IsRightProper.weakFibration_of_rlp p hp (N.map g) c ((𝒲.W_iff_wSSet_nerveMap _).1 hg)
    exact (mem_iff_of_isPullback V
      (isPullback_baseChangeMap (R.map (N.map g)) (R.map c) (R.map p))
      ((isPullback_baseChangeMap (N.map g) c p).map R) (PreservesPullback.iso R c p)
      (PreservesPullback.iso_hom_fst R c p)).1 (𝒲.ordinaryNerveElementsRightAdjoint_map_mem A _ hw)
  intro X Y g b hg
  obtain ⟨c, rfl⟩ : ∃ c : N.obj Y ⟶ L, η.app Y ≫ R.map c = b :=
    ⟨((ordinaryNerveElementsAdjunction A).homEquiv _ _).symm b,
      ((ordinaryNerveElementsAdjunction A).homEquiv_unit _ _ _).symm.trans
        (Equiv.apply_symm_apply _ _)⟩
  have hnat : g ≫ η.app Y = η.app X ≫ R.map (N.map g) := η.naturality g
  have h₁ := baseChangeMap_comp_mem_iff V (R.map p) g (η.app Y) (R.map c)
  have h₂ := baseChangeMap_comp_mem_iff V (R.map p) (η.app X) (R.map (N.map g)) (R.map c)
  rw [hnat, h₂] at h₁
  exact V.of_postcomp _ _ (hη Y (R.map c)) (h₁.1 (V.comp_mem _ _ (hη X _) (hR g hg c)))

theorem isRightProper_wPsh_of_isRightProper_wSSet (hW : 𝒲.IsAccessible) (A : Type u)
    [SmallCategory A] [minimalBasicLocalizer.{u}.IsTest A]
    [IsRightProper (minimalBasicLocalizer.{u}.wPsh A)] [IsRightProper 𝒲.wSSet] :
    IsRightProper (𝒲.wPsh A) := by
  have : 𝒲.IsTest A := isTest_of_le (fun _ _ F hF ↦ (minimalBasicLocalizer_W_iff F).1 hF 𝒲) A
  have := 𝒲.isAccessibleALocalizer_wPsh_of_isTest (C := AsSmall.{u} SimplexCategory) hW
  let R := ordinaryNerveElementsRightAdjoint A
  let N := ordinaryNerveElements A
  let η := (ordinaryNerveElementsAdjunction A).unit
  let V := 𝒲.wPsh A
  refine ⟨fun {X Y} f hf ↦ ?_⟩
  obtain ⟨K, i, p, ⟨hi, hiw⟩, hp, hip⟩ := 𝒲.exists_factorization_sSet (N.map f)
  have : Mono i := hi
  have hRp := 𝒲.rlp_rightAdjoint_map A p hp
  have hsq : IsPullback (pullback.snd (η.app Y) (R.map p)) (pullback.fst (η.app Y) (R.map p))
      (R.map p) (η.app Y) := (IsPullback.of_hasPullback _ _).flip
  let j : X ⟶ pullback (η.app Y) (R.map p) := pullback.lift f (η.app X ≫ R.map i) (by
    rw [Category.assoc, ← R.map_comp, hip]
    exact η.naturality f)
  have hθ : V (pullback.snd (η.app Y) (R.map p)) := by
    have : IsIso (pullback.snd (𝟙 (R.obj (N.obj Y))) (R.map p)) :=
      (IsPullback.of_hasPullback _ _).isIso_snd_of_isIso
    refine (mem_iff_of_isPullback V (isPullback_baseChangeMap (η.app Y) (𝟙 _) (R.map p)) hsq
      (asIso (pullback.snd (𝟙 _) (R.map p))).symm ?_).2
      (𝒲.baseChangeClass_unit A Y (R.map p) hRp (𝟙 _))
    rw [Iso.symm_hom, asIso_inv, IsIso.inv_comp_eq, ← pullback.condition, Category.comp_id]
    rfl
  have hjq : j ≫ pullback.fst _ _ = f := pullback.lift_fst _ _ _
  have hjθ : j ≫ pullback.snd _ _ = η.app X ≫ R.map i := pullback.lift_snd _ _ _
  have hj : (MorphismProperty.monomorphisms _ ⊓ V) j := by
    have : Mono (η.app X) := mono_ordinaryNerveElementsAdjunction_unit_app A X
    refine ⟨mono_of_mono_fac hjθ, V.of_postcomp _ _ hθ ?_⟩
    rw [hjθ]
    exact V.comp_mem _ _ (𝒲.ordinaryNerveElements_unit_mem A X)
      (𝒲.ordinaryNerveElementsRightAdjoint_map_mem A i hiw)
  have := hf j hj
  have sq : CommSq (𝟙 X) j f (pullback.fst (η.app Y) (R.map p)) := ⟨by simp [hjq]⟩
  let Rt : RetractArrow f (pullback.fst (η.app Y) (R.map p)) :=
    { i := Arrow.homMk j (𝟙 Y) (by simp [hjq])
      r := Arrow.homMk sq.lift (𝟙 Y) (by simp)
      retract := by ext <;> simp }
  rw [weakFibration_iff_le_baseChangeClass]
  exact ((weakFibration_iff_le_baseChangeClass V _).1
    (𝒲.weakFibration_rightAdjoint_map A p hp)).trans
    ((baseChangeClass_le_of_isPullback hsq).trans (baseChangeClass_le_of_retract Rt))

theorem isRightProper_wPsh_iff (hW : 𝒲.IsAccessible) (A B : Type u) [SmallCategory A]
    [SmallCategory B] [minimalBasicLocalizer.{u}.IsTest A] [minimalBasicLocalizer.{u}.IsTest B]
    [IsRightProper (minimalBasicLocalizer.{u}.wPsh A)]
    [IsRightProper (minimalBasicLocalizer.{u}.wPsh B)] :
    IsRightProper (𝒲.wPsh A) ↔ IsRightProper (𝒲.wPsh B) := by
  have : 𝒲.IsTest A := isTest_of_le (fun _ _ F hF ↦ (minimalBasicLocalizer_W_iff F).1 hF 𝒲) A
  have : 𝒲.IsTest B := isTest_of_le (fun _ _ F hF ↦ (minimalBasicLocalizer_W_iff F).1 hF 𝒲) B
  refine ⟨fun _ ↦ ?_, fun _ ↦ ?_⟩
  · have := 𝒲.isRightProper_wSSet_of_isRightProper_wPsh A
    exact 𝒲.isRightProper_wPsh_of_isRightProper_wSSet hW B
  · have := 𝒲.isRightProper_wSSet_of_isRightProper_wPsh B
    exact 𝒲.isRightProper_wPsh_of_isRightProper_wSSet hW A

theorem terminal_from_mem_fibrantBaseChangeClass (hW : 𝒲.IsAccessible) (A : Type u)
    [SmallCategory A] [𝒲.IsTest A] (M : Aᵒᵖ ⥤ Type u) (hM : 𝒲.wPsh A (terminal.from M)) :
    fibrantBaseChangeClass (𝒲.wPsh A) (terminal.from M) := by
  intro E B q hq _ b
  have hF : (MorphismProperty.monomorphisms _ ⊓ 𝒲.wPsh A).rlp (terminal.from (pullback b q)) := by
    have h := (MorphismProperty.monomorphisms _ ⊓ 𝒲.wPsh A).rlp.of_isPullback
      (IsPullback.of_hasPullback b q).flip hq
    rwa [show pullback.fst b q = terminal.from _ from terminal.hom_ext _ _] at h
  have hfac : (Limits.prod.fst : pullback b q ⨯ M ⟶ pullback b q) =
      Limits.prod.map (𝟙 _) (terminal.from M) ≫ Limits.prod.fst := by
    simp
  have hfst : 𝒲.wPsh A (Limits.prod.fst : pullback b q ⨯ M ⟶ pullback b q) := by
    rw [hfac]
    exact (𝒲.wPsh A).comp_mem _ _ (𝒲.prod_map_mem_of_fibrant_isTest A hW _ hF _ hM)
      (isomorphisms_le_of_containsIdentities (𝒲.wPsh _) _ (Limits.prod.rightUnitor _).isIso_hom)
  exact (MorphismProperty.mem_iff_of_isPullback _ (IsPullback.of_hasBinaryProduct' (pullback b q) M)
    (isPullback_baseChangeMap (terminal.from M) b q) (Iso.refl _) (terminal.hom_ext _ _)).2 hfst

end BasicLocalizer

open BasicLocalizer in
theorem BasicLocalizer.isRightProper_wPsh_generated_aspherical {ι : Type u} (F : ι → Cat.{u, u})
    (hW : (generated (MorphismProperty.ofHoms fun i ↦ terminal.from (F i))).IsAccessible)
    (A : Type u) [SmallCategory A] [Homotopical.EZCategory A]
    [Homotopical.HasTrivialAutomorphisms A] [minimalBasicLocalizer.{u}.IsTest A] :
    IsRightProper ((generated (MorphismProperty.ofHoms fun i ↦ terminal.from (F i))).wPsh A) := by
  let T : MorphismProperty Cat.{u, u} := MorphismProperty.ofHoms fun i ↦ terminal.from (F i)
  let 𝒲 := generated T
  have : 𝒲.IsTest A := isTest_of_le (fun _ _ G hG ↦ (minimalBasicLocalizer_W_iff G).1 hG 𝒲) A
  have hV := 𝒲.isAccessibleALocalizer_wPsh_of_isTest hW (C := A)
  have hS : generatedALocalizer.{u, u} (T.map (nerveFunctor A) ⊔
      MorphismProperty.ofHoms fun a : A ↦ terminal.from (yoneda.obj a)) = 𝒲.wPsh A := by
    rw [𝒲.wPsh_eq_regularCompletion A T rfl, IsALocalizer.regularCompletion_eq_of_rigid]
  rw [isRightProper_iff_of_generatedALocalizer _ hS]
  have := hV.isALocalizer_fibrantBaseChangeClass
  refine sup_le ?_ fun _ _ _ ⟨a⟩ ↦ 𝒲.terminal_from_mem_fibrantBaseChangeClass hW A _
    (IsTestALocalizer.terminal_from_yoneda a)
  rw [map_le_iff]
  rintro _ _ _ ⟨i⟩
  rw [MorphismProperty.inverseImage_iff]
  have : PreservesLimitsOfSize.{0, 0} (nerveFunctor A) :=
    (nerveAdjunction A).rightAdjoint_preservesLimits
  have ht : IsIso (terminal.from ((nerveFunctor A).obj (⊤_ Cat.{u, u}))) := by
    rw [terminal.hom_ext (terminal.from _) (PreservesTerminal.iso (nerveFunctor A)).hom]
    infer_instance
  have hN : 𝒲.wPsh A ((nerveFunctor A).map (terminal.from (F i))) :=
    (mem_iff_map_map_of_counit (nerveAdjunction A) 𝒲.W (fun C ↦ IsWeakTest.counit_mem C) _).1
      (le_generated_W T _ ⟨i⟩)
  rw [← (fibrantBaseChangeClass (𝒲.wPsh A)).cancel_right_of_respectsIso _
    (terminal.from ((nerveFunctor A).obj (⊤_ Cat.{u, u}))), terminal.comp_from]
  refine 𝒲.terminal_from_mem_fibrantBaseChangeClass hW A _ ?_
  rw [← terminal.comp_from ((nerveFunctor A).map (terminal.from (F i)))]
  exact (𝒲.wPsh A).comp_mem _ _ hN
    (isomorphisms_le_of_containsIdentities (𝒲.wPsh _) _ (isomorphisms.infer_property _))

end Atoms.TestCategory
