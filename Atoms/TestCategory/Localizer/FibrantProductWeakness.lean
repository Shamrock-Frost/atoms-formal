import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.Nerve
import Atoms.Homotopical.Localizer.RightProperSlice
import Atoms.Homotopical.Regular.Rigid
import Atoms.TestCategory.Localizer.ModelStructure
import Atoms.TestCategory.Simplicial.NerveResolution

open CategoryTheory Limits Opposite
open Atoms.Homotopical Simplicial MorphismProperty

namespace Atoms.TestCategory

universe u

namespace BasicLocalizer

theorem rlp_terminal_rightAdjoint (𝒲 : BasicLocalizer.{u}) (A : Type u) [SmallCategory A]
    (K : SSet.{u})
    (hK : (MorphismProperty.monomorphisms _ ⊓ 𝒲.wSSet).rlp (terminal.from K)) :
    (MorphismProperty.monomorphisms _ ⊓ 𝒲.wPsh A).rlp
      (terminal.from ((ordinaryNerveElementsRightAdjoint A).obj K)) := by
  intro U V i ⟨hm, hw⟩
  have : Mono i := hm
  have : HasLiftingProperty i ((ordinaryNerveElementsRightAdjoint A).map (terminal.from K)) :=
    ((ordinaryNerveElementsAdjunction A).hasLiftingProperty_iff i _).1
      (hK _ ⟨mono_nerveMap_of_faithful _ (injective_elementsFunctor_map_obj A i),
        (𝒲.W_iff_wSSet_nerveMap ((elementsFunctor A).map i)).1 hw⟩)
  have : IsIso (terminal.from ((ordinaryNerveElementsRightAdjoint A).obj (⊤_ SSet.{u}))) := by
    rw [terminal.hom_ext (terminal.from _) (PreservesTerminal.iso _).hom]
    infer_instance
  rw [terminal.hom_ext (terminal.from _)
    ((ordinaryNerveElementsRightAdjoint A).map (terminal.from K) ≫ terminal.from _)]
  infer_instance

theorem exists_factorization_sSet (𝒲 : BasicLocalizer.{u})
    [hW : IsAccessibleALocalizer (𝒲.wPsh (AsSmall.{u} SimplexCategory))] {X Y : SSet.{u}}
    (g : X ⟶ Y) :
    ∃ (Z : SSet.{u}) (i : X ⟶ Z) (π : Z ⟶ Y),
      (MorphismProperty.monomorphisms _ ⊓ 𝒲.wSSet) i ∧
        (MorphismProperty.monomorphisms _ ⊓ 𝒲.wSSet).rlp π ∧ i ≫ π = g := by
  let E := SSet.asSmallEquivalence.{u}
  obtain ⟨Z', i', π', ⟨hm', hw'⟩, hπ', hfac⟩ := hW.exists_factorization (E.functor.map g)
  have : Mono i' := hm'
  refine ⟨E.inverse.obj Z', (E.unitIso.app X).hom ≫ E.inverse.map i',
    E.inverse.map π' ≫ (E.unitIso.app Y).inv, ⟨?_, ?_⟩, ?_, ?_⟩
  · exact monomorphisms.infer_property _
  · change 𝒲.wPsh _ (E.functor.map _)
    rw [E.functor.map_comp]
    exact (𝒲.wPsh _).comp_mem _ _
      (isomorphisms_le_of_containsIdentities (𝒲.wPsh _) _ (isomorphisms.infer_property _))
      ((map_functor_map_inverse_iff E (𝒲.wPsh _) i').2 hw')
  · intro U V j ⟨hm, hw⟩
    have : Mono j := hm
    have : HasLiftingProperty j (E.inverse.map π') :=
      (E.toAdjunction.hasLiftingProperty_iff j π').1 (hπ' _ ⟨monomorphisms.infer_property _, hw⟩)
    infer_instance
  · rw [Category.assoc, ← Category.assoc (E.inverse.map i'), ← E.inverse.map_comp, hfac]
    simp

theorem exists_fibrant_rightAdjoint_comparison
    (𝒲 : BasicLocalizer.{u}) (A : Type u) [SmallCategory A]
    [𝒲.IsTest A]
    [IsAccessibleALocalizer (𝒲.wPsh (AsSmall.{u} SimplexCategory))] (X : Aᵒᵖ ⥤ Type u) :
    ∃ (K : SSet.{u}) (j : X ⟶ (ordinaryNerveElementsRightAdjoint A).obj K),
      𝒲.wPsh A j ∧ (MorphismProperty.monomorphisms _ ⊓ 𝒲.wSSet).rlp (terminal.from K) := by
  obtain ⟨K, i, π, ⟨-, hi⟩, hπ, -⟩ :=
    𝒲.exists_factorization_sSet (terminal.from ((ordinaryNerveElements A).obj X))
  refine ⟨K, (ordinaryNerveElementsAdjunction A).unit.app X ≫
    (ordinaryNerveElementsRightAdjoint A).map i, ?_, ?_⟩
  · exact (𝒲.wPsh A).comp_mem _ _ (𝒲.ordinaryNerveElements_unit_mem A X)
      (𝒲.ordinaryNerveElementsRightAdjoint_map_mem A i hi)
  · rw [terminal.hom_ext (terminal.from K) π]
    exact hπ

end BasicLocalizer

namespace BasicLocalizer

theorem prod_fibrant_comparison_mem (𝒲 : BasicLocalizer.{u}) (A : Type u) [SmallCategory A]
    [𝒲.IsLocalTest A] [hW : IsAccessibleALocalizer (𝒲.wPsh A)]
    {X Y : Aᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hX : (MorphismProperty.monomorphisms _ ⊓ 𝒲.wPsh A).rlp (terminal.from X))
    (hY : (MorphismProperty.monomorphisms _ ⊓ 𝒲.wPsh A).rlp (terminal.from Y))
    (hf : 𝒲.wPsh A f) (Z : Aᵒᵖ ⥤ Type u) :
    𝒲.wPsh A (Limits.prod.map (𝟙 Z) f) := by
  let J := rightAdjointSeparatingInterval A
  have hc : ∀ T : Aᵒᵖ ⥤ Type u, 𝒲.wPsh A (J.cylinder.contraction.app T) :=
    fun T => 𝒲.wPsh_snd_of_locallyAspherical A (𝒲.locallyAspherical_rightAdjoint_interval A) T
  obtain ⟨S, hsmall, hS, hSV⟩ := hW.exists_weakEquivalences_eq J.cylinder hc
  have : S.IsSmall.{u} := hsmall
  rw [← hSV] at hX hY hf ⊢
  replace hX := (J.cylinder.rlp_trivialCofibrations_terminal_from_iff S hS X).1 hX
  replace hY := (J.cylinder.rlp_trivialCofibrations_terminal_from_iff S hS Y).1 hY
  obtain ⟨g, hfg, hgf⟩ :=
    J.cylinder.exists_homotopy_inverse_of_weakEquivalences S hX hY f hf
  have hfg' := J.cylinder_homotopic_prod_map Z hfg
  have hgf' := J.cylinder_homotopic_prod_map Z hgf
  rw [Limits.prod.map_id_id] at hfg' hgf'
  refine J.cylinder.weakEquivalences_of_homotopic S _ (Limits.prod.map (𝟙 Z) g)
    ?_ ?_
  · rw [Limits.prod.map_map, Category.comp_id]
    exact hfg'
  · rw [Limits.prod.map_map, Category.comp_id]
    exact hgf'

theorem prod_map_mem_of_fibrant_isTest (𝒲 : BasicLocalizer.{u}) (A : Type u) [SmallCategory A]
    (hW : 𝒲.IsAccessible) [𝒲.IsTest A] (X : Aᵒᵖ ⥤ Type u)
    (hX : (MorphismProperty.monomorphisms _ ⊓ 𝒲.wPsh A).rlp (terminal.from X))
    {Y Z : Aᵒᵖ ⥤ Type u} (f : Y ⟶ Z) (hf : 𝒲.wPsh A f) :
    𝒲.wPsh A (Limits.prod.map (𝟙 X) f) := by
  have := 𝒲.isAccessibleALocalizer_wPsh A hW
  have := 𝒲.isAccessibleALocalizer_wPsh (AsSmall.{u} SimplexCategory) hW
  obtain ⟨K, j, hj, hK⟩ := 𝒲.exists_fibrant_rightAdjoint_comparison A X
  have hRK := 𝒲.rlp_terminal_rightAdjoint A K hK
  have hjY := 𝒲.prod_fibrant_comparison_mem A j hX hRK hj Y
  have hjZ := 𝒲.prod_fibrant_comparison_mem A j hX hRK hj Z
  have hfK := 𝒲.prod_map_rightAdjoint_mem A f hf K
  have sq : Limits.prod.map f (𝟙 X) ≫ Limits.prod.map (𝟙 Z) j =
      Limits.prod.map (𝟙 Y) j ≫ Limits.prod.map f (𝟙 _) := by
    simp
  have hfX : 𝒲.wPsh A (Limits.prod.map f (𝟙 X)) := by
    refine (𝒲.wPsh A).of_postcomp _ _ hjZ ?_
    rw [sq]
    exact (𝒲.wPsh A).comp_mem _ _ hjY hfK
  have hb : Limits.prod.map (𝟙 X) f ≫ (prod.braiding X Z).hom =
      (prod.braiding X Y).hom ≫ Limits.prod.map f (𝟙 X) :=
    braid_natural _ _
  refine (𝒲.wPsh A).of_postcomp _ (prod.braiding X Z).hom
    (isomorphisms_le_of_containsIdentities (𝒲.wPsh _) _ (isomorphisms.infer_property _)) ?_
  rw [hb]
  exact (𝒲.wPsh A).comp_mem _ _
    (isomorphisms_le_of_containsIdentities (𝒲.wPsh _) _ (isomorphisms.infer_property _)) hfX

end BasicLocalizer

theorem prod_map_mem_of_fibrant_isTestALocalizer {A : Type u} [SmallCategory A]
    (V : MorphismProperty (Aᵒᵖ ⥤ Type u)) [IsAccessibleALocalizer V] [IsTestALocalizer V]
    (X : Aᵒᵖ ⥤ Type u) (hX : (MorphismProperty.monomorphisms _ ⊓ V).rlp (terminal.from X))
    {Y Z : Aᵒᵖ ⥤ Type u} (f : Y ⟶ Z) (hf : V f) :
    V (Limits.prod.map (𝟙 X) f) := by
  have := isTest_ofTestALocalizer V
  rw [← BasicLocalizer.ofTestALocalizer_wPsh V] at hX hf ⊢
  exact (BasicLocalizer.ofTestALocalizer V).prod_map_mem_of_fibrant_isTest A
    (BasicLocalizer.isAccessible_ofTestALocalizer V) X hX f hf

instance BasicLocalizer.isRightProper_wPsh_costructuredArrow (𝒲 : BasicLocalizer.{u})
    {A : Type u} [SmallCategory A] [𝒲.IsLocalTest A] [IsRightProper (𝒲.wPsh A)]
    (X : Aᵒᵖ ⥤ Type u) :
    IsRightProper (𝒲.wPsh (CostructuredArrow yoneda X)) := by
  rw [𝒲.wPsh_costructuredArrow_eq]
  infer_instance

section Minimal

variable {A : Type u} [SmallCategory A]

variable (A) in
theorem minimal_wPsh_eq_generatedALocalizer [Homotopical.EZCategory A]
    [Homotopical.HasTrivialAutomorphisms A] [minimalBasicLocalizer.{u}.IsTest A] :
    minimalBasicLocalizer.{u}.wPsh A = generatedALocalizer.{u, u}
      (MorphismProperty.ofHoms fun a : A ↦ terminal.from (yoneda.obj a)) := by
  refine le_antisymm ?_ (generatedALocalizer_le ?_)
  · have : IsTestALocalizer (generatedALocalizer.{u, u}
        (MorphismProperty.ofHoms fun a : A ↦ terminal.from (yoneda.obj a))) :=
      ⟨fun a ↦ le_generatedALocalizer _ _ ⟨a⟩⟩
    rw [← BasicLocalizer.ofTestALocalizer_wPsh (generatedALocalizer.{u, u}
      (MorphismProperty.ofHoms fun a : A ↦ terminal.from (yoneda.obj a)))]
    intro X Y f hf
    exact BasicLocalizer.generated_W_le ⊥ _ bot_le _ hf
  · rintro _ _ _ ⟨a⟩
    exact IsTestALocalizer.terminal_from_yoneda a

theorem minimal_wPsh_prod_fst_yoneda [minimalBasicLocalizer.{u}.IsTest A] (X : Aᵒᵖ ⥤ Type u)
    (hX : (MorphismProperty.monomorphisms _ ⊓ minimalBasicLocalizer.{u}.wPsh A).rlp
      (terminal.from X)) (a : A) :
    minimalBasicLocalizer.{u}.wPsh A (Limits.prod.fst : X ⨯ yoneda.obj a ⟶ X) := by
  have hm := minimalBasicLocalizer.prod_map_mem_of_fibrant_isTest A
    isAccessible_minimalBasicLocalizer X hX (terminal.from (yoneda.obj a))
    (IsTestALocalizer.terminal_from_yoneda a)
  have hfac : (Limits.prod.fst : X ⨯ yoneda.obj a ⟶ X) =
      Limits.prod.map (𝟙 X) (terminal.from (yoneda.obj a)) ≫ Limits.prod.fst := by
    simp
  rw [hfac]
  exact (minimalBasicLocalizer.wPsh A).comp_mem _ _ hm
    (isomorphisms_le_of_containsIdentities (minimalBasicLocalizer.wPsh _) _
      (prod.rightUnitor X).isIso_hom)

instance isRightProper_minimal_wPsh [Homotopical.EZCategory A]
    [Homotopical.HasTrivialAutomorphisms A] [minimalBasicLocalizer.{u}.IsTest A] :
    IsRightProper (minimalBasicLocalizer.{u}.wPsh A) := by
  refine (isRightProper_iff_of_generatedALocalizer
    (MorphismProperty.ofHoms fun a : A ↦ terminal.from (yoneda.obj a))
    (minimal_wPsh_eq_generatedALocalizer A).symm).2 ?_
  rintro _ _ _ ⟨a⟩ E B q hq _ b
  have hF : (MorphismProperty.monomorphisms _ ⊓ minimalBasicLocalizer.{u}.wPsh A).rlp
      (terminal.from (pullback b q)) := by
    have h := (MorphismProperty.monomorphisms _ ⊓
      minimalBasicLocalizer.{u}.wPsh A).rlp.of_isPullback (IsPullback.of_hasPullback b q).flip hq
    rwa [show pullback.fst b q = terminal.from _ from terminal.hom_ext _ _] at h
  exact (MorphismProperty.mem_iff_of_isPullback _
    (IsPullback.of_hasBinaryProduct' (pullback b q) (yoneda.obj a))
    (isPullback_baseChangeMap (terminal.from (yoneda.obj a)) b q) (Iso.refl _)
    (terminal.hom_ext _ _)).2 (minimal_wPsh_prod_fst_yoneda _ hF a)

end Minimal

end Atoms.TestCategory
