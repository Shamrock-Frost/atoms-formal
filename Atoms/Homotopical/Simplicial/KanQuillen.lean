import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.FundamentalLemma
import Atoms.Homotopical.Simplicial.InfiniteExtensionKan
import Atoms.Homotopical.Localizer.RightProper
import Atoms.Homotopical.Simplicial.VertexGeneration

open CategoryTheory Limits MorphismProperty Simplicial

universe u

namespace Atoms.Homotopical

open MonoidalCategory

theorem rlp_trivialCofibrations_exInfty_map {X Y : SSet.{u}} {p : X ⟶ Y}
    (hp : SSet.modelCategoryQuillen.J.rlp p) :
    (MorphismProperty.monomorphisms SSet.{u} ⊓ kanWeak).rlp (exInfty.{u}.map p) := by
  exact simplicialCylinder.{u}.rlp_trivialCofibrations_of_rlp_anodyne ⊥ bot_le (exInfty.{u}.map p)
    ((rlp_anodyne_bot_iff _).2 (J_rlp_exInfty_map hp))
    ((isFibrant_bot_iff_kanComplex _).2 inferInstance)

theorem rlp_trivialCofibrations_of_J_rlp {X Y : SSet.{u}} {p : X ⟶ Y}
    (hp : SSet.modelCategoryQuillen.J.rlp p) :
    (MorphismProperty.monomorphisms SSet.{u} ⊓ kanWeak).rlp p := by
  have hq := (MorphismProperty.monomorphisms SSet.{u} ⊓ kanWeak).rlp.pullback_fst
    (exInftyUnit.{u}.app Y) (exInfty.{u}.map p) (rlp_trivialCofibrations_exInfty_map hp)
  have hfac : exInftyRelativeUnit p ≫ pullback.fst (exInftyUnit.app Y) (exInfty.map p) = p :=
    pullback.lift_fst _ _ _
  have : HasLiftingProperty (exInftyRelativeUnit p) p :=
    anodyneExtensions_exInftyRelativeUnit p p hp
  exact of_retract (RetractArrow.ofRightLiftingProperty hfac) hq

theorem rlp_trivialCofibrations_kanWeak :
    (MorphismProperty.monomorphisms SSet.{u} ⊓ kanWeak).rlp = SSet.modelCategoryQuillen.J.rlp := by
  refine le_antisymm (antitone_rlp ?_) (fun _ _ _ hp ↦ rlp_trivialCofibrations_of_J_rlp hp)
  exact (le_llp_rlp SSet.modelCategoryQuillen.J).trans
    (le_inf SSet.anodyneExtensions_le_monomorphisms anodyneExtensions_le_kanWeak)

theorem trivialCofibrations_kanWeak_eq :
    MorphismProperty.monomorphisms SSet.{u} ⊓ kanWeak = SSet.anodyneExtensions.{u} := by
  refine le_antisymm ?_
    (le_inf SSet.anodyneExtensions_le_monomorphisms anodyneExtensions_le_kanWeak)
  rw [SSet.anodyneExtensions_eq_llp_rlp, ← rlp_trivialCofibrations_kanWeak]
  exact le_llp_rlp _

theorem rlp_monomorphisms_of_J_rlp_of_kanWeak {X Y : SSet.{u}} {p : X ⟶ Y}
    (hp : SSet.modelCategoryQuillen.J.rlp p) (hw : kanWeak p) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp p := by
  rw [simplicialCylinder.{u}.rlp_monomorphisms_eq ⊥]
  exact ⟨rlp_trivialCofibrations_of_J_rlp hp, hw⟩

theorem anodyneExtensions_of_comp {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [Mono g]
    (hf : SSet.anodyneExtensions f) (hfg : SSet.anodyneExtensions (f ≫ g)) :
    SSet.anodyneExtensions g := by
  rw [← trivialCofibrations_kanWeak_eq] at hf hfg ⊢
  exact ⟨MorphismProperty.monomorphisms.infer_property g, kanWeak.of_precomp f g hf.2 hfg.2⟩

theorem anodyneExtensions_vertex_nerve (C : Type u) [SmallCategory C] [HasTerminal C]
    (x : Δ[0] ⟶ nerve C) : SSet.anodyneExtensions x := by
  have hx : kanWeak (x ≫ terminal.from (nerve C)) := by
    rw [terminal.hom_ext (x ≫ terminal.from (nerve C)) (terminal.from Δ[0])]
    exact terminal_from_stdSimplex_mem_kanWeak 0
  rw [← trivialCofibrations_kanWeak_eq]
  exact ⟨SSet.stdSimplex.isTerminalObj₀.mono_from x,
    kanWeak.of_postcomp x _ (terminal_from_nerve_mem_kanWeak C) hx⟩

private theorem isWeakFactorizationSystem_trivialCofibrations_kanWeak :
    IsWeakFactorizationSystem (MorphismProperty.monomorphisms SSet.{u} ⊓ kanWeak)
      SSet.modelCategoryQuillen.J.rlp := by
  rw [← rlp_trivialCofibrations_kanWeak]
  exact isAccessibleALocalizer_kanWeak.isWeakFactorizationSystem_trivialCofibrations

private theorem isWeakFactorizationSystem_monomorphisms_kanWeak :
    IsWeakFactorizationSystem (MorphismProperty.monomorphisms SSet.{u})
      (SSet.modelCategoryQuillen.J.rlp ⊓ kanWeak) := by
  rw [← rlp_trivialCofibrations_kanWeak]
  exact isAccessibleALocalizer_kanWeak.isWeakFactorizationSystem_monomorphisms

instance isRightProper_kanWeak : IsRightProper kanWeak.{u} := by
  refine isRightProper_of_generatedALocalizer_snd
    simplicialCylinder.{u}.cellularContractions
    kanWeak_eq_generatedALocalizer_cellularContractions.symm {Δ[1]} ?_ ?_
  · rintro _ _ f (h | h) <;> cases h with
    | mk i => exact ⟨Δ[1], rfl, Iso.refl (Δ[1] ⊗ _), (Category.id_comp _).symm⟩
  · rintro L rfl Z
    exact simplicialCylinder.{u}.contraction_mem_weakEquivalences ⊥ bot_le Z

theorem weakFibration_kanWeak_of_J_rlp {X Y : SSet.{u}} {p : X ⟶ Y}
    (hp : SSet.modelCategoryQuillen.J.rlp p) : WeakFibration kanWeak p :=
  IsRightProper.weakFibration_of_rlp p (rlp_trivialCofibrations_of_J_rlp hp)

theorem kanWeak_yoneda_map {a a' : SimplexCategory} (f : a ⟶ a') :
    kanWeak.{u} (uliftYoneda.{u}.map f) := by
  refine kanWeak.of_postcomp (uliftYoneda.map f) (terminal.from _)
    (terminal_from_stdSimplex_mem_kanWeak a'.len) ?_
  rw [terminal.hom_ext (uliftYoneda.map f ≫ terminal.from _) (terminal.from _)]
  exact terminal_from_stdSimplex_mem_kanWeak a.len

theorem locallyConstant_iff_kanWeak {V : MorphismProperty SSet.{u}} [hV : IsALocalizer V]
    {E B : SSet.{u}} (p : E ⟶ B) :
    LocallyConstant V p ↔
      ∀ {K L : SSet.{u}} (f : K ⟶ L) (b : L ⟶ B), kanWeak f → V (baseChangeMap f b p) := by
  refine ⟨fun hlc K L f b hf ↦ ?_, fun h a a' f b ↦ h _ b (kanWeak_yoneda_map f)⟩
  have := hV.isSaturated_monomorphisms_inf_baseChangeClass p
  have hle := anodyneExtensions_le_of_vertex
    (MorphismProperty.monomorphisms SSet.{u} ⊓ baseChangeClass V p)
    (fun _ _ _ f g _ hg hf hfg ↦ ⟨hg, (baseChangeClass_comp_iff p f g hf.2).1 hfg.2⟩)
    (fun m x ↦ ⟨SSet.stdSimplex.isTerminalObj₀.mono_from x, fun b ↦ by
      obtain ⟨g, rfl⟩ := SSet.stdSimplex.map_surjective x
      exact hlc _ _ g b⟩)
  have htc : MorphismProperty.monomorphisms SSet.{u} ⊓ kanWeak ≤ baseChangeClass V p := by
    rw [trivialCofibrations_kanWeak_eq]
    exact hle.trans inf_le_right
  exact hV.le_baseChangeClass p htc f hf b

end Atoms.Homotopical

namespace SSet.modelCategoryQuillen

open HomotopicalAlgebra Atoms.Homotopical

scoped instance kanQuillenWeakEquivalences : CategoryWithWeakEquivalences SSet.{u} where
  weakEquivalences := kanWeak

theorem weakEquivalences_eq : weakEquivalences SSet.{u} = kanWeak := rfl

scoped instance kanQuillenModelCategory : ModelCategory SSet.{u} :=
  have : (weakEquivalences SSet.{u}).HasTwoOutOfThreeProperty :=
    isALocalizer_kanWeak.hasTwoOutOfThreeProperty
  have : IsWeakFactorizationSystem (cofibrations SSet.{u}) (trivialFibrations SSet.{u}) :=
    isWeakFactorizationSystem_monomorphisms_kanWeak
  have : IsWeakFactorizationSystem (trivialCofibrations SSet.{u}) (fibrations SSet.{u}) :=
    isWeakFactorizationSystem_trivialCofibrations_kanWeak
  ModelCategory.mk' SSet.{u}

end SSet.modelCategoryQuillen

open SSet.modelCategoryQuillen HomotopicalAlgebra in
theorem Atoms.Homotopical.kanWeak_iff_isIso_map {H : Type*} [Category* H] (L : SSet.{u} ⥤ H)
    [hL : L.IsLocalization kanWeak] {X Y : SSet.{u}} (f : X ⟶ Y) :
    kanWeak f ↔ IsIso (L.map f) :=
  have : L.IsLocalization (weakEquivalences SSet.{u}) := hL
  (weakEquivalence_iff f).symm.trans (weakEquivalence_iff_isIso_map L f)
