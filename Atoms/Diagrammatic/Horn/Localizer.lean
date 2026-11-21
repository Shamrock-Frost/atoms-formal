import Atoms.Diagrammatic.Horn.ModelStructure
import Atoms.Diagrammatic.Horn.Weakness
import Atoms.Diagrammatic.Horn.SubmoleculeAnodyne
import Atoms.TestCategory.Localizer.FibrantProductWeakness

open CategoryTheory Limits Opposite Atoms.Molecule Atoms.Molecule.OGP Atoms.Shape HomotopicalAlgebra
  Atoms.Homotopical Atoms.TestCategory

universe u

namespace Atoms.Diagrammatic

instance isAccessibleALocalizer_hornWeak :
    IsAccessibleALocalizer hornWeak.{u} :=
  grayExactCylinder.{u}.isAccessibleALocalizer_weakEquivalences hornInclusions
    hornInclusions_le_monomorphisms

theorem terminal_from_ball_mem_hornWeak (U : Atom) :
    hornWeak.{u} (terminal.from (ball U)) :=
  terminal_from_ball_mem_of_inclusions (V := hornWeak.{u})
    (fun f hf ↦ (saturation_hornInclusions_le_trivialCofibrations.{u} _
      (yoneda_map_mem_saturation_hornInclusions.{u} f hf)).2) U

private theorem terminal_from_yoneda_mem_hornWeak (a : Atom) :
    hornWeak (terminal.from (yoneda.obj a)) := by
  rw [show terminal.from (yoneda.obj a) =
      (uliftYonedaIsoYoneda.{0}.app a).inv ≫ terminal.from (ball a) from terminal.hom_ext _ _]
  exact hornWeak.comp_mem _ _
    ((inferInstance : IsALocalizer hornWeak).isomorphisms_le _
      (MorphismProperty.isomorphisms.infer_property _))
    (terminal_from_ball_mem_hornWeak a)

instance isTestALocalizer_hornWeak :
    IsTestALocalizer hornWeak where
  terminal_from_yoneda := terminal_from_yoneda_mem_hornWeak

instance isAccessibleALocalizer_inverseImage_hornWeak :
    IsAccessibleALocalizer.{u, u} (hornWeak.{u}.inverseImage DiagSet.asSmallEquivalence.inverse) :=
  IsAccessibleALocalizer.inverseImage_asSmall

instance isTestALocalizer_inverseImage_hornWeak :
    IsTestALocalizer (hornWeak.{u}.inverseImage DiagSet.asSmallEquivalence.inverse) where
  terminal_from_yoneda a := by
    have hT : IsTerminal (DiagSet.asSmallEquivalence.inverse.obj
        (⊤_ ((AsSmall.{u} Atom)ᵒᵖ ⥤ Type u))) :=
      terminalIsTerminal.isTerminalObj _
    let e : Arrow.mk (terminal.from (ball.{u} (AsSmall.down.obj a))) ≅
        Arrow.mk (DiagSet.asSmallEquivalence.inverse.map (terminal.from (yoneda.obj a))) :=
      Arrow.isoMk (Iso.refl _) (terminalIsTerminal.uniqueUpToIso hT) (hT.hom_ext _ _)
    exact (hornWeak.arrow_mk_iso_iff e).1 (terminal_from_ball_mem_hornWeak _)

end Atoms.Diagrammatic

namespace Atoms.TestCategory.BasicLocalizer

open Atoms.Diagrammatic

theorem hornWeak_le_wDiagSet (𝒲 : BasicLocalizer.{u}) : hornWeak.{u} ≤ 𝒲.wDiagSet :=
  grayExactCylinder.{u}.weakEquivalences_le_of_endpoint_mem hornInclusions
    hornInclusions_le_monomorphisms 𝒲.hornInclusions_le_wDiagSet fun ε X ↦
      (IsALocalizer.endpoint_mem_iff_contraction_mem grayExactCylinder ε X).2
        (𝒲.cylinderCompatibleWith_wDiagSet_grayExactCylinder X)

theorem hornWeak_le_wPsh (𝒲 : BasicLocalizer.{0}) :
    hornWeak ≤ 𝒲.wPsh Atom :=
  𝒲.wDiagSet_eq_wPsh ▸ 𝒲.hornWeak_le_wDiagSet

end Atoms.TestCategory.BasicLocalizer

namespace Atoms.Diagrammatic

theorem minimal_wDiagSet_le_hornWeak :
    minimalBasicLocalizer.{u}.wDiagSet ≤ hornWeak.{u} := by
  let 𝒲 := BasicLocalizer.ofTestALocalizer
    (hornWeak.{u}.inverseImage DiagSet.asSmallEquivalence.inverse)
  have hle : minimalBasicLocalizer.W ≤ 𝒲.W := BasicLocalizer.generated_W_le ⊥ 𝒲 bot_le
  have h𝒲 : 𝒲.wDiagSet = hornWeak.{u} := MorphismProperty.ext _ _ fun _ _ f ↦ by
    rw [BasicLocalizer.wDiagSet_iff, BasicLocalizer.ofTestALocalizer_wPsh]
    exact MorphismProperty.map_functor_map_inverse_iff DiagSet.asSmallEquivalence.symm hornWeak f
  rw [← h𝒲]
  intro X Y f hf
  exact hle _ hf

theorem hornWeak_eq_minimal_wDiagSet : hornWeak.{u} = minimalBasicLocalizer.{u}.wDiagSet :=
  le_antisymm (TestCategory.BasicLocalizer.hornWeak_le_wDiagSet _) minimal_wDiagSet_le_hornWeak

theorem hornWeak_uliftYoneda_map {a b : Atom} (f : a ⟶ b) :
    hornWeak.{u} (uliftYoneda.{u}.map f) := by
  rw [hornWeak_eq_minimal_wDiagSet]
  exact TestCategory.BasicLocalizer.wDiagSet_uliftYoneda_map _ f

theorem minimal_wPsh_atom_le_hornWeak :
    minimalBasicLocalizer.wPsh Atom ≤ hornWeak :=
  minimalBasicLocalizer.wDiagSet_eq_wPsh ▸ minimal_wDiagSet_le_hornWeak

theorem hornWeak_eq_minimal_wPsh_atom :
    hornWeak = minimalBasicLocalizer.wPsh Atom :=
  minimalBasicLocalizer.wDiagSet_eq_wPsh ▸ hornWeak_eq_minimal_wDiagSet

end Atoms.Diagrammatic

open CategoryTheory Limits Opposite Atoms Atoms.TestCategory Atoms.Homotopical
open Atoms.Shape MorphismProperty

namespace Atoms.Diagrammatic

theorem isFibrantMinimal_of_isHornFibrant (X : DiagSet.{u}) (hX : IsHornFibrant X) :
    (MorphismProperty.monomorphisms _ ⊓ minimalBasicLocalizer.{u}.wDiagSet).rlp
      (terminal.from X) := by
  rw [← hornWeak_eq_minimal_wDiagSet]
  exact (grayExactCylinder.rlp_trivialCofibrations_terminal_from_iff hornInclusions
    hornInclusions_le_monomorphisms X).2 ((isFibrant_hornInclusions_iff X).2 hX)

private theorem rlp_asSmall_map_of_rlp {E B : DiagSet.{u}} (q : E ⟶ B)
    (hq : (MorphismProperty.monomorphisms _ ⊓ minimalBasicLocalizer.{u}.wDiagSet).rlp q) :
    (MorphismProperty.monomorphisms _ ⊓ minimalBasicLocalizer.{u}.wPsh (AsSmall.{u} Atom)).rlp
      (DiagSet.asSmall.map q) := fun _ _ m hm ↦
  have : Mono m := hm.1
  (DiagSet.asSmallEquivalence.symm.toAdjunction.hasLiftingProperty_iff m q).1
    (hq _ ⟨inferInstance, (minimalBasicLocalizer.wDiagSet_iff _).2
      ((map_functor_map_inverse_iff DiagSet.asSmallEquivalence _ m).2 hm.2)⟩)

private theorem isFibrantMinimal_asSmall_obj (X : DiagSet.{u}) (hX : IsHornFibrant X) :
    (MorphismProperty.monomorphisms _ ⊓ minimalBasicLocalizer.{u}.wPsh (AsSmall.{u} Atom)).rlp
      (terminal.from (DiagSet.asSmall.obj X)) := by
  have hT : IsTerminal (DiagSet.asSmall.obj (⊤_ DiagSet.{u})) :=
    terminalIsTerminal.isTerminalObj _
  let e : Arrow.mk (DiagSet.asSmall.map (terminal.from X)) ≅
      Arrow.mk (terminal.from (DiagSet.asSmall.obj X)) :=
    Arrow.isoMk (Iso.refl _) (hT.uniqueUpToIso terminalIsTerminal) (terminal.hom_ext _ _)
  exact ((MorphismProperty.monomorphisms _ ⊓
    minimalBasicLocalizer.{u}.wPsh (AsSmall.{u} Atom)).rlp.arrow_mk_iso_iff e).1
    (rlp_asSmall_map_of_rlp _ (isFibrantMinimal_of_isHornFibrant X hX))

theorem prod_map_mem_hornWeak_of_fibrant (X : DiagSet.{u}) (hX : IsHornFibrant X)
    {Y Z : DiagSet.{u}} (f : Y ⟶ Z) (hf : hornWeak f) :
    hornWeak (Limits.prod.map (𝟙 X) f) := by
  rw [hornWeak_eq_minimal_wDiagSet, BasicLocalizer.wDiagSet_iff] at hf ⊢
  have h := minimalBasicLocalizer.prod_map_mem_of_fibrant_isTest (AsSmall.{u} Atom)
    isAccessible_minimalBasicLocalizer _ (isFibrantMinimal_asSmall_obj X hX) _ hf
  let e : Arrow.mk (Limits.prod.map (𝟙 (DiagSet.asSmall.obj X)) (DiagSet.asSmall.map f)) ≅
      Arrow.mk (DiagSet.asSmall.map (Limits.prod.map (𝟙 X) f)) :=
    Arrow.isoMk (PreservesLimitPair.iso DiagSet.asSmall X Y).symm
      (PreservesLimitPair.iso DiagSet.asSmall X Z).symm (by
        dsimp only [Arrow.mk_hom, Iso.symm_hom]
        rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, PreservesLimitPair.iso_hom,
          PreservesLimitPair.iso_hom, prodComparison_natural, CategoryTheory.Functor.map_id])
  exact ((minimalBasicLocalizer.wPsh _).arrow_mk_iso_iff e).1 h

theorem prod_ball_projection_mem_hornWeak (X : DiagSet.{u}) (hX : IsHornFibrant X) (a : Atom) :
    hornWeak (Limits.prod.fst : X ⨯ ball.{u} a ⟶ X) := by
  rw [hornWeak_eq_minimal_wDiagSet, BasicLocalizer.wDiagSet_iff]
  have h := minimal_wPsh_prod_fst_yoneda (DiagSet.asSmall.obj X)
    (isFibrantMinimal_asSmall_obj X hX) (AsSmall.up.obj a)
  let e : Arrow.mk (Limits.prod.fst :
        DiagSet.asSmall.obj X ⨯ yoneda.obj (AsSmall.up.obj a) ⟶ DiagSet.asSmall.obj X) ≅
      Arrow.mk (DiagSet.asSmall.map (Limits.prod.fst : X ⨯ ball.{u} a ⟶ X)) :=
    Arrow.isoMk (prod.mapIso (Iso.refl _) (DiagSet.asSmallBallIso a).symm ≪≫
      (PreservesLimitPair.iso DiagSet.asSmall X (ball a)).symm) (Iso.refl _) (by
        dsimp only [Arrow.mk_hom, Arrow.mk_right, Iso.refl_hom]
        rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, PreservesLimitPair.iso_inv_fst]
        simp)
  exact ((minimalBasicLocalizer.wPsh _).arrow_mk_iso_iff e).1 h

end Atoms.Diagrammatic

open CategoryTheory Limits Opposite Atoms Atoms.TestCategory Atoms.Homotopical
open Atoms.Shape MorphismProperty

namespace Atoms.Diagrammatic

def ballTerminalMaps : MorphismProperty DiagSet.{u} :=
  MorphismProperty.ofHoms (fun a : Atom => terminal.from (ball.{u} a))

instance isSmall_ballTerminalMaps : ballTerminalMaps.{u}.IsSmall.{u} :=
  MorphismProperty.isSmall_ofHoms _

theorem hornWeak_eq_generated_ballTerminal :
    generatedALocalizer ballTerminalMaps.{u} = hornWeak.{u} := by
  refine le_antisymm (generatedALocalizer_le ?_) ?_
  · rintro _ _ _ ⟨a⟩
    exact terminal_from_ball_mem_hornWeak a
  · let G := generatedALocalizer ballTerminalMaps.{u}
    have : IsALocalizer.{u, u} (G.inverseImage DiagSet.asSmallEquivalence.inverse) :=
      IsALocalizer.inverseImage_asSmall
    have hle : minimalBasicLocalizer.{u}.wPsh (AsSmall.{u} Atom) ≤
        G.inverseImage DiagSet.asSmallEquivalence.inverse := by
      rw [minimal_wPsh_eq_generatedALocalizer (AsSmall.{u} Atom)]
      refine generatedALocalizer_le ?_
      rintro _ _ _ ⟨a⟩
      have hT : IsTerminal (DiagSet.asSmallEquivalence.inverse.obj
          (⊤_ ((AsSmall.{u} Atom)ᵒᵖ ⥤ Type u))) :=
        terminalIsTerminal.isTerminalObj _
      let e : Arrow.mk (terminal.from (ball.{u} (AsSmall.down.obj a))) ≅
          Arrow.mk (DiagSet.asSmallEquivalence.inverse.map (terminal.from (yoneda.obj a))) :=
        Arrow.isoMk (Iso.refl _) (terminalIsTerminal.uniqueUpToIso hT) (hT.hom_ext _ _)
      exact (G.arrow_mk_iso_iff e).1 (le_generatedALocalizer _ _ ⟨_⟩)
    rw [hornWeak_eq_minimal_wDiagSet]
    intro X Y f hf
    exact (map_functor_map_inverse_iff DiagSet.asSmallEquivalence.symm G f).1
      (hle _ ((minimalBasicLocalizer.wDiagSet_iff f).1 hf))

theorem isHornFibrant_pullback_of_rlp {E B : DiagSet.{u}} (q : E ⟶ B)
    (hq : (MorphismProperty.monomorphisms _ ⊓
      hornWeak).rlp q) (b : ⊤_ DiagSet.{u} ⟶ B) :
    IsHornFibrant (pullback b q) := by
  have h := (MorphismProperty.monomorphisms _ ⊓
    hornWeak).rlp.of_isPullback
      (IsPullback.of_hasPullback b q).flip hq
  rw [show pullback.fst b q = terminal.from _ from terminal.hom_ext _ _] at h
  exact (isFibrant_hornInclusions_iff _).1
    ((grayExactCylinder.{u}.rlp_trivialCofibrations_terminal_from_iff hornInclusions
      hornInclusions_le_monomorphisms (pullback b q)).1 h)

theorem baseChange_ballTerminal_mem {E B : DiagSet.{u}} (q : E ⟶ B)
    (hq : (MorphismProperty.monomorphisms _ ⊓
      hornWeak).rlp q) (a : Atom) :
    baseChangeClass hornWeak q
      (terminal.from (ball.{u} a)) := by
  have := isAccessibleALocalizer_hornWeak.{u}
  intro b
  exact (mem_iff_of_isPullback _
    (IsPullback.of_hasBinaryProduct' (pullback b q) (ball.{u} a))
    (isPullback_baseChangeMap (terminal.from (ball.{u} a)) b q) (Iso.refl _)
    (terminal.hom_ext _ _)).2
    (prod_ball_projection_mem_hornWeak _ (isHornFibrant_pullback_of_rlp q hq b) a)

instance isRightProper_hornWeak : IsRightProper hornWeak.{u} := by
  rw [hornWeak_eq_minimal_wDiagSet]
  exact isRightProper_inverseImage_of_rlp_map.{u, 0, u, u} DiagSet.asSmall _
    rlp_asSmall_map_of_rlp

end Atoms.Diagrammatic
