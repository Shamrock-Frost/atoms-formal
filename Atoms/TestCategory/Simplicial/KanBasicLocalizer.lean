import Atoms.Homotopical.Simplicial.Regular
import Atoms.TestCategory.Simplicial.OrdinaryNerve
import Atoms.TestCategory.Localizer.TestLocalizer
import Atoms.TestCategory.BasicLocalizer.Generation

open CategoryTheory Limits MorphismProperty Simplicial

universe u

namespace Atoms.TestCategory

open Homotopical

instance isTestALocalizer_kanWeak : IsTestALocalizer kanWeak where
  terminal_from_yoneda := terminal_from_yoneda_mem_kanWeak

instance isAccessibleALocalizer_inverseImage_kanWeak :
    IsAccessibleALocalizer.{u, u} (kanWeak.{u}.inverseImage SSet.asSmallEquivalence.inverse) :=
  IsAccessibleALocalizer.inverseImage_asSmall

instance isTestALocalizer_inverseImage_kanWeak :
    IsTestALocalizer (kanWeak.{u}.inverseImage SSet.asSmallEquivalence.inverse) where
  terminal_from_yoneda a := by
    have hT : IsTerminal (SSet.asSmallEquivalence.inverse.obj
        (⊤_ ((AsSmall.{u} SimplexCategory)ᵒᵖ ⥤ Type u))) :=
      terminalIsTerminal.isTerminalObj _
    let e : Arrow.mk (terminal.from Δ[(ULift.down a).len]) ≅
        Arrow.mk (SSet.asSmallEquivalence.inverse.map (terminal.from (yoneda.obj a))) :=
      Arrow.isoMk (SSet.asSmallEquivalence.unitIso.app _ ≪≫
          SSet.asSmallEquivalence.inverse.mapIso (SSet.asSmallStdSimplexIso a))
        (terminalIsTerminal.uniqueUpToIso hT) (hT.hom_ext _ _)
    exact (kanWeak.arrow_mk_iso_iff e).1 (terminal_from_stdSimplex_mem_kanWeak _)

def kanBasicLocalizer : BasicLocalizer.{u} :=
  BasicLocalizer.ofTestALocalizer (kanWeak.{u}.inverseImage SSet.asSmallEquivalence.inverse)

theorem kanBasicLocalizer_wSSet : kanBasicLocalizer.{u}.wSSet = kanWeak.{u} := by
  rw [BasicLocalizer.wSSet, kanBasicLocalizer, BasicLocalizer.ofTestALocalizer_wPsh]
  exact MorphismProperty.ext _ _ fun _ _ f ↦
    map_functor_map_inverse_iff SSet.asSmallEquivalence.symm kanWeak f

theorem kanBasicLocalizer_wPsh : kanBasicLocalizer.{0}.wPsh SimplexCategory = kanWeak := by
  rw [← BasicLocalizer.wSSet_eq_wPsh, kanBasicLocalizer_wSSet]

theorem minimalBasicLocalizer_W_le_kanBasicLocalizer_W :
    minimalBasicLocalizer.{u}.W ≤ kanBasicLocalizer.W :=
  BasicLocalizer.generated_W_le ⊥ _ bot_le

theorem kanBasicLocalizer_W_iff {C D : Cat.{u, u}} (F : C ⟶ D) :
    kanBasicLocalizer.W F ↔ kanWeak (CategoryTheory.nerveFunctor.map F) := by
  rw [BasicLocalizer.W_iff_wSSet_nerveMap, kanBasicLocalizer_wSSet]

theorem kanBasicLocalizer_W_le_minimalBasicLocalizer_W :
    kanBasicLocalizer.W ≤ minimalBasicLocalizer.{u}.W := by
  intro C D F hF
  rw [BasicLocalizer.W_iff_wSSet_nerveMap]
  exact minimalBasicLocalizer.kanWeak_le_wSSet _ ((kanBasicLocalizer_W_iff F).1 hF)

theorem minimalBasicLocalizer_eq_kanBasicLocalizer :
    minimalBasicLocalizer.{u} = kanBasicLocalizer :=
  BasicLocalizer.ext (le_antisymm minimalBasicLocalizer_W_le_kanBasicLocalizer_W
    kanBasicLocalizer_W_le_minimalBasicLocalizer_W)

end Atoms.TestCategory
