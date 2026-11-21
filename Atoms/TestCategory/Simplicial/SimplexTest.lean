import Atoms.ForMathlib.CategoryTheory.Category.ULift
import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.Basic
import Atoms.Homotopical.Simplicial.VertexGeneration
import Atoms.TestCategory.Presheaf.Transport

open CategoryTheory Limits Opposite
open Atoms.Homotopical Simplicial MorphismProperty
open MonoidalCategory

universe u

namespace Atoms.TestCategory

def BasicLocalizer.wSSet (𝒲 : BasicLocalizer.{u}) : MorphismProperty SSet.{u} :=
  (𝒲.wPsh (AsSmall.{u} SimplexCategory)).inverseImage SSet.asSmall

theorem BasicLocalizer.wSSet_eq_wPsh (𝒲 : BasicLocalizer.{0}) :
    𝒲.wSSet = 𝒲.wPsh SimplexCategory := by
  rw [𝒲.wPsh_eq_inverseImage_presheafEquivalence
    (AsSmall.equiv : SimplexCategory ≌ AsSmall.{0} SimplexCategory)]
  rfl

namespace BasicLocalizer

theorem aspherical_asSmallSimplexCategory (𝒲 : BasicLocalizer.{u}) :
    𝒲.Aspherical (Cat.of (AsSmall.{u} SimplexCategory)) :=
  𝒲.terminal_aspherical (Cat.of (AsSmall.{u} SimplexCategory))

theorem locallyAspherical_asSmall_stdSimplex_one (𝒲 : BasicLocalizer.{u}) :
    𝒲.LocallyAspherical (AsSmall.{u} SimplexCategory) (SSet.asSmall.obj Δ[1]) := by
  intro a
  have hΔ (m : ℕ) : 𝒲.PshAspherical _ (SSet.asSmall.obj Δ[m]) :=
    (𝒲.pshAspherical_iff_of_iso _ (SSet.asSmallStdSimplexIso (AsSmall.up.obj ⦋m⦌))).2
      (𝒲.pshAspherical_yoneda _ _)
  have hp : 𝒲.PshAspherical _ (SSet.asSmall.obj (Δ[1] ⊗ Δ[(ULift.down a).len])) :=
    prism_of_isPushout (fun X => 𝒲.PshAspherical _ (SSet.asSmall.obj X))
      (fun e h => (𝒲.pshAspherical_iff_of_iso _ (SSet.asSmall.mapIso e)).1 h)
      (fun {X₀ X₁ X₂ X} {f₁ f₂ g₁ g₂} h hm h₀ h₁ h₂ => by
        have : Mono f₁ := hm
        exact 𝒲.pshAspherical_of_isPushout 𝒲.aspherical_asSmallSimplexCategory
          (h.map SSet.asSmall) h₀ h₁ h₂)
      hΔ _
  have e : yoneda.obj a ⨯ SSet.asSmall.obj Δ[1] ≅
      SSet.asSmall.obj (Δ[1] ⊗ Δ[(ULift.down a).len]) :=
    prod.braiding _ _ ≪≫
      prod.mapIso (Iso.refl _) (SSet.asSmallStdSimplexIso a).symm ≪≫
      (PreservesLimitPair.iso SSet.asSmall.{u} Δ[1] Δ[(ULift.down a).len]).symm ≪≫
      SSet.asSmall.mapIso ((CartesianMonoidalCategory.tensorLeftIsoProd
        (Δ[1] : SSet.{u})).app Δ[(ULift.down a).len]).symm
  exact (𝒲.pshAspherical_iff_of_iso _ e).2 hp

end BasicLocalizer

noncomputable def smallSimplexSeparatingInterval :
    SeparatingInterval (AsSmall.{u} SimplexCategory) :=
  .ofFunctor simplicialPoint isPullback_simplicialPoint SSet.asSmall.{u}
    (initialIsInitial.isInitialObj SSet.asSmall.{u} _)

namespace BasicLocalizer

instance isTest_asSmallSimplexCategory (𝒲 : BasicLocalizer.{u}) :
    𝒲.IsTest (AsSmall.{u} SimplexCategory) :=
  𝒲.isTest_of_separatingInterval _ smallSimplexSeparatingInterval
    𝒲.locallyAspherical_asSmall_stdSimplex_one 𝒲.aspherical_asSmallSimplexCategory

instance isALocalizer_wSSet (𝒲 : BasicLocalizer.{u}) : IsALocalizer 𝒲.wSSet :=
  IsALocalizer.inverseImage_asSmall_functor (V := 𝒲.wPsh (AsSmall.{u} SimplexCategory))

theorem kanWeak_le_wSSet (𝒲 : BasicLocalizer.{u}) : kanWeak ≤ 𝒲.wSSet :=
  kanWeak_le_inverseImage SSet.asSmall (fun _ _ _ _ ↦ inferInstance) fun m ↦ by
    have hm : 𝒲.PshAspherical _ (SSet.asSmall.obj Δ[m]) :=
      (𝒲.pshAspherical_iff_of_iso _ (SSet.asSmallStdSimplexIso (AsSmall.up.obj ⦋m⦌))).2
        (𝒲.pshAspherical_yoneda _ _)
    have hT : IsTerminal (SSet.asSmall.obj (⊤_ SSet.{u})) :=
      terminalIsTerminal.isTerminalObj _
    let e : Arrow.mk (terminal.from (SSet.asSmall.obj Δ[m])) ≅
        Arrow.mk (SSet.asSmall.map (terminal.from Δ[m])) :=
      Arrow.isoMk (Iso.refl _) (terminalIsTerminal.uniqueUpToIso hT) (hT.hom_ext _ _)
    exact (MorphismProperty.arrow_mk_iso_iff _ e).1
      ((𝒲.pshAspherical_iff_wPsh_terminal_from _ 𝒲.aspherical_asSmallSimplexCategory _).1 hm)

end BasicLocalizer

namespace BasicLocalizer

instance isTest_simplexCategory (𝒲 : BasicLocalizer.{0}) : 𝒲.IsTest SimplexCategory :=
  (𝒲.isTest_iff_of_equivalence AsSmall.equiv).2 inferInstance

theorem kanWeak_le_wPsh (𝒲 : BasicLocalizer.{0}) : kanWeak ≤ 𝒲.wPsh SimplexCategory :=
  𝒲.wSSet_eq_wPsh ▸ 𝒲.kanWeak_le_wSSet

end BasicLocalizer

end Atoms.TestCategory
