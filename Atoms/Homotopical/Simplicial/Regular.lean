import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.Basic
import Atoms.Homotopical.Regular.Saturation
import Atoms.Homotopical.Simplicial.Cells

open CategoryTheory Limits MorphismProperty Simplicial MonoidalCategory

namespace Atoms.Homotopical

universe u

theorem IsAccessibleALocalizer.isRegular_stdSimplex {V : MorphismProperty SSet.{0}}
    [hV : IsAccessibleALocalizer V] (m : ℕ) : IsRegular V Δ[m] :=
  (hV.isRegular_iff_of_iso ((uliftYonedaIsoYoneda.{0} (C := SimplexCategory)).app ⦋m⦌).symm).1
    (hV.isALocalizer.isRegular_yoneda ⦋m⦌)

theorem IsAccessibleALocalizer.isRegularALocalizer_simplex {V : MorphismProperty SSet.{0}}
    [hV : IsAccessibleALocalizer V] : IsRegularALocalizer V :=
  ⟨forall_of_stdSimplex hV.isMonoSaturatedClass_isRegular
    (fun i r hir h ↦ hV.isRegular_of_retract i r hir h) hV.isRegular_stdSimplex⟩

instance IsALocalizer.isRegularALocalizer_simplex {V : MorphismProperty SSet.{0}}
    [IsALocalizer V] : IsRegularALocalizer V :=
  have := (isAccessibleALocalizer_generatedALocalizer
    (⊥ : MorphismProperty SSet.{0})).isRegularALocalizer_simplex
  IsALocalizer.isRegularALocalizer_of_generatedALocalizer_bot

section AsSmall

variable {V : MorphismProperty ((AsSmall.{u} SimplexCategory)ᵒᵖ ⥤ Type u)}

private theorem isMonoSaturatedClass_isRegular_asSmall [hV : IsAccessibleALocalizer V] :
    IsMonoSaturatedClass (fun K : SSet.{u} ↦ IsRegular V (SSet.asSmall.obj K)) where
  of_isPushout h hm h₀ h₁ h₂ :=
    hV.isMonoSaturatedClass_isRegular.of_isPushout (h.map SSet.asSmall) inferInstance h₀ h₁ h₂
  of_isColimit J _ _ F hF _ hc h :=
    hV.isMonoSaturatedClass_isRegular.of_isColimit J (F ⋙ SSet.asSmall)
      (fun i j hij ↦ by have := hF i j hij; exact inferInstanceAs (Mono (SSet.asSmall.map _)))
      (isColimitOfPreserves SSet.asSmall hc) h

private theorem IsAccessibleALocalizer.isRegularALocalizer_asSmallSimplex
    [hV : IsAccessibleALocalizer V] : IsRegularALocalizer V :=
  ⟨fun X ↦ (hV.isRegular_iff_of_iso (SSet.asSmallEquivalence.counitIso.app X)).1
    (forall_of_stdSimplex isMonoSaturatedClass_isRegular_asSmall
      (fun i r hir h ↦ hV.isRegular_of_retract (SSet.asSmall.map i) (SSet.asSmall.map r)
        (by rw [← SSet.asSmall.map_comp, hir, SSet.asSmall.map_id]) h)
      (fun m ↦ (hV.isRegular_iff_of_iso (SSet.asSmallStdSimplexIso (AsSmall.up.obj ⦋m⦌))).2
        (hV.isALocalizer.isRegular_yoneda _)) _)⟩

instance IsALocalizer.isRegularALocalizer_asSmallSimplex [IsALocalizer V] :
    IsRegularALocalizer V :=
  have := (isAccessibleALocalizer_generatedALocalizer
    (⊥ : MorphismProperty ((AsSmall.{u} SimplexCategory)ᵒᵖ ⥤ Type u))
    ).isRegularALocalizer_asSmallSimplex
  IsALocalizer.isRegularALocalizer_of_generatedALocalizer_bot

end AsSmall

end Atoms.Homotopical
