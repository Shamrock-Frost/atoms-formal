import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Quillen
import Atoms.TestCategory.Localizer.ModelStructure
import Atoms.TestCategory.Nerve.Elements
import Atoms.TestCategory.Presheaf.Restriction

open CategoryTheory Limits HomotopicalAlgebra Atoms.Homotopical

namespace Atoms.TestCategory

universe u

variable {A B : Type u} [SmallCategory A] [SmallCategory B]

namespace BasicLocalizer

private theorem isQuillen_of_mono_of_weak {F : (Aᵒᵖ ⥤ Type u) ⥤ (Bᵒᵖ ⥤ Type u)}
    {G : (Bᵒᵖ ⥤ Type u) ⥤ (Aᵒᵖ ⥤ Type u)} (adj : F ⊣ G)
    (V₁ : MorphismProperty (Aᵒᵖ ⥤ Type u)) (V₂ : MorphismProperty (Bᵒᵖ ⥤ Type u))
    [IsAccessibleALocalizer V₁] [IsAccessibleALocalizer V₂]
    (hm : ∀ {X Y : Aᵒᵖ ⥤ Type u} (f : X ⟶ Y), Mono f → Mono (F.map f))
    (hw : ∀ {X Y : Aᵒᵖ ⥤ Type u} (f : X ⟶ Y), V₁ f → V₂ (F.map f)) :
    letI := IsAccessibleALocalizer.modelCategory (V := V₁)
    letI := IsAccessibleALocalizer.modelCategory (V := V₂)
    adj.IsQuillen := by
  let := IsAccessibleALocalizer.modelCategory (V := V₁)
  let := IsAccessibleALocalizer.modelCategory (V := V₂)
  refine ⟨fun X Y f hf => ?_, fun X Y f hf => ?_⟩
  · exact hm f hf
  · rw [mem_trivialCofibrations_iff] at hf
    obtain ⟨h1, h2⟩ := hf
    rw [MorphismProperty.inverseImage_iff, mem_trivialCofibrations_iff]
    exact ⟨(cofibration_iff _).2 (hm f ((cofibration_iff f).1 h1)),
      (weakEquivalence_iff _).2 (hw f ((weakEquivalence_iff f).1 h2))⟩

variable (𝒲 : BasicLocalizer.{u})

theorem isQuillen_restriction (hW : 𝒲.IsAccessible) [𝒲.IsTest A] [𝒲.IsTest B] {u : A ⥤ B}
    (hu : 𝒲.AsphericalFunctor u.toCatHom) :
    letI := isAccessibleALocalizer_wPsh_of_isTest 𝒲 hW (C := A)
    letI := isAccessibleALocalizer_wPsh_of_isTest 𝒲 hW (C := B)
    letI := IsAccessibleALocalizer.modelCategory (V := 𝒲.wPsh A)
    letI := IsAccessibleALocalizer.modelCategory (V := 𝒲.wPsh B)
    (u.op.ranAdjunction (Type u)).IsQuillen := by
  let := isAccessibleALocalizer_wPsh_of_isTest 𝒲 hW (C := A)
  let := isAccessibleALocalizer_wPsh_of_isTest 𝒲 hW (C := B)
  exact isQuillen_of_mono_of_weak (u.op.ranAdjunction (Type u)) (𝒲.wPsh B) (𝒲.wPsh A)
    (fun f h => have := h; Functor.map_mono _ f)
    fun f hf => (𝒲.wPsh_whiskerLeft_iff hu f).2 hf

theorem isQuillen_elementsComparison (hW : 𝒲.IsAccessible) [𝒲.IsTest A] [𝒲.IsTest B]
    {G : (Bᵒᵖ ⥤ Type u) ⥤ (Aᵒᵖ ⥤ Type u)} (adj : elementsFunctor A ⋙ nerveFunctor B ⊣ G) :
    letI := isAccessibleALocalizer_wPsh_of_isTest 𝒲 hW (C := A)
    letI := isAccessibleALocalizer_wPsh_of_isTest 𝒲 hW (C := B)
    letI := IsAccessibleALocalizer.modelCategory (V := 𝒲.wPsh A)
    letI := IsAccessibleALocalizer.modelCategory (V := 𝒲.wPsh B)
    adj.IsQuillen := by
  let := isAccessibleALocalizer_wPsh_of_isTest 𝒲 hW (C := A)
  let := isAccessibleALocalizer_wPsh_of_isTest 𝒲 hW (C := B)
  exact isQuillen_of_mono_of_weak adj (𝒲.wPsh A) (𝒲.wPsh B)
    (fun f h => mono_map_elementsFunctor_comp_nerveFunctor A B f h)
    fun f hf => by
      rw [𝒲.wPsh_eq_inverseImage_elementsFunctor_comp_nerveFunctor (A := A) (B := B)] at hf
      exact hf

end BasicLocalizer

end Atoms.TestCategory
