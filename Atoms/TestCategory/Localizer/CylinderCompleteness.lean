import Atoms.Homotopical.Cylinder.AbsoluteWeakEquivalence
import Atoms.TestCategory.Localizer.RepresentableRecognition

open CategoryTheory Limits Opposite MorphismProperty HomotopicalAlgebra Atoms.Homotopical
open CostructuredArrow (overMkIsoYoneda overMkIsoYoneda_naturality mono_left_iff)

namespace Atoms.TestCategory

universe u

variable {A : Type u} [SmallCategory A]
  (𝕀 : ExactCylinder.{u} (Aᵒᵖ ⥤ Type u)) (S : MorphismProperty (Aᵒᵖ ⥤ Type u)) [S.IsSmall.{u}]

private theorem anodyne_over_of_arrowIso (hAn : 𝕀.anodyne S = saturation.{u} S)
    (hrep : ∀ {a b : A} (f : a ⟶ b), Mono f → saturation.{u} S (yoneda.map f))
    (X : Aᵒᵖ ⥤ Type u) {P Q : (CostructuredArrow yoneda X)ᵒᵖ ⥤ Type u} (g : P ⟶ Q) {U T : A}
    (f : U ⟶ T) [Mono f] (e : Arrow.mk ((sliceForget X).map g) ≅ Arrow.mk (yoneda.map f)) :
    (𝕀.over X).anodyne (sliceGenerators S X) g := by
  rw [𝕀.anodyne_over_eq_of_eq_saturation S S hAn X]
  refine ((𝕀.anodyne S).arrow_mk_iso_iff e).2 ?_
  rw [hAn]
  exact hrep f inferInstance

theorem anodyne_sliceHom_yoneda_map (hAn : 𝕀.anodyne S = saturation.{u} S)
    (hrep : ∀ {a b : A} (f : a ⟶ b), Mono f → saturation.{u} S (yoneda.map f))
    {U T : A} (f : U ⟶ T) [Mono f] (X : Aᵒᵖ ⥤ Type u) (b : yoneda.obj T ⟶ X) :
    (𝕀.over X).anodyne (sliceGenerators S X) (sliceHom (yoneda.map f) b) :=
  anodyne_over_of_arrowIso 𝕀 S hAn hrep X _ f (sliceForgetMapSliceHomIso (yoneda.map f) b)

theorem anodyne_over_yoneda_map (hAn : 𝕀.anodyne S = saturation.{u} S)
    (hrep : ∀ {a b : A} (f : a ⟶ b), Mono f → saturation.{u} S (yoneda.map f))
    (X : Aᵒᵖ ⥤ Type u) {a b : CostructuredArrow yoneda X} (f : a ⟶ b) [Mono f] :
    (𝕀.over X).anodyne (sliceGenerators S X) (yoneda.map f) :=
  have : Mono f.left := (mono_left_iff f).2 inferInstance
  anodyne_over_of_arrowIso 𝕀 S hAn hrep X _ f.left
    (Arrow.isoMk (sliceForgetYonedaIso a) (sliceForgetYonedaIso b)
      (by
        change (sliceForgetYonedaNatIso X).hom.app a ≫ yoneda.map f.left =
          (sliceForget X).map (yoneda.map f) ≫ (sliceForgetYonedaNatIso X).hom.app b
        simpa [Functor.comp_map, CostructuredArrow.proj] using
          ((sliceForgetYonedaNatIso X).hom.naturality f).symm))

theorem weakEquivalences_over_yoneda_map [EZCategory A]
    (hS : S ≤ MorphismProperty.monomorphisms _) (hAn : 𝕀.anodyne S = saturation.{u} S)
    (hrep : ∀ {a b : A} (f : a ⟶ b), Mono f → saturation.{u} S (yoneda.map f))
    (X : Aᵒᵖ ⥤ Type u) {a b : CostructuredArrow yoneda X} (f : a ⟶ b) :
    (𝕀.over X).weakEquivalences (sliceGenerators S X) (yoneda.map f) := by
  let W := (𝕀.over X).weakEquivalences (sliceGenerators S X)
  have : W.HasTwoOutOfThreeProperty := (𝕀.over X).weakEquivalences_hasTwoOutOfThreeProperty _
  have hmono {a b : CostructuredArrow yoneda X} (i : a ⟶ b) [Mono i] : W (yoneda.map i) :=
    (𝕀.over X).anodyne_le_weakEquivalences _ (sliceGenerators_le_monomorphisms S hS X)
      _ (anodyne_over_yoneda_map 𝕀 S hAn hrep X i)
  have hsplit {a b : CostructuredArrow yoneda X} (p : a ⟶ b) [IsSplitEpi p] :
      W (yoneda.map p) := by
    apply MorphismProperty.of_precomp W (yoneda.map (section_ p)) (yoneda.map p) (hmono _)
    rw [← Functor.map_comp, IsSplitEpi.id]
    simpa using ((𝕀.over X).isomorphisms_le_weakEquivalences (sliceGenerators S X) _
      (MorphismProperty.isomorphisms.infer_property (𝟙 (yoneda.obj b))))
  obtain ⟨c, p, i, hp, hi, hpi⟩ := EZCategory.exists_factorization f
  have := hp
  have := hi
  rw [← hpi, Functor.map_comp]
  exact MorphismProperty.comp_mem _ _ _ (hsplit p) (hmono i)

theorem weakEquivalences_over_eq_minimal [EZCategory A] [HasTrivialAutomorphisms A]
    [minimalBasicLocalizer.{u}.IsLocalTest A] [IsRightProper (minimalBasicLocalizer.{u}.wPsh A)]
    (hS : S ≤ MorphismProperty.monomorphisms _) (hAn : 𝕀.anodyne S = saturation.{u} S)
    (hrep : ∀ {a b : A} (f : a ⟶ b), Mono f → saturation.{u} S (yoneda.map f))
    (hW : 𝕀.weakEquivalences S = minimalBasicLocalizer.{u}.wPsh A) (X : Aᵒᵖ ⥤ Type u) :
    (𝕀.over X).weakEquivalences (sliceGenerators S X) =
      minimalBasicLocalizer.wPsh (CostructuredArrow yoneda X) := by
  have : IsALocalizer ((𝕀.over X).weakEquivalences (sliceGenerators S X)) :=
    (𝕀.over X).isALocalizer_weakEquivalences _ (sliceGenerators_le_monomorphisms _ hS X)
  refine le_antisymm ?_ (minimal_wPsh_le_of_representableMaps_le _ ?_)
  · rw [𝕀.weakEquivalences_over_eq_of_eq_saturation S S hS hAn X,
      minimalBasicLocalizer.wPsh_costructuredArrow_eq X, ← hW]
    exact 𝕀.overWeakEquivalences_le S hS X
  · rintro _ _ _ ⟨i⟩
    exact weakEquivalences_over_yoneda_map 𝕀 S hS hAn hrep _ i.2.2

theorem weakEquivalences_over_eq_underlying [EZCategory A] [HasTrivialAutomorphisms A]
    [minimalBasicLocalizer.{u}.IsLocalTest A] [IsRightProper (minimalBasicLocalizer.{u}.wPsh A)]
    (hS : S ≤ MorphismProperty.monomorphisms _) (hAn : 𝕀.anodyne S = saturation.{u} S)
    (hrep : ∀ {a b : A} (f : a ⟶ b), Mono f → saturation.{u} S (yoneda.map f))
    (hW : 𝕀.weakEquivalences S = minimalBasicLocalizer.{u}.wPsh A) (X : Aᵒᵖ ⥤ Type u) :
    (𝕀.over X).weakEquivalences (sliceGenerators S X) =
      (𝕀.weakEquivalences S).inverseImage (sliceForget X) := by
  rw [weakEquivalences_over_eq_minimal 𝕀 S hS hAn hrep hW X,
    minimalBasicLocalizer.wPsh_costructuredArrow_eq X, hW]

theorem isComplete_of_saturation_yoneda_map [EZCategory A] [HasTrivialAutomorphisms A]
    [minimalBasicLocalizer.{u}.IsLocalTest A] [IsRightProper (minimalBasicLocalizer.{u}.wPsh A)]
    (hS : S ≤ MorphismProperty.monomorphisms _) (hAn : 𝕀.anodyne S = saturation.{u} S)
    (hrep : ∀ {a b : A} (f : a ⟶ b), Mono f → saturation.{u} S (yoneda.map f))
    (hW : 𝕀.weakEquivalences S = minimalBasicLocalizer.{u}.wPsh A) :
    𝕀.IsComplete S :=
  ((𝕀.isComplete_tfae_absolute S hS).out 1 0).1 fun X ↦ by
    rw [← 𝕀.weakEquivalences_over_eq_of_eq_saturation S S hS hAn X]
    exact weakEquivalences_over_eq_underlying 𝕀 S hS hAn hrep hW X

theorem absoluteWeakEquivalences_yoneda_map [EZCategory A] [HasTrivialAutomorphisms A]
    [minimalBasicLocalizer.{u}.IsLocalTest A] [IsRightProper (minimalBasicLocalizer.{u}.wPsh A)]
    (hS : S ≤ MorphismProperty.monomorphisms _) (hAn : 𝕀.anodyne S = saturation.{u} S)
    (hrep : ∀ {a b : A} (f : a ⟶ b), Mono f → saturation.{u} S (yoneda.map f))
    (hW : 𝕀.weakEquivalences S = minimalBasicLocalizer.{u}.wPsh A) {a b : A} (f : a ⟶ b) :
    𝕀.absoluteWeakEquivalences S (yoneda.map f) := by
  have h : 𝕀.weakEquivalences S ≤ 𝕀.absoluteWeakEquivalences S :=
    ((𝕀.isComplete_tfae_absolute S hS).out 0 2).1
      (isComplete_of_saturation_yoneda_map 𝕀 S hS hAn hrep hW)
  rw [hW] at h
  exact h _ (minimalBasicLocalizer.wPsh_yoneda_map A f)

end Atoms.TestCategory
