import Atoms.ForMathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.MorphismProperty.Composition

namespace CategoryTheory.MorphismProperty

variable {C : Type*} [Category C]

lemma HasTwoOutOfThreeProperty.sInf {W : Set (MorphismProperty C)}
    (h : ∀ W' ∈ W, W'.HasTwoOutOfThreeProperty) : (sInf W).HasTwoOutOfThreeProperty where
  comp_mem f g hf hg := by
    rw [MorphismProperty.sInf_iff] at hf hg ⊢
    exact fun W' hW' ↦ have := h W' hW'; W'.comp_mem f g (hf W' hW') (hg W' hW')
  of_postcomp f g hg hfg := by
    rw [MorphismProperty.sInf_iff] at hg hfg ⊢
    exact fun W' hW' ↦ have := h W' hW'; W'.of_postcomp f g (hg W' hW') (hfg W' hW')
  of_precomp f g hf hfg := by
    rw [MorphismProperty.sInf_iff] at hf hfg ⊢
    exact fun W' hW' ↦ have := h W' hW'; W'.of_precomp f g (hf W' hW') (hfg W' hW')

instance : (splitEpimorphisms C).IsMultiplicative where
  id_mem _ := inferInstanceAs (IsSplitEpi (𝟙 _))
  comp_mem f g hf hg := by
    have h₁ : IsSplitEpi f := hf
    have h₂ : IsSplitEpi g := hg
    exact inferInstanceAs (IsSplitEpi (f ≫ g))

section Adjunction

variable {C : Type*} [Category C] {D : Type*} [Category D] {L : C ⥤ D} {R : D ⥤ C}
  (adj : L ⊣ R) (W : MorphismProperty D) [W.HasTwoOutOfThreeProperty]

theorem map_unit_app_mem_of_counit [W.ContainsIdentities] (h : ∀ d : D, W (adj.counit.app d))
    (c : C) : W (L.map (adj.unit.app c)) :=
  W.of_postcomp _ (adj.counit.app (L.obj c)) (h _) (by
    rw [adj.left_triangle_components c]
    exact W.id_mem _)

theorem mem_iff_map_map_of_counit (h : ∀ d : D, W (adj.counit.app d)) {d d' : D} (f : d ⟶ d') :
    W f ↔ W (L.map (R.map f)) := by
  rw [← W.postcomp_iff _ _ (h d'), ← Functor.comp_map, adj.counit.naturality f,
    Functor.id_map, W.precomp_iff _ _ (h d)]

end Adjunction

end CategoryTheory.MorphismProperty
