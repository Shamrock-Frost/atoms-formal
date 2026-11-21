import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Over
import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.FibrewisePath
import Atoms.Homotopical.Simplicial.Joyal

open CategoryTheory Limits Simplicial HomotopicalAlgebra MorphismProperty

universe u

namespace SSet.modelCategoryJoyal

theorem fibration_of_rightFibrations {E B : SSet.{u}} [B.Quasicategory] {p : E ⟶ B}
    (hp : rightFibrations p) : Fibration p := by
  have : InnerFibration p := innerFibration_of_rightFibrations hp
  have : E.Quasicategory := quasicategory_of_innerFibration p
  exact (fibration_iff_isofibration _).2 (Isofibration.of_hasLiftingProperty_vertex _
    (rightAnodyneExtensions_coherentIso_vertex false _ hp))

private lemma rlp_I_iff {X Y : SSet.{u}} (f : X ⟶ Y) :
    modelCategoryQuillen.I.rlp f ↔ Fibration f ∧ WeakEquivalence f := by
  rw [← rlp_monomorphisms]
  change (cofibrations SSet.{u}).rlp _ ↔ _
  rw [cofibrations_rlp, mem_trivialFibrations_iff]

theorem weakEquivalence_of_rlp_I {X Y : SSet.{u}} {f : X ⟶ Y}
    (h : modelCategoryQuillen.I.rlp f) : WeakEquivalence f :=
  ((rlp_I_iff f).1 h).2

theorem trivialFibration_of_rightFibrations_of_fiberMap {P G B : SSet.{u}}
    {pG : G ⟶ B} (hG : rightFibrations pG) {π : P ⟶ G} (hπ : rightFibrations π)
    (h : ∀ b : B _⦋0⦌, WeakEquivalence (fiberMap (p := π ≫ pG) π rfl b)) :
    modelCategoryQuillen.I.rlp π := by
  refine trivialFibration_of_rightFibrations_of_fiber hπ fun g ↦ ?_
  let b := pG.app _ g
  have := kanComplex_fiber_of_rightFibrations hG b
  have : Fibration (fiberMap (p := π ≫ pG) π rfl b) :=
    fibration_of_rightFibrations (rightFibrations_fiberMap π rfl hπ b)
  have := h b
  have hb := (rlp_I_iff (fiberMap (p := π ≫ pG) π rfl b)).2 ⟨inferInstance, inferInstance⟩
  exact MorphismProperty.of_isPullback (isPullback_fiber_fiberMap π pG rfl) hb

theorem weakEquivalence_of_fiberMap {E F B : SSet.{u}} {p : E ⟶ B}
    {q : F ⟶ B} (hp : rightFibrations p) (hq : rightFibrations q) (φ : E ⟶ F) (hφ : φ ≫ q = p)
    (h : ∀ b : B _⦋0⦌, WeakEquivalence (fiberMap φ hφ b)) : WeakEquivalence φ := by
  let ι := fiberwiseMappingPathι q φ
  let π := fiberwiseMappingPathπ q φ
  let r := pullback.fst φ (fiberwisePathEval q 1)
  have hr : r ≫ p = π ≫ q := fiberwiseMappingPath_fst_comp φ hφ
  have hι : ι ≫ π ≫ q = p := by rw [fiberwiseMappingPathι_π_assoc, hφ]
  have hιr : ι ≫ r = 𝟙 E := fiberwiseMappingPathι_fst q φ
  have hrI := trivialFibration_fiberwiseMappingPath_fst hq φ
  have := weakEquivalence_of_rlp_I hrI
  have : WeakEquivalence ι := by
    have : WeakEquivalence (ι ≫ r) := by
      rw [hιr]
      infer_instance
    exact weakEquivalence_of_postcomp ι r
  have hπb (b : B _⦋0⦌) : WeakEquivalence (fiberMap (p := π ≫ q) π rfl b) := by
    have := weakEquivalence_of_rlp_I (trivialFibration_fiberMap r hr hrI b)
    have : WeakEquivalence (fiberMap ι hι b) := by
      have : WeakEquivalence (fiberMap ι hι b ≫ fiberMap r hr b) := by
        rw [← fiberMap_comp]
        simp only [hιr]
        rw [fiberMap_id]
        infer_instance
      exact weakEquivalence_of_postcomp _ (fiberMap r hr b)
    have : WeakEquivalence (fiberMap ι hι b ≫ fiberMap (p := π ≫ q) π rfl b) := by
      rw [← fiberMap_comp]
      simp only [ι, π, fiberwiseMappingPathι_π]
      exact h b
    exact weakEquivalence_of_precomp (fiberMap ι hι b) _
  have := weakEquivalence_of_rlp_I (trivialFibration_of_rightFibrations_of_fiberMap hq
    (rightFibrations_fiberwiseMappingPathπ hp hq φ hφ) hπb)
  rw [← fiberwiseMappingPathι_π q φ]
  infer_instance

theorem weakEquivalence_iff_fiberMap {E F B : SSet.{u}} [B.Quasicategory]
    {p : E ⟶ B} {q : F ⟶ B} (hp : rightFibrations p) (hq : rightFibrations q) (φ : E ⟶ F)
    (hφ : φ ≫ q = p) :
    WeakEquivalence φ ↔ ∀ b : B _⦋0⦌, WeakEquivalence (fiberMap φ hφ b) := by
  refine ⟨fun _ b ↦ ?_, weakEquivalence_of_fiberMap hp hq φ hφ⟩
  have := fibration_of_rightFibrations hp
  have := fibration_of_rightFibrations hq
  exact weakEquivalence_pullback_map_of_fibration (yonedaEquiv.symm b) p q φ hφ

end SSet.modelCategoryJoyal
