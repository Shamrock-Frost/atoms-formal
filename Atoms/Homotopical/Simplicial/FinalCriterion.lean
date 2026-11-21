import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.SliceComposition
import Atoms.Homotopical.Simplicial.CommaLimit
import Atoms.Homotopical.Simplicial.FibrewiseEquivalence

open CategoryTheory Limits Simplicial HomotopicalAlgebra MorphismProperty

universe u

namespace SSet

private lemma fiberMap_congr {E F B : SSet.{u}} {p : E ⟶ B} {q : F ⟶ B} {φ ψ : E ⟶ F}
    (h : φ = ψ) (hφ : φ ≫ q = p) (hψ : ψ ≫ q = p) (b : B _⦋0⦌) :
    fiberMap φ hφ b = fiberMap ψ hψ b := by
  subst h
  rfl

namespace modelCategoryJoyal

theorem isFinal_iff_fiberMap {E X : SSet.{u}} [X.Quasicategory]
    {p : E ⟶ X} (hp : rightFibrations p) (x : X _⦋0⦌) (Φ : sliceAt X x ⟶ E)
    (hΦ : Φ ≫ p = sliceAtπ X x) :
    IsFinal (Φ.app _ (sliceId X x)) ↔ ∀ t : X _⦋0⦌, WeakEquivalence (fiberMap Φ hΦ t) := by
  have : InnerFibration p := innerFibration_of_rightFibrations hp
  have : E.Quasicategory := quasicategory_of_innerFibration p
  have : (Under.mk (yonedaEquiv.symm x)).right.Quasicategory := ‹X.Quasicategory›
  let v := sliceId X x
  let e := Φ.app _ v
  let πE := sliceAtπ E e
  let πX := sliceAtπ (sliceAt X x) v
  have hsq : sliceAtMap Φ v ≫ πE = πX ≫ Φ := sliceAtMap_comp_sliceAtπ Φ v
  have hA : sliceAtMap Φ v ≫ πE ≫ p = πX ≫ sliceAtπ X x := by
    rw [reassoc_of% hsq, hΦ]
  have hπX : modelCategoryQuillen.I.rlp πX :=
    (isFinal_iff_trivialFibration_sliceAtπ v).1 (rightAnodyneExtensions_sliceId X x)
  have hΦp : rightFibrations (Φ ≫ p) := hΦ ▸ rightFibrations_sliceAtπ X x
  have hAt (t : X _⦋0⦌) : WeakEquivalence (fiberMap (sliceAtMap Φ v) hA t) := by
    have hB : sliceAtMap p e ≫ sliceAtπ X (p.app _ e) = πE ≫ p := sliceAtMap_comp_sliceAtπ p e
    have hD : sliceAtMap (Φ ≫ p) v ≫ sliceAtπ X ((Φ ≫ p).app _ v) = πX ≫ sliceAtπ X x := by
      rw [sliceAtMap_comp_sliceAtπ, hΦ]
    have := weakEquivalence_of_rlp_I
      (trivialFibration_fiberMap _ hB (trivialFibration_sliceAtMap hp e) t)
    have hcomp : fiberMap (sliceAtMap Φ v) hA t ≫ fiberMap _ hB t =
        fiberMap (sliceAtMap (Φ ≫ p) v) hD t :=
      (fiberMap_comp _ _ hA hB t).symm.trans
        (fiberMap_congr (sliceAtMap_comp Φ p v).symm _ hD t)
    have : WeakEquivalence (fiberMap (sliceAtMap Φ v) hA t ≫ fiberMap _ hB t) := by
      rw [hcomp]
      exact weakEquivalence_of_rlp_I
        (trivialFibration_fiberMap _ hD (trivialFibration_sliceAtMap hΦp v) t)
    exact weakEquivalence_of_postcomp _ (fiberMap _ hB t)
  have hiff (t : X _⦋0⦌) : WeakEquivalence (fiberMap Φ hΦ t) ↔
      WeakEquivalence (fiberMap (p := πE ≫ p) πE rfl t) := by
    have hfib : fiberMap (sliceAtMap Φ v) hA t ≫ fiberMap (p := πE ≫ p) πE rfl t =
        fiberMap (p := πX ≫ sliceAtπ X x) πX rfl t ≫ fiberMap Φ hΦ t := by
      rw [← fiberMap_comp, ← fiberMap_comp]
      exact fiberMap_congr hsq _ _ t
    have := hAt t
    have := weakEquivalence_of_rlp_I
      (trivialFibration_fiberMap (q := sliceAtπ X x) πX rfl hπX t)
    refine ⟨fun _ ↦ ?_, fun _ ↦ ?_⟩
    · have : WeakEquivalence (fiberMap (sliceAtMap Φ v) hA t ≫
          fiberMap (p := πE ≫ p) πE rfl t) := by
        rw [hfib]
        infer_instance
      exact weakEquivalence_of_precomp (fiberMap (sliceAtMap Φ v) hA t) _
    · have : WeakEquivalence (fiberMap (p := πX ≫ sliceAtπ X x) πX rfl t ≫
          fiberMap Φ hΦ t) := by
        rw [← hfib]
        infer_instance
      exact weakEquivalence_of_precomp (fiberMap (p := πX ≫ sliceAtπ X x) πX rfl t) _
  rw [isFinal_iff_trivialFibration_sliceAtπ]
  refine ⟨fun h t ↦ (hiff t).2
      (weakEquivalence_of_rlp_I (trivialFibration_fiberMap (q := p) πE rfl h t)),
    fun h ↦ trivialFibration_of_rightFibrations_of_fiberMap hp (rightFibrations_sliceAtπ E e)
      fun t ↦ (hiff t).1 (h t)⟩

theorem isFinal_iff_fiberMap_yonedaMap {E X : SSet.{u}} [X.Quasicategory]
    {p : E ⟶ X} (hp : rightFibrations p) (e : E _⦋0⦌) :
    IsFinal e ↔
      ∀ t : X _⦋0⦌, WeakEquivalence (fiberMap (yonedaMap hp e) (yonedaMap_comp hp e) t) := by
  have h := isFinal_iff_fiberMap hp _ (yonedaMap hp e) (yonedaMap_comp hp e)
  rwa [yonedaMap_sliceId] at h

theorem isFinal_iff_weakEquivalence_of_sliceAt_map {C E : SSet.{u}} [C.Quasicategory]
    {p : E ⟶ C} (hp : rightFibrations p) (e : E _⦋0⦌) (φ : sliceAt C (p.app _ e) ⟶ E)
    (hφ : φ ≫ p = sliceAtπ C (p.app _ e))
    (he : yonedaEquiv.symm (sliceId C (p.app _ e)) ≫ φ = yonedaEquiv.symm e) :
    IsFinal e ↔ WeakEquivalence φ := by
  rw [yonedaEquiv_symm_comp] at he
  have h := isFinal_iff_fiberMap hp _ φ hφ
  rw [yonedaEquiv.symm.injective he] at h
  exact h.trans (weakEquivalence_iff_fiberMap (rightFibrations_sliceAtπ C _) hp φ hφ).symm

theorem exists_weakEquivalence_sliceAt_of_isFinal {C E : SSet.{u}} [C.Quasicategory]
    {p : E ⟶ C} (hp : rightFibrations p) {e : E _⦋0⦌} (he : IsFinal e) :
    ∃ φ : sliceAt C (p.app _ e) ⟶ E, φ ≫ p = sliceAtπ C (p.app _ e) ∧ WeakEquivalence φ :=
  ⟨yonedaMap hp e, yonedaMap_comp hp e, (weakEquivalence_iff_fiberMap
    (rightFibrations_sliceAtπ C _) hp _ (yonedaMap_comp hp e)).2
      ((isFinal_iff_fiberMap_yonedaMap hp e).1 he)⟩

theorem isLimitCone_iff_fiberMap_yonedaMap {K X : SSet.{u}} [X.Quasicategory]
    (d : K ⟶ X) (w : ((slice K).obj (Under.mk d)) _⦋0⦌) :
    IsLimitCone d ((sliceToCommaCone d).app _ w) ↔ ∀ t : X _⦋0⦌,
      WeakEquivalence (fiberMap (yonedaMap (rightFibrations_sliceπ d) w)
        (yonedaMap_comp (rightFibrations_sliceπ d) w) t) :=
  (isFinal_iff_isLimitCone_sliceToCommaCone d w).symm.trans
    (isFinal_iff_fiberMap_yonedaMap (X := X) _ w)

end modelCategoryJoyal

noncomputable def sliceFibreToMappingSpace {K X : SSet.{u}} (d : K ⟶ X) (t : X _⦋0⦌) :
    pullback (sliceπ (Under.mk d)) (yonedaEquiv.symm t) ⟶
      mappingSpace ((ihom K).obj X) ((constDiagram K X).app _ t)
        (yonedaEquiv ((ihomPointEquiv K X).symm d)) :=
  pullback.map _ _ _ _ (sliceToCommaCone d) (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id, sliceToCommaCone_commaConeπ])
      (by rw [Category.comp_id, Category.id_comp]) ≫
    (commaConeFibreIsoMappingSpace d t).hom

theorem modelCategoryJoyal.weakEquivalence_sliceFibreToMappingSpace {K X : SSet.{u}}
    [X.Quasicategory] (d : K ⟶ X) (t : X _⦋0⦌) :
    WeakEquivalence (sliceFibreToMappingSpace d t) := by
  have : (Under.mk d).right.Quasicategory := ‹X.Quasicategory›
  have := fibration_of_rightFibrations (rightFibrations_sliceπ d)
  have : Fibration (commaConeπ d) := (fibration_iff_isofibration _).2 (isofibration_commaConeπ _)
  have := weakEquivalence_sliceToCommaCone d
  have := weakEquivalence_pullback_map_of_fibration (yonedaEquiv.symm t) (sliceπ (Under.mk d))
    (commaConeπ d) (sliceToCommaCone d) (sliceToCommaCone_commaConeπ _)
  rw [sliceFibreToMappingSpace]
  infer_instance

end SSet
