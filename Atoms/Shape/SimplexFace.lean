import Atoms.Molecule.RegularComplex.Morphism
import Atoms.Shape.Horn
import Atoms.Shape.Standard
import Mathlib.Order.Interval.Finset.Fin

open CategoryTheory Order Set Atoms.Molecule Atoms.Molecule.OGP

namespace Atoms.Shape

theorem atomSimplexVertices_top (n : ℕ) :
    atomSimplexVertices n (atomSimplex n).top = Finset.univ := by
  obtain ⟨y, hy⟩ := exists_atomSimplexVertices_eq n (Finset.univ_nonempty (α := Fin (n + 1)))
  exact Finset.eq_univ_of_forall fun j =>
    atomSimplexVertices_subset_iff.2 ((atomSimplex n).le_top y) (hy ▸ Finset.mem_univ j)

def simplexFacet (m : ℕ) (k : Fin (m + 2)) : (atomSimplex (m + 1)).ogp :=
  simplexHom (SimplexCategory.δ k).toOrderHom (atomSimplex m).top

theorem atomSimplexVertices_simplexFacet (m : ℕ) (k : Fin (m + 2)) :
    atomSimplexVertices (m + 1) (simplexFacet m k) = {k}ᶜ := by
  rw [simplexFacet, atomSimplexVertices_simplexHom, atomSimplexVertices_top]
  exact Fin.image_succAbove_univ k

theorem simplexFacet_covBy (m : ℕ) (k : Fin (m + 2)) :
    simplexFacet m k ⋖ (atomSimplex (m + 1)).top := by
  have h₁ := card_atomSimplexVertices (simplexFacet m k)
  have h₂ := card_atomSimplexVertices (atomSimplex (m + 1)).top
  rw [atomSimplexVertices_simplexFacet, Finset.card_compl, Finset.card_singleton,
    Fintype.card_fin] at h₁
  rw [atomSimplexVertices_top, Finset.card_univ, Fintype.card_fin] at h₂
  obtain ⟨c, hfc, hct⟩ := exists_covBy_le_of_lt
    (lt_of_le_of_ne ((atomSimplex (m + 1)).le_top (simplexFacet m k)) fun h => by
      rw [h] at h₁; omega)
  have hgc := Nat.covBy_iff_add_one_eq.1 (hfc.grade ℕ)
  exact (GradeOrder.eq_of_le_of_grade_le hct (by omega)) ▸ hfc

def simplexHornData (m : ℕ) (k : Fin (m + 2)) : AtomicHornData :=
  atomicHornDataOfCovBy (atomSimplex (m + 1)) (simplexFacet m k) (simplexFacet_covBy m k)

theorem mem_hornSubset_simplexHornData_iff (m : ℕ) (k : Fin (m + 2))
    (a : (atomSimplex (m + 1)).ogp) :
    a ∈ hornSubset (simplexHornData m k).toHornData ↔
      ∃ i, i ≠ k ∧ i ∉ atomSimplexVertices (m + 1) a := by
  refine (mem_hornSet_closure_singleton_iff (simplexHornData m k).toHornData rfl).trans ?_
  change (a ≠ (atomSimplex (m + 1)).top ∧ a ≠ simplexFacet m k) ↔ _
  rw [← (atomSimplexVertices_injective _).ne_iff' (atomSimplexVertices_top _),
    ← (atomSimplexVertices_injective _).ne_iff' (atomSimplexVertices_simplexFacet m k)]
  constructor
  · rintro ⟨h₁, h₂⟩
    obtain ⟨i, hi⟩ : ∃ i, i ∉ atomSimplexVertices (m + 1) a := by
      by_contra hc
      push Not at hc
      exact h₁ (Finset.eq_univ_of_forall hc)
    by_cases hik : i = k
    · subst hik
      refine by_contra fun hc => h₂ (Finset.ext fun j => ?_)
      push Not at hc
      rw [Finset.mem_compl, Finset.mem_singleton]
      exact ⟨fun hj hji => hi (hji ▸ hj), hc j⟩
    · exact ⟨i, hik, hi⟩
  · rintro ⟨i, hik, hi⟩
    refine ⟨fun h => hi (h ▸ Finset.mem_univ i), fun h => hi ?_⟩
    rw [h, Finset.mem_compl, Finset.mem_singleton]
    exact hik

theorem boundary_closure_simplexFacet_zero (m : ℕ) (k : Fin (m + 2)) (h0 : k ≠ 0)
    (hl : k ≠ Fin.last (m + 1)) (α : Bool) :
    (atomSimplex (m + 1)).ogp.boundary (LowerSet.Iic (simplexFacet m k)) 0 α =
      (atomSimplex (m + 1)).ogp.boundary ⊤ 0 α := by
  let j : Fin (m + 2) := cond α (Fin.last (m + 1)) 0
  have hj : ∀ i : Fin (m + 2), i ≠ j → (i < j ↔ α = true) := by
    intro i hij
    cases α
    · simp [j]
    · simpa [j] using Fin.lt_last_iff_ne_last.2 hij
  have hjk : j ∈ atomSimplexVertices (m + 1) (simplexFacet m k) := by
    rw [atomSimplexVertices_simplexFacet, Finset.mem_compl, Finset.mem_singleton]
    cases α
    · exact Ne.symm h0
    · exact Ne.symm hl
  obtain ⟨w, hw⟩ := exists_atomSimplexVertices_eq (m + 1) (Finset.singleton_nonempty j)
  rw [← (atomSimplex (m + 1)).Iic_top,
    boundary_closure_zero_atomSimplex _ α hw hjk fun i _ => hj i,
    boundary_closure_zero_atomSimplex _ α hw (atomSimplexVertices_top (m + 1) ▸
      Finset.mem_univ j) fun i _ => hj i]

theorem dimension_atomSimplex (n : ℕ) : (atomSimplex n).dimension = n := by
  have := card_atomSimplexVertices (atomSimplex n).top
  rw [atomSimplexVertices_top, Finset.card_univ, Fintype.card_fin] at this
  rw [(atomSimplex n).dimension_eq]
  omega

theorem dimension_atomSimplex_one_pos : 0 < (atomSimplex 1).dimension := by
  rw [dimension_atomSimplex]
  exact Nat.one_pos

theorem orient_top_simplexFacet (m : ℕ) (k : Fin (m + 2)) :
    (atomSimplex (m + 1)).ogp.orient (simplexFacet_covBy m k) =
      decide (k.val % 2 = 0) := by
  rw [orient_atomSimplex_erase (v := k) (atomSimplexVertices_top _ ▸ Finset.mem_univ k)
    (by rw [atomSimplexVertices_simplexFacet, atomSimplexVertices_top,
      Finset.compl_singleton]) (simplexFacet_covBy m k), atomSimplexVertices_top,
    Finset.filter_gt_eq_Iio, Fin.card_Iio]

theorem mem_faceSet_top_atomSimplex_iff (m : ℕ) (α : Bool) (x : (atomSimplex (m + 1)).ogp) :
    x ∈ (atomSimplex (m + 1)).ogp.faces α (atomSimplex (m + 1)).top ↔
      ∃ k : Fin (m + 2), simplexFacet m k = x ∧ decide (k.val % 2 = 0) = α := by
  constructor
  · rintro ⟨hcov, ho⟩
    have h₁ := card_atomSimplexVertices x
    have h₂ := card_atomSimplexVertices (atomSimplex (m + 1)).top
    have hg := Nat.covBy_iff_add_one_eq.1 (hcov.grade ℕ)
    rw [atomSimplexVertices_top, Finset.card_univ, Fintype.card_fin] at h₂
    have hc : (atomSimplexVertices (m + 1) x)ᶜ.card = 1 := by
      rw [Finset.card_compl, Fintype.card_fin]
      omega
    obtain ⟨k, hk⟩ := Finset.card_eq_one.1 hc
    have hx' : atomSimplexVertices (m + 1) x = {k}ᶜ := by
      rw [← hk, compl_compl]
    have hxk : simplexFacet m k = x := atomSimplexVertices_injective _
      ((atomSimplexVertices_simplexFacet m k).trans hx'.symm)
    refine ⟨k, hxk, ?_⟩
    rw [← orient_top_simplexFacet]
    exact ((atomSimplex (m + 1)).ogp.orient_congr rfl hxk (simplexFacet_covBy m k) hcov).trans ho
  · rintro ⟨k, rfl, hk⟩
    exact ⟨simplexFacet_covBy m k, (orient_top_simplexFacet m k).trans hk⟩

theorem image_univ_simplexHom {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1)) :
    Set.range (simplexHom f) =
      (LowerSet.Iic (simplexHom f (atomSimplex m).top) : Set (atomSimplex n).ogp) := by
  rw [← Set.image_univ, ← LowerSet.coe_top, ← (atomSimplex m).Iic_top, LowerSet.coe_Iic,
    (Atom.isMap (simplexHom f)).image_Iic, LowerSet.coe_Iic]

theorem boundary_univ_one_atomSimplex_two (α : Bool) :
    (atomSimplex 2).ogp.boundary ⊤ 1 α =
      lowerClosure ((atomSimplex 2).ogp.faces α (atomSimplex 2).top) := by
  rw [← (atomSimplex 2).Iic_top]
  exact boundary_Iic (by rw [← (atomSimplex 2).dimension_eq, dimension_atomSimplex]) α

theorem image_univ_simplexHom_δ_atomSimplex_one (α : Bool) :
    Set.range (simplexHom (SimplexCategory.δ (cond α 0 1 : Fin 2)).toOrderHom) =
      ((atomSimplex 1).ogp.boundary ⊤ 0 α : Set (atomSimplex 1).ogp) := by
  set v := simplexHom (SimplexCategory.δ (cond α 0 1 : Fin 2)).toOrderHom (atomSimplex 0).top
  have hv : atomSimplexVertices 1 v = {cond α 1 0} := by
    rw [atomSimplexVertices_simplexHom, atomSimplexVertices_top, Finset.univ_unique (α := Fin 1),
      Finset.image_singleton, Finset.singleton_inj, Fin.default_eq_zero]
    cases α
    · simp only [cond_false, SimplexCategory.δ, SimplexCategory.mkHom,
        SimplexCategory.Hom.toOrderHom_mk, OrderEmbedding.toOrderHom_coe,
        Fin.succAboveOrderEmb_apply, Fin.succAbove_ne_zero_zero one_ne_zero]
    · simp only [cond_true, SimplexCategory.δ, SimplexCategory.mkHom,
        SimplexCategory.Hom.toOrderHom_mk, OrderEmbedding.toOrderHom_coe,
        Fin.succAboveOrderEmb_apply, Fin.zero_succAbove, Fin.succ_zero_eq_one]
  rw [image_univ_simplexHom, ← (atomSimplex 1).Iic_top,
    boundary_closure_zero_atomSimplex _ α hv (atomSimplexVertices_top 1 ▸ Finset.mem_univ _)
      (fun i _ hi => by cases α <;> fin_cases i <;> first | exact absurd rfl hi | decide)]

theorem boundary_univ_zero_atomSimplex_one (α : Bool) :
    (atomSimplex 1).ogp.boundary ⊤ 0 α =
      .Iic (simplexHom (SimplexCategory.δ (cond α 0 1 : Fin 2)).toOrderHom (atomSimplex 0).top) :=
  SetLike.coe_injective ((image_univ_simplexHom_δ_atomSimplex_one α).symm.trans
    (image_univ_simplexHom _))

theorem boundary_Iic_simplexHom_δ_atomSimplex_one (i : Fin 2) (β : Bool) :
    (atomSimplex 1).ogp.boundary
        (.Iic (simplexHom (SimplexCategory.δ i).toOrderHom (atomSimplex 0).top)) 0 β =
      .Iic (simplexHom (SimplexCategory.δ i).toOrderHom (atomSimplex 0).top) := by
  have h (α : Bool) := boundary_univ_zero_atomSimplex_one α ▸ krullDim_boundary_le ⊤ 0 α
  revert i
  rw [Fin.forall_fin_two]
  exact ⟨boundary_eq_self (h true) β, boundary_eq_self (h false) β⟩

theorem boundary_univ_one_atomSimplex_one (α : Bool) :
    (atomSimplex 1).ogp.boundary ⊤ 1 α = ⊤ :=
  boundary_eq_self (by
    rw [LowerSet.krullDim_top, (atomSimplex 1).krullDim_eq_dimension, dimension_atomSimplex]) α

theorem isPastingIn_atomSimplex_two :
    (atomSimplex 2).ogp.IsPastingIn 0 (LowerSet.Iic (simplexFacet 1 2))
      (LowerSet.Iic (simplexFacet 1 0))
      ((atomSimplex 2).ogp.boundary ⊤ 1 true) := by
  obtain ⟨w, hw⟩ := exists_atomSimplexVertices_eq 2 (Finset.singleton_nonempty (1 : Fin 3))
  have hone : ∀ i : Fin 3, i ∈ ({2} : Finset (Fin 3))ᶜ → i ∈ ({0} : Finset (Fin 3))ᶜ → i = 1 := by
    decide
  have hinter : LowerSet.Iic (simplexFacet 1 2) ⊓ LowerSet.Iic (simplexFacet 1 0) =
      LowerSet.Iic w := by
    refine SetLike.ext fun x => ?_
    rw [LowerSet.mem_inf_iff, LowerSet.mem_Iic_iff, LowerSet.mem_Iic_iff, LowerSet.mem_Iic_iff,
      ← atomSimplexVertices_subset_iff, ← atomSimplexVertices_subset_iff,
      ← atomSimplexVertices_subset_iff, hw,
      atomSimplexVertices_simplexFacet, atomSimplexVertices_simplexFacet]
    exact ⟨fun ⟨h₂, h₀⟩ i hi => Finset.mem_singleton.2 (hone i (h₂ hi) (h₀ hi)),
      fun h => ⟨h.trans (by decide), h.trans (by decide)⟩⟩
  have hmeet (α : Bool) : LowerSet.Iic (simplexFacet 1 2) ⊓ LowerSet.Iic (simplexFacet 1 0) =
      (atomSimplex 2).ogp.boundary (.Iic (simplexFacet 1 (cond α 2 0))) 0 α := by
    rw [hinter, boundary_closure_zero_atomSimplex _ α hw
      (by rw [atomSimplexVertices_simplexFacet]; revert α; decide)
      (fun i hi _ => by rw [atomSimplexVertices_simplexFacet] at hi; revert α i; decide)]
  refine ⟨?_, hmeet true, hmeet false⟩
  rw [boundary_univ_one_atomSimplex_two]
  refine SetLike.ext fun x => ?_
  rw [LowerSet.mem_sup_iff, LowerSet.mem_Iic_iff, LowerSet.mem_Iic_iff, mem_lowerClosure]
  constructor
  · rintro (h | h)
    · exact ⟨_, (mem_faceSet_top_atomSimplex_iff 1 true _).2 ⟨2, rfl, rfl⟩, h⟩
    · exact ⟨_, (mem_faceSet_top_atomSimplex_iff 1 true _).2 ⟨0, rfl, rfl⟩, h⟩
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨k, rfl, hk⟩ := (mem_faceSet_top_atomSimplex_iff 1 true y).1 hy
    fin_cases k
    · exact Or.inr hxy
    · exact absurd hk (by decide)
    · exact Or.inl hxy

def simplexHomEmb {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1)) (hf : Function.Injective f) :
    (atomSimplex m).ogp ⟶ (atomSimplex n).ogp :=
  ConcreteCategory.ofHom ⟨simplexHom f, Atom.isMorphism_of_isInclusionHom (simplexHom f)
    (isInclusionHom_simplexHom_of_injective f hf)⟩

instance isInclusion_simplexHomEmb {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1))
    (hf : Function.Injective f) : IsInclusion (simplexHomEmb f hf) :=
  ⟨isInclusionHom_simplexHom_of_injective f hf⟩

theorem eq_top_atomSimplex_zero (x : (atomSimplex 0).ogp) : x = (atomSimplex 0).top := by
  obtain ⟨i, hi⟩ := simplexVertices_nonempty 0 ((FiniteOGP.ofOGPIso (simplex 0)).inv x)
  refine atomSimplexVertices_injective 0 ((Finset.eq_univ_of_forall fun j => ?_).trans
    (atomSimplexVertices_top 0).symm)
  obtain rfl : j = i := Fin.ext (by have := j.isLt; have := i.isLt; omega)
  exact hi

end Atoms.Shape
