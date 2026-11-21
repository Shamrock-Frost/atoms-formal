import Atoms.Molecule.RegularComplex.Comap
import Atoms.Molecule.RegularComplex.Thin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.LinearAlgebra.Pi

universe u v w

open CategoryTheory Order

namespace Atoms.Molecule.OGP

variable {P : OGP.{u}} {Q : OGP.{v}} {R : OGP.{w}}

abbrev gradeSet (P : OGP.{u}) (n : ℕ) : Type u := {x : P // grade ℕ x = n}

def indicatorChain (S : Set P) [DecidablePred (· ∈ S)] (n : ℕ) : P.gradeSet n → ℤ :=
  fun x => if x.1 ∈ S then 1 else 0

@[simp] theorem indicatorChain_apply (S : Set P) [DecidablePred (· ∈ S)] (n : ℕ)
    (x : P.gradeSet n) : indicatorChain S n x = if x.1 ∈ S then 1 else 0 :=
  rfl

section Chains

variable [Fintype P] [DecidableLE P]

def incidence (x y : P) : ℤ :=
  if y ∈ P.faces true x then 1 else if y ∈ P.faces false x then -1 else 0

theorem incidence_eq_sub (x y : P) : incidence x y =
    (if y ∈ P.faces true x then 1 else 0) - (if y ∈ P.faces false x then 1 else 0) := by
  have hd : Disjoint (P.faces true x) (P.faces false x) := P.disjoint_faces x true
  unfold incidence
  by_cases ht : y ∈ P.faces true x
  · rw [if_pos ht, if_pos ht, if_neg (Set.disjoint_left.1 hd ht), sub_zero]
  · rw [if_neg ht, if_neg ht, zero_sub]
    by_cases hf : y ∈ P.faces false x
    · rw [if_pos hf, if_pos hf]
    · rw [if_neg hf, if_neg hf, neg_zero]

theorem incidence_eq_of_covBy {x y : P} (h : y ⋖ x) :
    incidence x y = if P.orient h then 1 else -1 := by
  have hf : y ∈ P.faces (P.orient h) x := ⟨h, rfl⟩
  have hd : Disjoint (P.faces true x) (P.faces false x) := P.disjoint_faces x true
  rw [incidence_eq_sub]
  cases ho : P.orient h
  · rw [ho] at hf
    rw [if_neg (Set.disjoint_right.1 hd hf), if_pos hf]
    rfl
  · rw [ho] at hf
    rw [if_pos hf, if_neg (Set.disjoint_left.1 hd hf), sub_zero]
    rfl

theorem covBy_of_incidence_ne_zero {x y : P} (h : incidence x y ≠ 0) : y ⋖ x := by
  unfold incidence at h
  by_cases ht : y ∈ P.faces true x
  · exact ht.1
  · by_cases hf : y ∈ P.faces false x
    · exact hf.1
    · rw [if_neg ht, if_neg hf] at h
      exact (h rfl).elim

omit [DecidableLE P] in
private theorem sum_gradeSet {M : Type*} [AddCommMonoid M] (n : ℕ) (F : P → M)
    (hF : ∀ x, F x ≠ 0 → grade ℕ x = n) : ∑ x : P.gradeSet n, F x.1 = ∑ x : P, F x := by
  rw [← Finset.sum_subtype (Finset.univ.filter fun x : P => grade ℕ x = n) (by simp) F,
    Finset.sum_filter_of_ne fun x _ => hF x]

variable (P) in
def chainDiff (n : ℕ) : (P.gradeSet (n + 1) → ℤ) →ₗ[ℤ] (P.gradeSet n → ℤ) where
  toFun g y := ∑ x, g x * incidence x.1 y.1
  map_add' g g' := funext fun y => by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' a g := funext fun y => by
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum, RingHom.id_apply]

theorem chainDiff_apply (n : ℕ) (g : P.gradeSet (n + 1) → ℤ) (y : P.gradeSet n) :
    P.chainDiff n g y = ∑ x, g x * incidence x.1 y.1 :=
  rfl

theorem chainDiff_single [DecidableEq P] (n : ℕ) (x : P.gradeSet (n + 1)) :
    P.chainDiff n (Pi.single x 1) = fun y => incidence x.1 y.1 := by
  funext y
  rw [chainDiff_apply, Fintype.sum_eq_single x fun x' hx' => by rw [Pi.single_eq_of_ne hx',
    zero_mul], Pi.single_eq_same, one_mul]

variable (P) in
def chainAugmentation : (P.gradeSet 0 → ℤ) →ₗ[ℤ] ℤ where
  toFun g := ∑ x, g x
  map_add' g g' := by simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' a g := by simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]

omit [DecidableLE P] in
theorem chainAugmentation_apply (g : P.gradeSet 0 → ℤ) : P.chainAugmentation g = ∑ x, g x :=
  rfl

private theorem sum_incidence_mul_incidence (hP : P.IsOrientedThin) {n : ℕ}
    (x : P.gradeSet (n + 2)) (z : P.gradeSet n) :
    ∑ y : P.gradeSet (n + 1), incidence x.1 y.1 * incidence y.1 z.1 = 0 := by
  have hne {y : P} (h : incidence x.1 y * incidence y z.1 ≠ 0) : z.1 ⋖ y ∧ y ⋖ x.1 :=
    ⟨covBy_of_incidence_ne_zero (right_ne_zero_of_mul h),
      covBy_of_incidence_ne_zero (left_ne_zero_of_mul h)⟩
  rw [sum_gradeSet (n + 1) (fun y => incidence x.1 y * incidence y z.1) fun y h => by
    have := Nat.covBy_iff_add_one_eq.1 ((hne h).1.grade ℕ)
    rw [← this, z.2]]
  by_cases hzx : z.1 < x.1
  · obtain ⟨z₁, z₂, h₁₂, hI, hs⟩ := hP.diamond x.1 z.1 hzx (by rw [x.2, z.2])
    have hmem (y : P) : y ∈ Set.Ioo z.1 x.1 ↔ y = z₁ ∨ y = z₂ := by rw [hI]; rfl
    have hcov {y : P} (hy : y = z₁ ∨ y = z₂) : z.1 ⋖ y ∧ y ⋖ x.1 := by
      have hy' := (hmem y).2 hy
      have h₁ := grade_strictMono (𝕆 := ℕ) hy'.1
      have h₂ := grade_strictMono (𝕆 := ℕ) hy'.2
      rw [x.2] at h₂
      rw [z.2] at h₁
      exact ⟨GradeOrder.covBy_of_le_of_grade_eq_add_one hy'.1.le (by rw [z.2]; omega),
        GradeOrder.covBy_of_le_of_grade_eq_add_one hy'.2.le (by rw [x.2]; omega)⟩
    obtain ⟨c₁, c₁'⟩ := hcov (Or.inl rfl)
    obtain ⟨c₂, c₂'⟩ := hcov (Or.inr rfl)
    rw [Fintype.sum_eq_add z₁ z₂ h₁₂ fun y hy => by
      by_contra h
      obtain ⟨a, b⟩ := hne h
      rcases (hmem y).1 ⟨a.lt, b.lt⟩ with rfl | rfl
      exacts [hy.1 rfl, hy.2 rfl]]
    have hsign := hs c₁ c₁' c₂ c₂'
    rw [incidence_eq_of_covBy c₁, incidence_eq_of_covBy c₁', incidence_eq_of_covBy c₂,
      incidence_eq_of_covBy c₂']
    revert hsign
    cases P.orient c₁ <;> cases P.orient c₁' <;> cases P.orient c₂ <;> cases P.orient c₂' <;>
      decide
  · exact Finset.sum_eq_zero fun y _ => by
      by_contra h
      obtain ⟨a, b⟩ := hne h
      exact hzx (a.lt.trans b.lt)

theorem chainDiff_comp_chainDiff (hP : P.IsOrientedThin) (n : ℕ) :
    P.chainDiff n ∘ₗ P.chainDiff (n + 1) = 0 := by
  refine LinearMap.ext fun g => funext fun z => ?_
  simp only [LinearMap.comp_apply, chainDiff_apply, LinearMap.zero_apply, Pi.zero_apply,
    Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  exact Finset.sum_eq_zero fun x _ => by
    rw [← Finset.mul_sum, sum_incidence_mul_incidence hP x z, mul_zero]

theorem chainAugmentation_comp_chainDiff (hP : P.IsOrientedThin) :
    P.chainAugmentation ∘ₗ P.chainDiff 0 = 0 := by
  refine LinearMap.ext fun g => ?_
  simp only [LinearMap.comp_apply, chainAugmentation_apply, chainDiff_apply, LinearMap.zero_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun x _ => ?_
  classical
  rw [← Finset.mul_sum, sum_gradeSet 0 (fun y => incidence x.1 y) fun y h => by
    have := Nat.covBy_iff_add_one_eq.1 ((covBy_of_incidence_ne_zero h).grade ℕ)
    rw [x.2] at this
    omega]
  obtain ⟨s, t, hst, hs, ht⟩ := hP.exists_faces_eq x.2
  have hinc (y : P) : incidence x.1 y = (if y = t then 1 else 0) - (if y = s then 1 else 0) := by
    simp only [incidence_eq_sub, hs, ht, Set.mem_singleton_iff]
  rw [Fintype.sum_eq_add t s (Ne.symm hst) fun y hy => by
    rw [hinc, if_neg hy.1, if_neg hy.2, sub_zero]]
  simp only [hinc, if_neg hst, if_neg (Ne.symm hst), if_pos, sub_zero, zero_sub, add_neg_cancel,
    mul_zero]

def chainComplex (hP : P.IsOrientedThin) : ChainComplex (ModuleCat.{u} ℤ) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of ℤ (P.gradeSet n → ℤ))
    (fun n => ModuleCat.ofHom (P.chainDiff n)) fun n => by
      rw [← ModuleCat.ofHom_comp, chainDiff_comp_chainDiff hP]
      rfl

theorem chainComplex_d (hP : P.IsOrientedThin) (n : ℕ) :
    (chainComplex hP).d (n + 1) n = ModuleCat.ofHom (P.chainDiff n) :=
  ChainComplex.of_d (fun n => ModuleCat.of ℤ (P.gradeSet n → ℤ))
    (fun n => ModuleCat.ofHom (P.chainDiff n)) n

theorem chainDiff_indicatorChain {n : ℕ} {U : LowerSet P} [DecidablePred (· ∈ U)]
    [∀ α, DecidablePred (· ∈ P.facesIn U n α)] (hU : IsMoleculeIn P U)
    (hn : krullDim U = (n + 1 : ℕ)) :
    P.chainDiff n (indicatorChain U (n + 1)) =
      indicatorChain (P.facesIn U n true) n - indicatorChain (P.facesIn U n false) n := by
  funext y
  have hdim : krullDim U ≤ (grade ℕ y.1 + 1 : ℕ) := by rw [y.2, hn]
  obtain ⟨a, ha⟩ : ∃ a : Bool → ℤ,
      ∀ α, a α = ∑ x : P, if x ∈ (U : Set P) ∧ y.1 ∈ P.faces α x then 1 else 0 :=
    ⟨_, fun _ => rfl⟩
  have h1 (α : Bool) (h : (P.cofaces α y.1 ∩ U).Nonempty) : a α = 1 := by
    obtain ⟨c, hc⟩ := h
    rw [ha, Fintype.sum_eq_single c fun x hx => if_neg fun h' =>
      hx (hU.subsingleton_cofaces_inter hdim α ⟨h'.2, h'.1⟩ hc), if_pos ⟨hc.2, hc.1⟩]
  have h0 (α : Bool) (h : ¬ (P.cofaces α y.1 ∩ U).Nonempty) : a α = 0 := by
    rw [ha]
    exact Finset.sum_eq_zero fun x _ => if_neg fun h' => h ⟨x, h'.2, h'.1⟩
  have hfaces (α : Bool) : (if y.1 ∈ P.facesIn U n α then (1 : ℤ) else 0) =
      if y.1 ∈ (U : Set P) then 1 - a (!α) else 0 := by
    by_cases hy : y.1 ∈ (U : Set P)
    · rw [if_pos hy]
      by_cases hc : (P.cofaces (!α) y.1 ∩ U).Nonempty
      · rw [h1 _ hc, sub_self, if_neg fun h =>
          hc.ne_empty (Set.disjoint_iff_inter_eq_empty.1 h.2.2)]
      · rw [h0 _ hc, sub_zero, if_pos ⟨hy, y.2, Set.disjoint_iff_inter_eq_empty.2
          (Set.not_nonempty_iff_eq_empty.1 hc)⟩]
    · rw [if_neg hy, if_neg fun h => hy h.1]
  have hsum := sum_gradeSet (n + 1)
    (fun x => (if x ∈ (U : Set P) then 1 else 0) * incidence x y.1) fun x h => by
      have := Nat.covBy_iff_add_one_eq.1
        ((covBy_of_incidence_ne_zero (right_ne_zero_of_mul h)).grade ℕ)
      rw [← this, y.2]
  rw [chainDiff_apply, Pi.sub_apply, indicatorChain_apply, indicatorChain_apply, hfaces, hfaces]
  simp only [indicatorChain_apply]
  rw [hsum]
  simp only [incidence_eq_sub, mul_sub, ite_zero_mul_ite_zero, mul_one, Finset.sum_sub_distrib]
  rw [← ha, ← ha]
  by_cases hy : y.1 ∈ (U : Set P)
  · rw [if_pos hy, if_pos hy, Bool.not_true, Bool.not_false, sub_sub_sub_cancel_left]
  · have hno (α : Bool) : ¬ (P.cofaces α y.1 ∩ U).Nonempty := fun ⟨c, hc, hcU⟩ =>
      hy (U.lower hc.1.le hcU)
    rw [if_neg hy, if_neg hy, h0 true (hno true), h0 false (hno false), sub_zero]

end Chains

section Comaps

def comapChainHom (c : P → Q) (n : ℕ) : (Q.gradeSet n → ℤ) →ₗ[ℤ] (P.gradeSet n → ℤ) where
  toFun g x := if h : grade ℕ (c x.1) = n then g ⟨c x.1, h⟩ else 0
  map_add' g g' := funext fun x => by
    by_cases h : grade ℕ (c x.1) = n
    · simp only [dif_pos h, Pi.add_apply]
    · simp only [dif_neg h, Pi.add_apply, add_zero]
  map_smul' a g := funext fun x => by
    by_cases h : grade ℕ (c x.1) = n
    · simp only [dif_pos h, Pi.smul_apply, RingHom.id_apply]
    · simp only [dif_neg h, Pi.smul_apply, smul_zero, RingHom.id_apply]

theorem comapChainHom_apply (c : P → Q) (n : ℕ) (g : Q.gradeSet n → ℤ) (x : P.gradeSet n) :
    comapChainHom c n g x = if h : grade ℕ (c x.1) = n then g ⟨c x.1, h⟩ else 0 :=
  rfl

private theorem IsComap.comapChainHom_single [DecidableEq Q] {c : P → Q} (hc : IsComap c) {n : ℕ}
    (y : Q.gradeSet n) [DecidablePred (· ∈ lowerPreimage hc.monotone (.Iic y.1))] :
    comapChainHom c n (Pi.single y 1) =
      indicatorChain (lowerPreimage hc.monotone (.Iic y.1)) n := by
  classical
  funext x
  rw [comapChainHom_apply, indicatorChain_apply]
  have hx := hc.grade_le x.1
  rw [x.2] at hx
  by_cases h : grade ℕ (c x.1) = n
  · rw [dif_pos h, Pi.single_apply]
    refine if_congr ⟨fun he => ?_, fun hle => ?_⟩ rfl rfl
    · rw [SetLike.mem_coe, mem_lowerPreimage, ← he]
      exact LowerSet.mem_Iic_iff.2 le_rfl
    · rw [SetLike.mem_coe, mem_lowerPreimage] at hle
      exact Subtype.ext (GradeOrder.eq_of_le_of_grade_le (LowerSet.mem_Iic_iff.1 hle)
        (by rw [h, y.2]))
  · rw [dif_neg h, if_neg fun hle => h (le_antisymm (by
      have := grade_mono (𝕆 := ℕ) (LowerSet.mem_Iic_iff.1 hle)
      rwa [y.2] at this) hx)]

theorem IsComap.mem_facesIn_lowerPreimage_Iic {c : P → Q} (hc : IsComap c) {n : ℕ} {y : Q}
    (hy : grade ℕ y = n + 1) {α : Bool} {x : P} (hx : grade ℕ x = n) :
    x ∈ P.facesIn (lowerPreimage hc.monotone (.Iic y)) n α ↔ c x ∈ Q.faces α y := by
  have hb := hc.boundary_Iic y n α
  rw [OGP.boundary_Iic hy] at hb
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hxb : x ∈ lowerPreimage hc.monotone (lowerClosure (Q.faces α y)) := by
      rw [hb]
      exact mem_boundary_of_mem_facesIn h le_rfl
    obtain ⟨z, hz, hxz⟩ := mem_lowerClosure.1 hxb
    have hzd := Nat.covBy_iff_add_one_eq.1 (hz.1.grade ℕ)
    rwa [GradeOrder.eq_of_le_of_grade_le hxz (by
      have := hc.grade_le x
      omega)]
  · have hxb : x ∈ P.boundary (lowerPreimage hc.monotone (.Iic y)) n α := by
      rw [← hb, mem_lowerPreimage]
      exact subset_lowerClosure h
    exact mem_facesIn_of_mem_boundary hxb hx

variable [Fintype P] [DecidableLE P] [Fintype Q] [DecidableLE Q]

theorem IsComap.chainDiff_comp_comapChainHom {c : P → Q} (hc : IsComap c) (n : ℕ) :
    P.chainDiff n ∘ₗ comapChainHom c (n + 1) = comapChainHom c n ∘ₗ Q.chainDiff n := by
  classical
  refine LinearMap.pi_ext' fun y => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, LinearMap.coe_single]
  have hdim : krullDim (lowerPreimage hc.monotone (.Iic y.1)) = (n + 1 : ℕ) := by
    rw [hc.krullDim_lowerPreimage_Iic, LowerSet.krullDim_Iic, y.2]
  rw [hc.comapChainHom_single, chainDiff_indicatorChain (hc.isMoleculeIn_Iic y.1) hdim,
    chainDiff_single]
  funext w
  rw [Pi.sub_apply, indicatorChain_apply, indicatorChain_apply,
    if_congr (hc.mem_facesIn_lowerPreimage_Iic y.2 w.2) rfl rfl,
    if_congr (hc.mem_facesIn_lowerPreimage_Iic y.2 w.2) rfl rfl, comapChainHom_apply]
  by_cases h : grade ℕ (c w.1) = n
  · rw [dif_pos h, incidence_eq_sub]
  · have hno (α : Bool) : c w.1 ∉ Q.faces α y.1 := fun hf => h (by
      have := Nat.covBy_iff_add_one_eq.1 (hf.1.grade ℕ)
      rw [y.2] at this
      omega)
    rw [dif_neg h, if_neg (hno true), if_neg (hno false), sub_zero]

omit [DecidableLE P] [DecidableLE Q] in
theorem IsComap.chainAugmentation_comp_comapChainHom {c : P → Q} (hc : IsComap c) :
    P.chainAugmentation ∘ₗ comapChainHom c 0 = Q.chainAugmentation := by
  classical
  refine LinearMap.pi_ext' fun y => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, LinearMap.coe_single]
  rw [hc.comapChainHom_single, chainAugmentation_apply, chainAugmentation_apply,
    Fintype.sum_eq_single y fun y' hy' => Pi.single_eq_of_ne hy' _, Pi.single_eq_same]
  have hdim : krullDim (lowerPreimage hc.monotone (.Iic y.1)) = 0 := by
    rw [hc.krullDim_lowerPreimage_Iic, LowerSet.krullDim_Iic, y.2]
    rfl
  obtain ⟨p, hp, hU⟩ := (hc.isMoleculeIn_Iic y.1).exists_eq_Iic_of_krullDim_eq_zero hdim
  have hmem (x : P) : x ∈ (lowerPreimage hc.monotone (.Iic y.1) : Set P) ↔ x = p := by
    rw [SetLike.mem_coe, hU, LowerSet.mem_Iic_iff]
    exact ⟨fun h => hp.eq_of_le h, fun h => h ▸ le_rfl⟩
  have hp0 : grade ℕ p = 0 := grade_eq_zero_iff.2 hp
  rw [Fintype.sum_eq_single ⟨p, hp0⟩ fun x hx => by
    rw [indicatorChain_apply]
    exact if_neg fun h => hx (Subtype.ext ((hmem x.1).1 h))]
  rw [indicatorChain_apply]
  exact if_pos ((hmem p).2 rfl)

omit [Fintype P] [DecidableLE P] in
theorem comapChainHom_id (n : ℕ) : comapChainHom (id : P → P) n = LinearMap.id :=
  LinearMap.ext fun _ => funext fun x => dif_pos x.2

omit [Fintype P] [DecidableLE P] [Fintype Q] [DecidableLE Q] in
theorem IsComap.comapChainHom_comp {c : P → Q} {d : Q → R} (hc : IsComap c) (hd : IsComap d)
    (n : ℕ) : comapChainHom (d ∘ c) n = comapChainHom c n ∘ₗ comapChainHom d n := by
  refine LinearMap.ext fun g => funext fun x => ?_
  rw [LinearMap.comp_apply, comapChainHom_apply, comapChainHom_apply]
  by_cases h : grade ℕ (c x.1) = n
  · rw [dif_pos h]
    rfl
  · have h₁ := hc.grade_le x.1
    have h₂ := hd.grade_le (c x.1)
    rw [x.2] at h₁
    rw [dif_neg h, dif_neg fun h' => h (by rw [Function.comp_apply] at h'; omega)]

end Comaps

section Morphisms

variable [Fintype P] [DecidableLE P] [DecidableEq Q] [Fintype Q] [DecidableLE Q]

omit [DecidableLE P] [Fintype Q] [DecidableLE Q] in
variable (f : P → Q) in
def morphismChainHom (n : ℕ) : (P.gradeSet n → ℤ) →ₗ[ℤ] (Q.gradeSet n → ℤ) where
  toFun g y := ∑ x, g x * if f x.1 = y.1 then 1 else 0
  map_add' g g' := funext fun y => by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' a g := funext fun y => by
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum, RingHom.id_apply]

omit [DecidableLE P] [Fintype Q] [DecidableLE Q] in
theorem morphismChainHom_apply (f : P → Q) (n : ℕ) (g : P.gradeSet n → ℤ) (y : Q.gradeSet n) :
    morphismChainHom f n g y = ∑ x, g x * if f x.1 = y.1 then 1 else 0 :=
  rfl

omit [DecidableLE P] [Fintype Q] [DecidableLE Q] in
private theorem morphismChainHom_single [DecidableEq P] (f : P → Q) (n : ℕ) (x : P.gradeSet n) :
    morphismChainHom f n (Pi.single x 1) = fun y => if f x.1 = y.1 then 1 else 0 := by
  funext y
  rw [morphismChainHom_apply, Fintype.sum_eq_single x fun x' hx' => by
    rw [Pi.single_eq_of_ne hx', zero_mul], Pi.single_eq_same, one_mul]

private theorem IsMorphism.sum_faces_fibre {f : P → Q} (hf : IsMorphism f) (α : Bool) (x : P)
    (w : Q) : (∑ v : P, if v ∈ P.faces α x ∧ f v = w then (1 : ℤ) else 0) =
      if w ∈ Q.faces α (f x) then 1 else 0 := by
  by_cases hw : w ∈ Q.faces α (f x)
  · obtain ⟨v, hv, rfl⟩ := (hf.bijOn_faces x α).surjOn hw
    rw [if_pos hw, Fintype.sum_eq_single v fun v' hv' => if_neg fun h =>
      hv' ((hf.bijOn_faces x α).injOn h.1 hv h.2), if_pos ⟨hv, rfl⟩]
  · rw [if_neg hw]
    exact Finset.sum_eq_zero fun v _ => if_neg fun ⟨h₁, h₂⟩ =>
      hw (h₂ ▸ (hf.bijOn_faces x α).mapsTo h₁)

theorem IsMorphism.chainDiff_comp_morphismChainHom {f : P → Q} (hf : IsMorphism f) (n : ℕ) :
    Q.chainDiff n ∘ₗ morphismChainHom f (n + 1) = morphismChainHom f n ∘ₗ P.chainDiff n := by
  classical
  refine LinearMap.pi_ext' fun x => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, LinearMap.coe_single]
  rw [morphismChainHom_single, chainDiff_single]
  funext w
  have hx : grade ℕ (f x.1) = n + 1 := by rw [hf.grade_eq, x.2]
  rw [chainDiff_apply, Fintype.sum_eq_single ⟨f x.1, hx⟩ fun y hy => by
    rw [if_neg fun h => hy (Subtype.ext h.symm), zero_mul], if_pos rfl, one_mul,
    morphismChainHom_apply, sum_gradeSet n (fun v => incidence x.1 v * if f v = w.1 then 1 else 0)
      fun v h => by
        have := Nat.covBy_iff_add_one_eq.1 ((covBy_of_incidence_ne_zero
          (left_ne_zero_of_mul h)).grade ℕ)
        rw [x.2] at this
        omega]
  simp only [incidence_eq_sub, sub_mul, ite_zero_mul_ite_zero, one_mul, Finset.sum_sub_distrib,
    hf.sum_faces_fibre]

omit [DecidableLE P] [DecidableLE Q] in
theorem IsMorphism.chainAugmentation_comp_morphismChainHom {f : P → Q} (hf : IsMorphism f) :
    Q.chainAugmentation ∘ₗ morphismChainHom f 0 = P.chainAugmentation := by
  classical
  refine LinearMap.pi_ext' fun x => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, LinearMap.coe_single]
  have hx : grade ℕ (f x.1) = 0 := by rw [hf.grade_eq, x.2]
  rw [morphismChainHom_single, chainAugmentation_apply, chainAugmentation_apply,
    Fintype.sum_eq_single ⟨f x.1, hx⟩ fun y hy => if_neg fun h => hy (Subtype.ext h.symm),
    if_pos rfl, Fintype.sum_eq_single x fun y hy => Pi.single_eq_of_ne hy _, Pi.single_eq_same]

omit [DecidableLE P] [DecidableLE Q] in
theorem comapChainHom_iso {P Q : OGP.{u}} [Fintype Q] [DecidableEq P] (e : P ≅ Q) (n : ℕ) :
    comapChainHom (⇑e.hom) n = morphismChainHom (⇑e.inv) n := by
  refine LinearMap.ext fun g => funext fun x => ?_
  rw [comapChainHom_apply, morphismChainHom_apply]
  have hx : grade ℕ (e.hom x.1) = n := by rw [(isMorphism e.hom).grade_eq, x.2]
  rw [dif_pos hx, Fintype.sum_eq_single ⟨e.hom x.1, hx⟩ fun y hy => by
    rw [if_neg fun h => hy (Subtype.ext ((Iso.inv_hom_id_apply e y.1).symm.trans
      (congrArg (⇑e.hom) h))), mul_zero],
    if_pos (Iso.hom_inv_id_apply e x.1), mul_one]

end Morphisms

section ChainMaps

variable {P Q R : OGP.{u}} [Fintype P] [DecidableLE P] [Fintype Q] [DecidableLE Q] [Fintype R]
  [DecidableLE R]

def IsComap.chainMap {c : P → Q} (hc : IsComap c) (hP : P.IsOrientedThin)
    (hQ : Q.IsOrientedThin) : chainComplex hQ ⟶ chainComplex hP :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (comapChainHom c n)) fun n => by
    rw [chainComplex_d, chainComplex_d]
    exact ModuleCat.hom_ext (hc.chainDiff_comp_comapChainHom n)

theorem IsComap.chainMap_f {c : P → Q} (hc : IsComap c) (hP : P.IsOrientedThin)
    (hQ : Q.IsOrientedThin) (n : ℕ) :
    (hc.chainMap hP hQ).f n = ModuleCat.ofHom (comapChainHom c n) :=
  rfl

omit [Fintype R] [DecidableLE R] in
theorem chainMap_id (hR : P.IsRDC) :
    (IsComap.id hR).chainMap hR.isOrientedThin hR.isOrientedThin = 𝟙 _ :=
  HomologicalComplex.hom_ext _ _ fun n => ModuleCat.hom_ext (comapChainHom_id n)

theorem IsComap.chainMap_comp {c : P → Q} {d : Q → R} (hc : IsComap c) (hd : IsComap d)
    (hP : P.IsOrientedThin) (hQ : Q.IsOrientedThin) (hR : R.IsOrientedThin) :
    (hc.comp hd).chainMap hP hR = hd.chainMap hQ hR ≫ hc.chainMap hP hQ :=
  HomologicalComplex.hom_ext _ _ fun n => ModuleCat.hom_ext (hc.comapChainHom_comp hd n)

def IsMorphism.chainMap [DecidableEq Q] {f : P → Q} (hf : IsMorphism f) (hP : P.IsOrientedThin)
    (hQ : Q.IsOrientedThin) : chainComplex hP ⟶ chainComplex hQ :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (morphismChainHom f n)) fun n => by
    rw [chainComplex_d, chainComplex_d]
    exact ModuleCat.hom_ext (hf.chainDiff_comp_morphismChainHom n)

theorem IsMorphism.chainMap_f [DecidableEq Q] {f : P → Q} (hf : IsMorphism f)
    (hP : P.IsOrientedThin) (hQ : Q.IsOrientedThin) (n : ℕ) :
    (hf.chainMap hP hQ).f n = ModuleCat.ofHom (morphismChainHom f n) :=
  rfl

theorem chainMap_isComap_iso [DecidableEq P] (e : P ≅ Q) (hP : P.IsOrientedThin) (hQ : Q.IsRDC) :
    (isComap_iso e hQ).chainMap hP hQ.isOrientedThin =
      (isMorphism e.inv).chainMap hQ.isOrientedThin hP :=
  HomologicalComplex.hom_ext _ _ fun n => ModuleCat.hom_ext (comapChainHom_iso e n)

end ChainMaps

end Atoms.Molecule.OGP
