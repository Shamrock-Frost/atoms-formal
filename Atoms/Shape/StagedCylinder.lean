import Atoms.Molecule.Construction.GrayProductMolecule
import Atoms.Molecule.Pasting.Staged

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Order Set

universe u

namespace Atoms.Molecule.OGP

abbrev arrowCyl (Q : OGP.{u}) : OGP.{u} := grayProduct (globe.{u} 1) Q

variable {Q : OGP.{u}}

abbrev globeOneEnd (γ : Bool) : globe.{u} 1 := SuspCarrier.pole γ

abbrev arrowProd (A : LowerSet (globe.{u} 1)) (C : LowerSet Q) :
    LowerSet (arrowCyl Q) := A ×ˢ C

theorem mem_Iic_globeOneEnd {a : globe.{u} 1} {γ : Bool} :
    a ∈ LowerSet.Iic (globeOneEnd γ) ↔ a = globeOneEnd γ :=
  LowerSet.mem_Iic_iff.trans ⟨(SuspCarrier.isMin_pole γ).eq_of_le, fun h => h ▸ le_rfl⟩

theorem boundary_globe_one_univ_succ (n : ℕ) (δ : Bool) :
    (globe.{u} 1).boundary ⊤ (n + 1) δ = ⊤ :=
  boundary_eq_self (by
    rw [LowerSet.krullDim_top, krullDim_globe]
    exact_mod_cast Nat.le_add_left 1 n) δ

theorem dim_globe_one_eq_zero_of_ne {a : globe.{u} 1}
    (h : a ≠ ⊤) : grade ℕ a = 0 := by
  rcases a with b | ⟨⟨⟩⟩
  · exact SuspCarrier.grade_pole b
  · exact absurd rfl h

theorem dim_arrowCyl_apply (z : arrowCyl Q) :
    grade ℕ z = grade ℕ z.1 + grade ℕ z.2 := rfl

theorem isMoleculeIn_arrowProd_univ {C : LowerSet Q} (hC : IsMoleculeIn Q C) :
    IsMoleculeIn (arrowCyl Q) (arrowProd ⊤ C) :=
  isMoleculeIn_prod (isAtom_globe 1).1 hC

theorem isMoleculeIn_arrowProd_end {C : LowerSet Q} (hC : IsMoleculeIn Q C) (γ : Bool) :
    IsMoleculeIn (arrowCyl Q) (arrowProd (.Iic (globeOneEnd γ)) C) :=
  (isMoleculeIn_Iic_prod_iff (SuspCarrier.isMin_pole γ) C).2 hC

theorem krullDim_arrowProd_univ_le {C : LowerSet Q} {n : ℕ} (hC : krullDim C ≤ n) :
    krullDim (arrowProd ⊤ C) ≤ (n + 1 : ℕ) := by
  have h := krullDim_prod_le (P := globe.{u} 1) (Q := Q) (U := ⊤) (V := C)
    (by rw [LowerSet.krullDim_top, krullDim_globe]) hC
  rwa [Nat.add_comm] at h

theorem krullDim_arrowProd_end_le {C : LowerSet Q} {n : ℕ} (γ : Bool) (hC : krullDim C ≤ n) :
    krullDim (arrowProd (.Iic (globeOneEnd γ)) C) ≤ (n : ℕ) := by
  have h := krullDim_prod_le (P := globe.{u} 1) (Q := Q) (U := .Iic (globeOneEnd γ)) (V := C)
    (by rw [LowerSet.krullDim_Iic, SuspCarrier.grade_pole]) hC
  rwa [Nat.zero_add] at h

theorem arrowProd_union (A : LowerSet (globe.{u} 1)) (C C' : LowerSet Q) :
    arrowProd A (C ⊔ C') = arrowProd A C ⊔ arrowProd A C' :=
  LowerSet.prod_sup A C C'

theorem arrowProd_inter (A : LowerSet (globe.{u} 1)) (C C' : LowerSet Q) :
    arrowProd A (C ⊓ C') = arrowProd A C ⊓ arrowProd A C' :=
  LowerSet.prod_inf A C C'

theorem boundary_arrowProd_end (C : LowerSet Q) (γ : Bool) (n : ℕ) (δ : Bool) :
    (arrowCyl Q).boundary (arrowProd (.Iic (globeOneEnd γ)) C) n δ =
      arrowProd (.Iic (globeOneEnd γ)) (Q.boundary C n δ) :=
  boundary_Iic_prod (SuspCarrier.isMin_pole γ) C n δ

theorem boundary_arrowProd_univ_zero {C : LowerSet Q}
    (hg : Q.IsGlobular C) (δ : Bool) :
    (arrowCyl Q).boundary (arrowProd ⊤ C) 0 δ =
      arrowProd (.Iic (globeOneEnd δ)) (Q.boundary C 0 δ) := by
  have H := fun {a b} => mem_boundary_prod_of_isGlobular (n := 0) (α := δ) (x := a) (y := b)
    (isAtom_globe 1).1.isGlobular hg
  refine le_antisymm ?_ ?_
  · rintro ⟨a, b⟩ h
    obtain ⟨k, hk, ha, hb⟩ := H.1 h
    obtain rfl : k = 0 := by omega
    rw [boundary_zero_globe_one] at ha
    exact ⟨ha, by simpa using hb⟩
  · rintro ⟨a, b⟩ ⟨ha, hb⟩
    exact H.2 ⟨0, le_rfl, by rw [boundary_zero_globe_one]; exact ha, by simpa using hb⟩

theorem boundary_arrowProd_univ_succ {C : LowerSet Q}
    (hg : Q.IsGlobular C) (n : ℕ) (δ : Bool) :
    (arrowCyl Q).boundary (arrowProd ⊤ C) (n + 1) δ =
      arrowProd (.Iic (globeOneEnd δ)) (Q.boundary C (n + 1) δ) ⊔
        arrowProd ⊤ (Q.boundary C n (!δ)) := by
  have H := fun {a b} => mem_boundary_prod_of_isGlobular (n := n + 1) (α := δ) (x := a)
    (y := b) (isAtom_globe 1).1.isGlobular hg
  refine le_antisymm ?_ ?_
  · rintro ⟨a, b⟩ h
    obtain ⟨k, hk, ha, hb⟩ := H.1 h
    rcases k with _ | k
    · rw [boundary_zero_globe_one] at ha
      exact Or.inl ⟨ha, by simpa using hb⟩
    · refine Or.inr ⟨LowerSet.mem_top, ?_⟩
      rcases k with _ | k
      · simpa using hb
      · exact hg.boundary_le_boundary (by omega) _ _ hb
  · rintro ⟨a, b⟩ (⟨ha, hb⟩ | ⟨-, hb⟩)
    · exact H.2 ⟨0, Nat.zero_le _, by rw [boundary_zero_globe_one]; exact ha,
        by simpa using hb⟩
    · refine H.2 ⟨1, by omega, by rw [boundary_globe_one_univ_succ]; exact LowerSet.mem_top,
        ?_⟩
      simpa using hb

def copyWhiskerRest (γ : Bool) (C : LowerSet Q) : ℕ → LowerSet (arrowCyl Q)
  | 0 => ⊥
  | l + 1 => arrowProd ⊤ (Q.boundary C l (!γ))

def copyWhisker (γ : Bool) (C : LowerSet Q) (l : ℕ) : LowerSet (arrowCyl Q) :=
  arrowProd (.Iic (globeOneEnd γ)) C ⊔ copyWhiskerRest γ C l

@[simp] theorem copyWhiskerRest_zero (γ : Bool) (C : LowerSet Q) :
    copyWhiskerRest γ C 0 = (⊥ : LowerSet (arrowCyl Q)) := rfl

theorem copyWhiskerRest_succ (γ : Bool) (C : LowerSet Q) (l : ℕ) :
    copyWhiskerRest γ C (l + 1) = arrowProd ⊤ (Q.boundary C l (!γ)) := rfl

theorem copyWhiskerRest_subset {γ : Bool} {C : LowerSet Q} (hC : IsMoleculeIn Q C)
    (l : ℕ) : copyWhiskerRest γ C l ≤ arrowProd ⊤ (Q.boundary C l (!γ)) := by
  rcases l with _ | l
  · exact bot_le
  · exact LowerSet.prod_mono_right (hC.isGlobular.boundary_le_boundary (Nat.lt_succ_self l) _ _)

theorem copyWhiskerRest_subset_arrowProd_univ (γ : Bool) (C : LowerSet Q) (l : ℕ) :
    copyWhiskerRest γ C l ≤ arrowProd ⊤ C := by
  rcases l with _ | l
  · exact bot_le
  · exact LowerSet.prod_mono_right (boundary_le C _ _)

theorem krullDim_copyWhiskerRest_le (γ : Bool) (C : LowerSet Q) (l : ℕ) :
    krullDim (copyWhiskerRest γ C l) ≤ (l : ℕ) := by
  rcases l with _ | l
  · exact krullDim_le_coe_iff.2 fun x => x.2.elim
  · exact krullDim_arrowProd_univ_le (krullDim_boundary_le C l (!γ))

theorem copyWhiskerRest_congr {δ : Bool} {C C' : LowerSet Q} {j : ℕ}
    (h : ∀ j', j' < j → Q.boundary C j' (!δ) = Q.boundary C' j' (!δ)) :
    copyWhiskerRest δ C j = copyWhiskerRest δ C' j := by
  rcases j with _ | j
  · rfl
  · rw [copyWhiskerRest_succ, copyWhiskerRest_succ, h j (Nat.lt_succ_self j)]

theorem boundary_arrowProd_univ {C : LowerSet Q} (hg : Q.IsGlobular C)
    (j : ℕ) (δ : Bool) :
    (arrowCyl Q).boundary (arrowProd ⊤ C) j δ =
      arrowProd (.Iic (globeOneEnd δ)) (Q.boundary C j δ) ⊔ copyWhiskerRest δ C j := by
  rcases j with _ | j
  · rw [boundary_arrowProd_univ_zero hg, copyWhiskerRest_zero, sup_bot_eq]
  · rw [boundary_arrowProd_univ_succ hg, copyWhiskerRest_succ]

theorem copyWhisker_subset_arrowProd_univ (γ : Bool) (C : LowerSet Q) (l : ℕ) :
    copyWhisker γ C l ≤ arrowProd ⊤ C :=
  sup_le (LowerSet.prod_mono_left le_top) (copyWhiskerRest_subset_arrowProd_univ γ C l)

theorem krullDim_copyWhisker_le {γ : Bool} {C : LowerSet Q} {n : ℕ} (hC : krullDim C ≤ n)
    (l : ℕ) : krullDim (copyWhisker γ C l) ≤ (max n l : ℕ) := by
  unfold copyWhisker
  rw [LowerSet.krullDim_sup]
  exact sup_le ((krullDim_arrowProd_end_le γ hC).trans (by exact_mod_cast le_max_left n l))
    ((krullDim_copyWhiskerRest_le γ C l).trans (by exact_mod_cast le_max_right n l))

theorem copyWhisker_zero (γ : Bool) (C : LowerSet Q) :
    copyWhisker γ C 0 = arrowProd (.Iic (globeOneEnd γ)) C := by
  rw [copyWhisker, copyWhiskerRest_zero, sup_bot_eq]

theorem copyWhisker_succ (γ : Bool) {C : LowerSet Q} (hC : IsMoleculeIn Q C) (l : ℕ) :
    copyWhisker γ C (l + 1) =
      copyWhisker γ C l ⊔ arrowProd ⊤ (Q.boundary C l (!γ)) := by
  unfold copyWhisker
  rw [copyWhiskerRest_succ, sup_assoc,
    sup_eq_right.2 (copyWhiskerRest_subset hC l)]

theorem copyWhisker_inter_arrowProd {γ : Bool} {C : LowerSet Q} (hC : IsMoleculeIn Q C)
    (l : ℕ) : copyWhisker γ C l ⊓ arrowProd ⊤ (Q.boundary C l (!γ)) =
      arrowProd (.Iic (globeOneEnd γ)) (Q.boundary C l (!γ)) ⊔ copyWhiskerRest γ C l := by
  rw [copyWhisker, inf_sup_right, LowerSet.prod_inf_prod, inf_top_eq,
    inf_eq_right.2 (boundary_le C _ _), inf_eq_left.2 (copyWhiskerRest_subset hC l)]

theorem boundary_arrowProd_univ_boundary {γ : Bool} {C : LowerSet Q}
    (hC : IsMoleculeIn Q C) (l : ℕ) :
    (arrowCyl Q).boundary (arrowProd ⊤ (Q.boundary C l (!γ))) l γ =
      arrowProd (.Iic (globeOneEnd γ)) (Q.boundary C l (!γ)) ⊔ copyWhiskerRest γ C l := by
  have hb := hC.boundary l (!γ)
  rw [boundary_arrowProd_univ hb.isGlobular,
    boundary_eq_self (krullDim_boundary_le C l (!γ)) γ]
  refine congrArg _ (copyWhiskerRest_congr fun j' hj' => ?_)
  exact hC.isGlobular j' l hj' _ _

theorem isPastingIn_copyWhisker_succ_of {γ : Bool} {C : LowerSet Q}
    (hC : IsMoleculeIn Q C) {l : ℕ}
    (hin : (arrowCyl Q).boundary (copyWhisker γ C l) l (!γ) =
      arrowProd (.Iic (globeOneEnd γ)) (Q.boundary C l (!γ)) ⊔ copyWhiskerRest γ C l) :
    (arrowCyl Q).IsPastingIn l
      (cond (!γ) (copyWhisker γ C l) (arrowProd ⊤ (Q.boundary C l (!γ))))
      (cond (!γ) (arrowProd ⊤ (Q.boundary C l (!γ))) (copyWhisker γ C l))
      (copyWhisker γ C (l + 1)) := by
  refine (isPastingIn_cond_iff (!γ)).2 ⟨(copyWhisker_succ γ hC l).symm, ?_, ?_⟩
  · rw [copyWhisker_inter_arrowProd hC, Bool.not_not, boundary_arrowProd_univ_boundary hC l]
  · rw [copyWhisker_inter_arrowProd hC, hin]

theorem copyWhisker_spec (γ : Bool) {C : LowerSet Q} (hC : IsMoleculeIn Q C) :
    ∀ l, IsMoleculeIn (arrowCyl Q) (copyWhisker γ C l) ∧
      ∀ n, l ≤ n → ∀ δ, (arrowCyl Q).boundary (copyWhisker γ C l) n δ =
        arrowProd (.Iic (globeOneEnd γ)) (Q.boundary C n δ) ⊔ copyWhiskerRest γ C l := by
  intro l
  induction l with
  | zero =>
    refine ⟨copyWhisker_zero γ C ▸ isMoleculeIn_arrowProd_end hC γ, fun n _ δ => ?_⟩
    rw [copyWhisker_zero, copyWhiskerRest_zero, sup_bot_eq]
    exact boundary_arrowProd_end C γ n δ
  | succ l ih =>
    obtain ⟨hm, hbd⟩ := ih
    have hE := isMoleculeIn_arrowProd_univ (hC.boundary l (!γ))
    have hp := isPastingIn_copyWhisker_succ_of hC (hbd l le_rfl (!γ))
    have hmol : IsMoleculeIn (arrowCyl Q) (copyWhisker γ C (l + 1)) :=
      hp.isMoleculeIn (Bool.cond_rec_prop _ hm hE) (Bool.cond_rec_prop _ hE hm)
    refine ⟨hmol, fun n hn δ => ?_⟩
    have hEd : krullDim (arrowProd ⊤ (Q.boundary C l (!γ))) ≤ (n : ℕ) :=
      (krullDim_arrowProd_univ_le (krullDim_boundary_le C l (!γ))).trans (by exact_mod_cast hn)
    have hEn : (arrowCyl Q).boundary (arrowProd ⊤ (Q.boundary C l (!γ))) n δ =
        arrowProd ⊤ (Q.boundary C l (!γ)) := boundary_eq_self hEd δ
    have hU : (arrowCyl Q).boundary (copyWhisker γ C (l + 1)) n δ =
        (arrowCyl Q).boundary (copyWhisker γ C l) n δ ⊔
          (arrowCyl Q).boundary (arrowProd ⊤ (Q.boundary C l (!γ))) n δ :=
      hp.boundary_eq_sup_of_lt_cond _ hm.isGlobular hE.isGlobular (by omega) δ
    rw [hU, hEn, hbd n (by omega) δ, copyWhiskerRest_succ, sup_assoc,
      sup_eq_right.2 (copyWhiskerRest_subset hC l)]

theorem isPastingIn_copyWhisker_succ (γ : Bool) {C : LowerSet Q} (hC : IsMoleculeIn Q C)
    (l : ℕ) :
    (arrowCyl Q).IsPastingIn l
      (cond (!γ) (copyWhisker γ C l) (arrowProd ⊤ (Q.boundary C l (!γ))))
      (cond (!γ) (arrowProd ⊤ (Q.boundary C l (!γ))) (copyWhisker γ C l))
      (copyWhisker γ C (l + 1)) :=
  isPastingIn_copyWhisker_succ_of hC ((copyWhisker_spec γ hC l).2 l le_rfl (!γ))

theorem boundary_arrowProd_univ_top {V : LowerSet Q} (hV : IsMoleculeIn Q V) {d : ℕ}
    (hd : krullDim V ≤ d) (β : Bool) :
    (arrowCyl Q).boundary (arrowProd ⊤ V) d β = copyWhisker β V d := by
  rw [boundary_arrowProd_univ hV.isGlobular, boundary_eq_self hd]
  rfl

section Step

variable {γ : Bool} {j : ℕ} {M Pc : LowerSet Q}

theorem inter_eq_boundary_piece (hp : Q.IsPastingIn j (cond γ M Pc) (cond γ Pc M) (M ⊔ Pc)) :
    M ⊓ Pc = Q.boundary Pc j (!γ) :=
  ((isPastingIn_cond_iff γ).1 hp).2.1

theorem inter_eq_boundary_stage (hp : Q.IsPastingIn j (cond γ M Pc) (cond γ Pc M) (M ⊔ Pc)) :
    M ⊓ Pc = Q.boundary M j γ :=
  ((isPastingIn_cond_iff γ).1 hp).2.2

variable (hM : IsMoleculeIn Q M) (hPc : IsMoleculeIn Q Pc)
  (hp : Q.IsPastingIn j (cond γ M Pc) (cond γ Pc M) (M ⊔ Pc))
include hM hPc hp

theorem boundary_stage_eq_boundary_piece {j' : ℕ} (hj : j' < j) (δ : Bool) :
    Q.boundary M j' δ = Q.boundary Pc j' δ :=
  hp.boundary_eq_boundary_of_lt_cond γ hM.isGlobular hPc.isGlobular hj δ

theorem isPastingIn_arrowProd_copyWhisker :
    (arrowCyl Q).IsPastingIn j (cond γ (arrowProd ⊤ M) (copyWhisker γ Pc j))
      (cond γ (copyWhisker γ Pc j) (arrowProd ⊤ M))
      (arrowProd ⊤ M ⊔ copyWhisker γ Pc j) := by
  have hW := copyWhisker_spec γ hPc j
  have hrest : copyWhiskerRest γ M j = copyWhiskerRest γ Pc j :=
    copyWhiskerRest_congr fun j' hj' => boundary_stage_eq_boundary_piece hM hPc hp hj' _
  have hsub : copyWhiskerRest γ Pc j ≤ arrowProd ⊤ M := by
    rw [← hrest]; exact copyWhiskerRest_subset_arrowProd_univ γ M j
  have hint : arrowProd ⊤ M ⊓ copyWhisker γ Pc j =
      arrowProd (.Iic (globeOneEnd γ)) (Q.boundary Pc j (!γ)) ⊔ copyWhiskerRest γ Pc j := by
    rw [copyWhisker, inf_sup_left, LowerSet.prod_inf_prod, top_inf_eq, inter_eq_boundary_piece hp,
      inf_eq_right.2 hsub]
  refine (isPastingIn_cond_iff γ).2 ⟨rfl, ?_, ?_⟩
  · rw [hint, hW.2 j le_rfl (!γ)]
  · rw [hint, boundary_arrowProd_univ hM.isGlobular j γ, hrest,
      ← inter_eq_boundary_stage hp, inter_eq_boundary_piece hp]

theorem isPastingIn_copyWhisker_arrowProd :
    (arrowCyl Q).IsPastingIn j
      (cond γ (copyWhisker (!γ) (Q.boundary M (j + 1) (!γ)) j) (arrowProd ⊤ Pc))
      (cond γ (arrowProd ⊤ Pc) (copyWhisker (!γ) (Q.boundary M (j + 1) (!γ)) j))
      (copyWhisker (!γ) (Q.boundary M (j + 1) (!γ)) j ⊔ arrowProd ⊤ Pc) := by
  have hC := hM.boundary (j + 1) (!γ)
  have hW := copyWhisker_spec (!γ) hC j
  have hCb : Q.boundary (Q.boundary M (j + 1) (!γ)) j γ = Q.boundary Pc j (!γ) := by
    rw [hM.isGlobular j (j + 1) (Nat.lt_succ_self j),
      ← inter_eq_boundary_stage hp, inter_eq_boundary_piece hp]
  have hrest : copyWhiskerRest (!γ) (Q.boundary M (j + 1) (!γ)) j =
      copyWhiskerRest (!γ) Pc j := by
    refine copyWhiskerRest_congr fun j' hj' => ?_
    rw [hM.isGlobular j' (j + 1) (by omega)]
    exact boundary_stage_eq_boundary_piece hM hPc hp hj' _
  have hCP : Q.boundary M (j + 1) (!γ) ⊓ Pc = Q.boundary Pc j (!γ) := by
    rw [← inter_eq_boundary_piece hp]
    refine le_antisymm (inf_le_inf_right _ (boundary_le M _ _)) (le_inf ?_ inf_le_right)
    rw [inter_eq_boundary_stage hp]
    exact hM.isGlobular.boundary_le_boundary (Nat.lt_succ_self j) _ _
  have hint : copyWhisker (!γ) (Q.boundary M (j + 1) (!γ)) j ⊓ arrowProd ⊤ Pc =
      arrowProd (.Iic (globeOneEnd (!γ))) (Q.boundary Pc j (!γ)) ⊔ copyWhiskerRest (!γ) Pc j := by
    rw [copyWhisker, hrest, inf_sup_right, LowerSet.prod_inf_prod, inf_top_eq, hCP,
      inf_eq_left.2 (copyWhiskerRest_subset_arrowProd_univ (!γ) Pc j)]
  refine (isPastingIn_cond_iff γ).2 ⟨rfl, ?_, ?_⟩
  · rw [hint, boundary_arrowProd_univ hPc.isGlobular j (!γ)]
  · rw [hint, hW.2 j le_rfl γ, hCb, hrest]

theorem isPastingIn_arrowProd_union (hd : krullDim Pc ≤ (j + 1 : ℕ)) :
    (arrowCyl Q).IsPastingIn (j + 1)
      (cond (!γ) (arrowProd ⊤ M ⊔ copyWhisker γ Pc j)
        (copyWhisker (!γ) (Q.boundary M (j + 1) (!γ)) j ⊔ arrowProd ⊤ Pc))
      (cond (!γ) (copyWhisker (!γ) (Q.boundary M (j + 1) (!γ)) j ⊔ arrowProd ⊤ Pc)
        (arrowProd ⊤ M ⊔ copyWhisker γ Pc j))
      (arrowProd ⊤ (M ⊔ Pc)) := by
  set C₂ := Q.boundary M (j + 1) (!γ) with hC₂
  have hC := hM.boundary (j + 1) (!γ)
  have hW := copyWhisker_spec γ hPc j
  have hW₂ := copyWhisker_spec (!γ) hC j
  have hcM := isMoleculeIn_arrowProd_univ (Q := Q) hM
  have hcP := isMoleculeIn_arrowProd_univ (Q := Q) hPc
  have p1 := isPastingIn_arrowProd_copyWhisker hM hPc hp
  have p2 := isPastingIn_copyWhisker_arrowProd hM hPc hp
  have bS₁ : (arrowCyl Q).boundary (arrowProd ⊤ M ⊔ copyWhisker γ Pc j) (j + 1) (!γ)
      = (arrowCyl Q).boundary (arrowProd ⊤ M) (j + 1) (!γ) ⊔
        (arrowCyl Q).boundary (copyWhisker γ Pc j) (j + 1) (!γ) :=
    p1.boundary_eq_sup_of_lt_cond γ hcM.isGlobular hW.1.isGlobular (Nat.lt_succ_self j) _
  have bD₂ : (arrowCyl Q).boundary (copyWhisker (!γ) C₂ j ⊔ arrowProd ⊤ Pc) (j + 1) γ
      = (arrowCyl Q).boundary (copyWhisker (!γ) C₂ j) (j + 1) γ ⊔
        (arrowCyl Q).boundary (arrowProd ⊤ Pc) (j + 1) γ :=
    p2.boundary_eq_sup_of_lt_cond γ hW₂.1.isGlobular hcP.isGlobular (Nat.lt_succ_self j) _
  have ePc : Q.boundary Pc (j + 1) (!γ) = Pc := boundary_eq_self hd _
  have ePc' : Q.boundary Pc (j + 1) γ = Pc := boundary_eq_self hd _
  have eC₂ : Q.boundary C₂ (j + 1) γ = C₂ := boundary_eq_self (krullDim_boundary_le _ _ _) _
  have hMP : Q.boundary M j γ = Q.boundary Pc j (!γ) := by
    rw [← inter_eq_boundary_stage hp, inter_eq_boundary_piece hp]
  have hr1 : copyWhiskerRest γ Pc j ≤ arrowProd ⊤ (Q.boundary Pc j (!γ)) :=
    copyWhiskerRest_subset hPc j
  have hr2 : copyWhiskerRest (!γ) C₂ j ≤ arrowProd ⊤ (Q.boundary Pc j (!γ)) := by
    rcases j with _ | j
    · exact bot_le
    · rw [copyWhiskerRest_succ, hC₂,
        hM.isGlobular j (j + 1 + 1) (by omega),
        boundary_stage_eq_boundary_piece hM hPc hp (Nat.lt_succ_self j)]
      exact LowerSet.prod_mono_right (hPc.isGlobular.boundary_le_boundary
        (Nat.lt_succ_self j) _ _)
  have hC₂M : C₂ ≤ M := boundary_le M _ _
  have hw : copyWhisker γ Pc j ≤ arrowProd ⊤ Pc :=
    copyWhisker_subset_arrowProd_univ γ Pc j
  have hw₂ : copyWhisker (!γ) C₂ j ≤ arrowProd ⊤ M :=
    (copyWhisker_subset_arrowProd_univ (!γ) C₂ j).trans (LowerSet.prod_mono_right hC₂M)
  have hcap : arrowProd ⊤ M ⊓ arrowProd ⊤ Pc =
      arrowProd ⊤ (Q.boundary Pc j (!γ)) := by
    rw [← arrowProd_inter, inter_eq_boundary_piece hp]
  set T := arrowProd (.Iic (globeOneEnd (!γ))) C₂ ⊔ arrowProd (.Iic (globeOneEnd γ)) Pc ⊔
    arrowProd ⊤ (Q.boundary Pc j (!γ)) with hT
  have v1 : (arrowCyl Q).boundary (arrowProd ⊤ M ⊔ copyWhisker γ Pc j) (j + 1) (!γ)
      = T := by
    rw [bS₁, boundary_arrowProd_univ hM.isGlobular, hW.2 (j + 1) (by omega), ePc,
      copyWhiskerRest_succ, Bool.not_not, hMP, ← sup_assoc,
      sup_eq_left.2 (hr1.trans (le_sup_right.trans le_sup_left)), sup_right_comm]
  have v2 : (arrowCyl Q).boundary (copyWhisker (!γ) C₂ j ⊔ arrowProd ⊤ Pc) (j + 1) γ
      = T := by
    rw [bD₂, hW₂.2 (j + 1) (by omega), eC₂, boundary_arrowProd_univ hPc.isGlobular, ePc',
      copyWhiskerRest_succ, sup_sup_sup_comm, sup_eq_right.2 hr2]
  have v3 : (arrowProd ⊤ M ⊔ copyWhisker γ Pc j) ⊓
      (copyWhisker (!γ) C₂ j ⊔ arrowProd ⊤ Pc) = T := by
    rw [inf_sup_left, inf_eq_right.2 (hw₂.trans le_sup_left), inf_sup_right, hcap,
      inf_eq_left.2 hw, copyWhisker, copyWhisker, sup_comm (arrowProd ⊤ _),
      sup_assoc (arrowProd _ Pc), sup_eq_right.2 hr1, sup_sup_sup_comm, sup_eq_right.2 hr2]
  refine (isPastingIn_cond_iff (!γ)).2 ⟨?_, ?_, ?_⟩
  · rw [arrowProd_union, sup_sup_sup_comm, sup_eq_left.2 hw₂, sup_eq_right.2 hw]
  · rw [v3, Bool.not_not, v2]
  · rw [v3, v1]

end Step

section Tops

variable {P : OGP.{u}}

def StagedTops (m : ℕ) (L R : ℕ → LowerSet P) (T : P → Prop) : Prop :=
  ∀ i < m, ∀ y ∈ L (i + 1) ⊔ R (i + 1), grade ℕ y = i + 1 → T y

theorem StagedTops.of_succ {m : ℕ} {L R : ℕ → LowerSet P} {T : P → Prop}
    (h : StagedTops (m + 1) L R T) : StagedTops m L R T :=
  fun i hi => h i (by omega)

theorem StagedTops.extend {m : ℕ} {L R : ℕ → LowerSet P} {T : P → Prop}
    (h : StagedTops m L R T) {l r : LowerSet P}
    (hl : ∀ y ∈ l, grade ℕ y = m + 1 → T y) (hr : ∀ y ∈ r, grade ℕ y = m + 1 → T y) :
    StagedTops (m + 1) (fun i => if i = m + 1 then l else L i)
      (fun i => if i = m + 1 then r else R i) T := by
  intro i hi y hy hyd
  by_cases e : i = m
  · subst e
    simp only [if_true] at hy
    rcases hy with hy | hy
    · exact hl y hy hyd
    · exact hr y hy hyd
  · have e' : i + 1 ≠ m + 1 := by omega
    simp only [e', if_false] at hy
    exact h i (by omega) y hy hyd

theorem StagedTops.toDual {m : ℕ} {L R : ℕ → LowerSet P} {T : P → Prop}
    (h : StagedTops (P := P) m L R T) : StagedTops (P := OGP.dual P ⊤) m R L T :=
  fun i hi y hy hyd => h i hi y hy.symm hyd

theorem StagedTops.ofDual {m : ℕ} {L R : ℕ → LowerSet P} {T : P → Prop}
    (h : StagedTops (P := OGP.dual P ⊤) m L R T) : StagedTops (P := P) m R L T :=
  fun i hi y hy hyd => h i hi y hy.symm hyd

private theorem exists_isStagedPasting_tops_right (T : P → Prop) :
    ∀ (m : ℕ) {X D N : LowerSet P} {j : ℕ} {L R M : ℕ → LowerSet P},
      P.IsStagedPasting m X L R M → StagedTops m L R T → IsMoleculeIn P D → krullDim D ≤ m →
        j < m → P.IsPastingIn j (M m) D N →
        (∀ l, j < l → l ≤ m → ∀ y ∈ P.boundary D l false, grade ℕ y = l → T y) →
          ∃ L' R' M' : ℕ → LowerSet P, P.IsStagedPasting m X L' R' M' ∧ M' m = N ∧
            StagedTops m L' R' T := by
  intro m
  induction m with
  | zero => intro _ _ _ j _ _ _ _ _ _ _ hj; omega
  | succ m ih =>
    intro X D N j L R M hs ht hD hDd hj hp hT
    obtain ⟨h1, h2⟩ := hs.stage_succ m (Nat.lt_succ_self m)
    obtain ⟨hL, dL⟩ := hs.isMoleculeIn_left m (Nat.lt_succ_self m)
    obtain ⟨hR, dR⟩ := hs.isMoleculeIn_right m (Nat.lt_succ_self m)
    have hMm := hs.isMoleculeIn_stage m (by omega)
    have hLM := h1.isMoleculeIn hL hMm
    have hDtop : ∀ y ∈ D, grade ℕ y = m + 1 → T y := fun y hy hyd =>
      hT (m + 1) (by omega) le_rfl y (by rw [boundary_eq_self hDd]; exact hy) hyd
    have htL : ∀ y ∈ L (m + 1), grade ℕ y = m + 1 → T y := fun y hy hyd =>
      ht m (Nat.lt_succ_self m) y (Or.inl hy) hyd
    have htR : ∀ y ∈ R (m + 1), grade ℕ y = m + 1 → T y := fun y hy hyd =>
      ht m (Nat.lt_succ_self m) y (Or.inr hy) hyd
    rcases eq_or_lt_of_le (Nat.le_of_lt_succ hj) with rfl | hjm
    · refine ⟨_, _, _, hs.of_succ.extend h1 (h2.assoc hp) hL dL
        ((h2.isPastingIn_right_sup hp).isMoleculeIn hR hD) ?_, by simp,
        ht.of_succ.extend htL ?_⟩
      · rw [LowerSet.krullDim_sup]
        exact sup_le dR hDd
      · rintro y (hy | hy) hyd
        · exact htR y hy hyd
        · exact hDtop y hy hyd
    · set D' := P.boundary D m false with hD'def
      have hD' : IsMoleculeIn P D' := hD.boundary m false
      have hD'le : krullDim D' ≤ m := krullDim_boundary_le D m false
      have hD'B : P.IsPastingIn m D' D D := isPastingIn_boundary_false_self D m
      have hDD : P.IsPastingIn m D' D' D' := by
        have := isPastingIn_boundary_false_self D' m
        rwa [boundary_eq_self hD'le] at this
      have hN := isPastingIn_interchange hjm hLM.isGlobular hR.isGlobular hD'.isGlobular
        hD.isGlobular h2 hD'B hp
      have hk1 := isPastingIn_interchange_left hjm hLM.isGlobular hR.isGlobular hD'.isGlobular
        hD.isGlobular h2 hD'B hp
      have hk2 := isPastingIn_interchange_right hjm hLM.isGlobular hR.isGlobular hD'.isGlobular
        hD.isGlobular h2 hD'B hp
      have hk3 := isPastingIn_interchange_left hjm hL.isGlobular hMm.isGlobular hD'.isGlobular
        hD'.isGlobular h1 hDD hk1
      have hk4 := isPastingIn_interchange_right hjm hL.isGlobular hMm.isGlobular hD'.isGlobular
        hD'.isGlobular h1 hDD hk1
      have hk5 := isPastingIn_interchange hjm hL.isGlobular hMm.isGlobular hD'.isGlobular
        hD'.isGlobular h1 hDD hk1
      have hT' : ∀ l, j < l → l ≤ m → ∀ y ∈ P.boundary D' l false, grade ℕ y = l → T y := by
        intro l hl hlm y hy hyd
        refine hT l hl (by omega) y ?_ hyd
        rcases eq_or_lt_of_le hlm with rfl | hlm'
        · rwa [boundary_boundary_of_le le_rfl] at hy
        · rwa [hD.isGlobular l m hlm' false false] at hy
      obtain ⟨L'', R'', M'', hs'', hM'', ht''⟩ := ih hs.of_succ ht.of_succ hD' hD'le hjm hk4 hT'
      have heq : (L (m + 1) ⊔ D') ⊔ M'' m = (L (m + 1) ⊔ M m) ⊔ D' := by
        rw [hM'', sup_sup_sup_comm, sup_idem]
      have hp1 : P.IsPastingIn m (L (m + 1) ⊔ D') (M'' m) ((L (m + 1) ⊔ D') ⊔ M'' m) := by
        rw [heq, hM'']; exact hk5
      have hp2 : P.IsPastingIn m ((L (m + 1) ⊔ D') ⊔ M'' m) (R (m + 1) ⊔ D) N := by
        rw [heq]; exact hN
      refine ⟨_, _, _, hs''.extend hp1 hp2 (hk3.isMoleculeIn hL hD') ?_
        (hk2.isMoleculeIn hR hD) ?_, by simp, ht''.extend ?_ ?_⟩
      · rw [LowerSet.krullDim_sup]
        exact sup_le dL (hD'le.trans (by exact_mod_cast Nat.le_succ m))
      · rw [LowerSet.krullDim_sup]; exact sup_le dR hDd
      · rintro y (hy | hy) hyd
        · exact htL y hy hyd
        · have := grade_le_of_mem_boundary hy
          omega
      · rintro y (hy | hy) hyd
        · exact htR y hy hyd
        · exact hDtop y hy hyd

theorem exists_isStagedPasting_tops (T : P → Prop) (β : Bool) (m : ℕ)
    {X D N : LowerSet P} {j : ℕ} {L R M : ℕ → LowerSet P}
    (hs : P.IsStagedPasting m X L R M) (ht : StagedTops m L R T) (hD : IsMoleculeIn P D)
    (hDd : krullDim D ≤ m) (hj : j < m)
    (hp : P.IsPastingIn j (cond β (M m) D) (cond β D (M m)) N)
    (hT : ∀ l, j < l → l ≤ m → ∀ y ∈ P.boundary D l (!β), grade ℕ y = l → T y) :
    ∃ L' R' M' : ℕ → LowerSet P, P.IsStagedPasting m X L' R' M' ∧ M' m = N ∧
      StagedTops m L' R' T := by
  cases β
  · obtain ⟨L', R', M', hs', hM', ht'⟩ := exists_isStagedPasting_tops_right
      (P := dual P ⊤) T m hs.dual ht.toDual ((isMoleculeIn_dual ⊤).2 hD) hDd hj
      ((isPastingIn_dual ⊤).2 hp) (fun l hl hlm y hy hyd => hT l hl hlm y
        (by rwa [boundary_dual] at hy) hyd)
    exact ⟨R', L', M', hs'.ofDual, hM', ht'.ofDual⟩
  · exact exists_isStagedPasting_tops_right T m hs ht hD hDd hj hp hT

theorem StagedTops.mono {m : ℕ} {L R : ℕ → LowerSet P} {T T' : P → Prop}
    (h : StagedTops m L R T) (hT : ∀ z, T z → T' z) : StagedTops m L R T' :=
  fun i hi y hy hyd => hT y (h i hi y hy hyd)

end Tops

def arrowProdTops (L R : ℕ → LowerSet Q) (K : ℕ) (z : arrowCyl Q) :
    Prop :=
  z.1 = ⊤ ∨ ∃ i < K, z.2 ∈ L (i + 1) ⊔ R (i + 1) ∧ grade ℕ z.2 = i + 1

theorem arrowProdTops_of_mem_copyWhisker {L R : ℕ → LowerSet Q} {K k : ℕ} (hk : k < K)
    {γ : Bool} {Pc : LowerSet Q} (hPc : Pc = L (k + 1) ∨ Pc = R (k + 1))
    (hd : krullDim Pc ≤ (k + 1 : ℕ))
    {y : arrowCyl Q} (hy : y ∈ copyWhisker γ Pc k)
    (hyd : k < grade ℕ y) : arrowProdTops L R K y := by
  rcases LowerSet.mem_sup_iff.1 hy with hy | hy
  · rw [LowerSet.mem_prod, mem_Iic_globeOneEnd] at hy
    have h1 : grade ℕ y.2 ≤ k + 1 := krullDim_le_coe_iff.1 hd ⟨y.2, hy.2⟩
    rw [dim_arrowCyl_apply, hy.1, SuspCarrier.grade_pole] at hyd
    refine Or.inr ⟨k, hk, ?_, by omega⟩
    rcases hPc with rfl | rfl
    · exact Or.inl hy.2
    · exact Or.inr hy.2
  · have : grade ℕ y ≤ k := krullDim_le_coe_iff.1 (krullDim_copyWhiskerRest_le γ Pc k) ⟨y, hy⟩
    omega

theorem arrowProdTops_of_mem_arrowProd_univ {L R : ℕ → LowerSet Q} {K k : ℕ}
    {Pc : LowerSet Q} (hd : krullDim Pc ≤ (k + 1 : ℕ))
    {y : arrowCyl Q} (hy : y ∈ arrowProd ⊤ Pc)
    (hyd : k + 1 < grade ℕ y) : arrowProdTops L R K y := by
  by_cases h : y.1 = ⊤
  · exact Or.inl h
  · rw [LowerSet.mem_prod] at hy
    have h1 : grade ℕ y.2 ≤ k + 1 := krullDim_le_coe_iff.1 hd ⟨y.2, hy.2⟩
    rw [dim_arrowCyl_apply, dim_globe_one_eq_zero_of_ne h] at hyd
    omega

theorem exists_isStagedPasting_arrowProd_union {X : LowerSet Q}
    {L R : ℕ → LowerSet Q} {K n k : ℕ} (hkK : k < K) (hKn : K < n) {γ : Bool}
    {M Pc : LowerSet Q} (hM : IsMoleculeIn Q M)
    (hPc : IsMoleculeIn Q Pc) (hp : Q.IsPastingIn k (cond γ M Pc) (cond γ Pc M) (M ⊔ Pc))
    (hd : krullDim Pc ≤ (k + 1 : ℕ)) (hPLR : Pc = L (k + 1) ∨ Pc = R (k + 1))
    {L₀ R₀ M₀ : ℕ → LowerSet (arrowCyl Q)}
    (hs : (arrowCyl Q).IsStagedPasting n (arrowProd ⊤ X) L₀ R₀ M₀)
    (hM₀ : M₀ n = arrowProd ⊤ M) (ht : StagedTops n L₀ R₀ (arrowProdTops L R K)) :
    ∃ L' R' M' : ℕ → LowerSet (arrowCyl Q),
      (arrowCyl Q).IsStagedPasting n (arrowProd ⊤ X) L' R' M' ∧
        M' n = arrowProd ⊤ (M ⊔ Pc) ∧ StagedTops n L' R' (arrowProdTops L R K) := by
  have p1 := isPastingIn_arrowProd_copyWhisker hM hPc hp
  have p2 := isPastingIn_copyWhisker_arrowProd hM hPc hp
  have p3 := isPastingIn_arrowProd_union hM hPc hp hd
  have hW := copyWhisker_spec γ hPc k
  have hC := hM.boundary (k + 1) (!γ)
  have hW₂ := copyWhisker_spec (!γ) hC k
  have hcP := isMoleculeIn_arrowProd_univ (Q := Q) hPc
  have hD₂ : IsMoleculeIn (arrowCyl Q)
      (copyWhisker (!γ) (Q.boundary M (k + 1) (!γ)) k ⊔ arrowProd ⊤ Pc) :=
    p2.isMoleculeIn (Bool.cond_rec_prop γ hW₂.1 hcP) (Bool.cond_rec_prop γ hcP hW₂.1)
  have dW : krullDim (copyWhisker γ Pc k) ≤ (k + 1 : ℕ) :=
    (krullDim_copyWhisker_le hd k).trans
      (by exact_mod_cast max_le (le_refl (k + 1)) (Nat.le_succ k))
  have dW₂ : krullDim (copyWhisker (!γ) (Q.boundary M (k + 1) (!γ)) k) ≤ (k + 1 : ℕ) :=
    (krullDim_copyWhisker_le (krullDim_boundary_le M (k + 1) (!γ)) k).trans
      (by exact_mod_cast max_le (le_refl (k + 1)) (Nat.le_succ k))
  have dD₂ : krullDim
      ↥(copyWhisker (!γ) (Q.boundary M (k + 1) (!γ)) k ⊔ arrowProd ⊤ Pc) ≤ (k + 2 : ℕ) := by
    rw [LowerSet.krullDim_sup]
    exact sup_le (dW₂.trans (by exact_mod_cast Nat.le_succ _)) (krullDim_arrowProd_univ_le hd)
  have tW : ∀ l, k < l → ∀ (δ : Bool), ∀ y ∈ (arrowCyl Q).boundary
      (copyWhisker γ Pc k) l δ, grade ℕ y = l → arrowProdTops L R K y :=
    fun l hl δ y hy hyd => arrowProdTops_of_mem_copyWhisker hkK hPLR hd
      (boundary_le _ l δ hy) (by omega)
  have tD : ∀ l, k + 1 < l → ∀ (δ : Bool), ∀ y ∈ (arrowCyl Q).boundary
      (copyWhisker (!γ) (Q.boundary M (k + 1) (!γ)) k ⊔ arrowProd ⊤ Pc) l δ,
      grade ℕ y = l → arrowProdTops L R K y := by
    intro l hl δ y hy hyd
    rcases boundary_le _ l δ hy with hy' | hy'
    · have : grade ℕ y ≤ k + 1 := krullDim_le_coe_iff.1 dW₂ ⟨y, hy'⟩
      omega
    · exact arrowProdTops_of_mem_arrowProd_univ hd hy' (by omega)
  obtain ⟨L₁, R₁, M₁, hs₁, hM₁, ht₁⟩ : ∃ L' R' M' : ℕ → LowerSet (arrowCyl Q),
      (arrowCyl Q).IsStagedPasting n (arrowProd ⊤ X) L' R' M' ∧
        M' n = arrowProd ⊤ M ⊔ copyWhisker γ Pc k ∧
          StagedTops n L' R' (arrowProdTops L R K) := by
    exact exists_isStagedPasting_tops _ γ n hs ht hW.1
      (dW.trans (by exact_mod_cast (show k + 1 ≤ n by omega))) (by omega)
      (by rw [hM₀]; exact p1) fun l hl _ => tW l hl _
  exact exists_isStagedPasting_tops _ (!γ) n hs₁ ht₁ hD₂
    (dD₂.trans (by exact_mod_cast (show k + 2 ≤ n by omega))) (by omega)
    (by rw [hM₁]; exact p3) fun l hl _ => tD l hl _

theorem exists_isStagedPasting_arrowProd {X : LowerSet Q} (hX : IsMoleculeIn Q X)
    {K n : ℕ} (hKn : K < n) {L R M : ℕ → LowerSet Q} (hs : Q.IsStagedPasting K X L R M) :
    ∃ L' R' M' : ℕ → LowerSet (arrowCyl Q),
      (arrowCyl Q).IsStagedPasting n (arrowProd ⊤ X) L' R' M' ∧
        M' n = arrowProd ⊤ (M K) ∧ StagedTops n L' R' (arrowProdTops L R K) := by
  suffices H : ∀ k ≤ K, ∃ L' R' M' : ℕ → LowerSet (arrowCyl Q),
      (arrowCyl Q).IsStagedPasting n (arrowProd ⊤ X) L' R' M' ∧
        M' n = arrowProd ⊤ (M k) ∧ StagedTops n L' R' (arrowProdTops L R K) from
    H K le_rfl
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨_, _, _, isStagedPasting_self (isMoleculeIn_arrowProd_univ hX) n,
      by rw [hs.stage_zero], fun i _ y hy hyd => ?_⟩
    rcases hy with hy | hy <;> have := grade_le_of_mem_boundary hy <;> omega
  | succ k ih =>
    intro hk
    obtain ⟨L₀, R₀, M₀, hs₀, hM₀, ht₀⟩ := ih (by omega)
    obtain ⟨h1, h2⟩ := hs.stage_succ k (by omega)
    obtain ⟨hL, dL⟩ := hs.isMoleculeIn_left k (by omega)
    obtain ⟨hR, dR⟩ := hs.isMoleculeIn_right k (by omega)
    have hMk := hs.isMoleculeIn_stage k (by omega)
    have h1' : Q.IsPastingIn k (cond false (M k) (L (k + 1))) (cond false (L (k + 1)) (M k))
        (M k ⊔ L (k + 1)) := by rw [sup_comm]; exact h1
    obtain ⟨L₁, R₁, M₁, hs₁, hM₁, ht₁⟩ := exists_isStagedPasting_arrowProd_union (by omega) hKn
      hMk hL h1' dL (Or.inl rfl) hs₀ hM₀ ht₀
    have hLM := h1.isMoleculeIn hL hMk
    have h2' : Q.IsPastingIn k (cond true (L (k + 1) ⊔ M k) (R (k + 1)))
        (cond true (R (k + 1)) (L (k + 1) ⊔ M k)) ((L (k + 1) ⊔ M k) ⊔ R (k + 1)) := by
      rw [h2.sup_eq]; exact h2
    rw [sup_comm] at hM₁
    obtain ⟨L₂, R₂, M₂, hs₂, hM₂, ht₂⟩ := exists_isStagedPasting_arrowProd_union (by omega) hKn
      hLM hR h2' dR (Or.inr rfl) hs₁ hM₁ ht₁
    exact ⟨L₂, R₂, M₂, hs₂, by rw [hM₂, h2.sup_eq], ht₂⟩

theorem exists_isStagedPasting_copyWhisker {V : LowerSet Q} (hV : IsMoleculeIn Q V)
    (β : Bool) {d n : ℕ} (hdn : d ≤ n) :
    ∃ L R M : ℕ → LowerSet (arrowCyl Q),
      (arrowCyl Q).IsStagedPasting n (arrowProd (.Iic (globeOneEnd β)) V) L R M ∧
        M n = copyWhisker β V d ∧
          StagedTops n L R (fun z => z.1 = ⊤) := by
  suffices H : ∀ l ≤ d, ∃ L R M : ℕ → LowerSet (arrowCyl Q),
      (arrowCyl Q).IsStagedPasting n (arrowProd (.Iic (globeOneEnd β)) V) L R M ∧
        M n = copyWhisker β V l ∧
        StagedTops n L R (fun z => z.1 = ⊤) from H _ le_rfl
  intro l
  induction l with
  | zero =>
    intro _
    refine ⟨_, _, _, isStagedPasting_self (isMoleculeIn_arrowProd_end hV β) n,
      (copyWhisker_zero β V).symm, fun i _ y hy hyd => ?_⟩
    rcases hy with hy | hy <;> have := grade_le_of_mem_boundary hy <;> omega
  | succ l ih =>
    intro hl
    obtain ⟨L₀, R₀, M₀, hs₀, hM₀, ht₀⟩ := ih (by omega)
    have hp := isPastingIn_copyWhisker_succ β hV l
    have hE := isMoleculeIn_arrowProd_univ (hV.boundary l (!β))
    have dE : krullDim (arrowProd ⊤ (Q.boundary V l (!β))) ≤ (l + 1 : ℕ) :=
      krullDim_arrowProd_univ_le (krullDim_boundary_le V l (!β))
    have tE : ∀ l', l < l' → ∀ (δ : Bool), ∀ y ∈ (arrowCyl Q).boundary
        (arrowProd ⊤ (Q.boundary V l (!β))) l' δ, grade ℕ y = l' →
        y.1 = ⊤ := by
      intro l' hl' δ y hy hyd
      by_contra h
      have hy' : y ∈ arrowProd ⊤ (Q.boundary V l (!β)) := boundary_le _ l' δ hy
      rw [LowerSet.mem_prod] at hy'
      have := grade_le_of_mem_boundary hy'.2
      rw [dim_arrowCyl_apply, dim_globe_one_eq_zero_of_ne h] at hyd
      omega
    exact exists_isStagedPasting_tops _ (!β) n hs₀ ht₀ hE
      (dE.trans (by exact_mod_cast (show l + 1 ≤ n by omega))) (by omega)
      (by rw [hM₀]; exact hp) fun l' hl' _ => tE l' hl' _

theorem exists_isStagedPasting_arrowProd_top {V X : LowerSet Q} (hV : IsMoleculeIn Q V)
    (hX : IsMoleculeIn Q X) {d : ℕ} (hd : krullDim V = (d + 1 : ℕ)) (σ : Bool)
    {L R M : ℕ → LowerSet Q} (hs : Q.IsStagedPasting d X L R M)
    (hM : M d = Q.boundary V d σ) :
    ∃ L' R' M' : ℕ → LowerSet (arrowCyl Q),
      (arrowCyl Q).IsStagedPasting (d + 1) (arrowProd ⊤ X) L' R' M' ∧
        M' (d + 1) = copyWhisker (!σ) V (d + 1) ∧
          StagedTops (d + 1) L' R' (fun z => arrowProdTops L R d z ∨
            (z.1 = globeOneEnd (!σ) ∧ z.2 ∈ V ∧ grade ℕ z.2 = d + 1)) := by
  obtain ⟨L₀, R₀, M₀, hs₀, hM₀, ht₀⟩ :=
    exists_isStagedPasting_arrowProd hX (Nat.lt_succ_self d) hs
  have hp := isPastingIn_copyWhisker_succ (!σ) hV d
  rw [Bool.not_not] at hp
  have hW := (copyWhisker_spec (!σ) hV d).1
  have dW : krullDim (copyWhisker (!σ) V d) ≤ (d + 1 : ℕ) :=
    (krullDim_copyWhisker_le hd.le d).trans (by rw [max_eq_left (Nat.le_succ d)])
  have tW : ∀ l, d < l → ∀ (δ : Bool), ∀ y ∈ (arrowCyl Q).boundary
      (copyWhisker (!σ) V d) l δ, grade ℕ y = l →
      (arrowProdTops L R d y ∨ (y.1 = globeOneEnd (!σ) ∧ y.2 ∈ V ∧ grade ℕ y.2 = d + 1)) := by
    intro l hl δ y hy hyd
    rcases LowerSet.mem_sup_iff.1 (boundary_le _ l δ hy) with hy' | hy'
    · rw [LowerSet.mem_prod, mem_Iic_globeOneEnd] at hy'
      have : grade ℕ y.2 ≤ d + 1 := krullDim_le_coe_iff.1 hd.le ⟨y.2, hy'.2⟩
      rw [dim_arrowCyl_apply, hy'.1, SuspCarrier.grade_pole] at hyd
      exact Or.inr ⟨hy'.1, hy'.2, by omega⟩
    · have : grade ℕ y ≤ d := krullDim_le_coe_iff.1 (krullDim_copyWhiskerRest_le (!σ) V d) ⟨y, hy'⟩
      omega
  have ht₀' := ht₀.mono fun z hz => Or.inl (b := (z.1 = globeOneEnd (!σ) ∧ z.2 ∈ V ∧
    grade ℕ z.2 = d + 1)) hz
  rw [hM] at hM₀
  exact exists_isStagedPasting_tops _ (!σ) (d + 1) hs₀ ht₀' hW dW (Nat.lt_succ_self d)
    (by rw [hM₀, Bool.cond_not, Bool.cond_not]; exact hp) fun l hl _ => tW l hl _

theorem IsStagedPasting.map {P Q : OGP.{u}} (f : P ⟶ Q) [IsInclusion f]
    {m : ℕ} {X : LowerSet P} {L R M : ℕ → LowerSet P}
    (h : P.IsStagedPasting m X L R M) :
    Q.IsStagedPasting m (OGP.map f X) (fun i => OGP.map f (L i)) (fun i => OGP.map f (R i))
      (fun i => OGP.map f (M i)) := by
  refine ⟨congrArg _ h.stage_zero,
    fun i hi => (isMoleculeIn_map_iff f _).2 (h.isMoleculeIn_stage i hi),
    fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · obtain ⟨h1, h2⟩ := h.stage_succ i hi
    rw [← map_sup]
    exact ⟨(isPastingIn_map_iff f i _ _ _).2 h1, (isPastingIn_map_iff f i _ _ _).2 h2⟩
  · exact ⟨(isMoleculeIn_map_iff f _).2 (h.isMoleculeIn_left i hi).1,
      (krullDim_map f _).trans_le (h.isMoleculeIn_left i hi).2⟩
  · exact ⟨(isMoleculeIn_map_iff f _).2 (h.isMoleculeIn_right i hi).1,
      (krullDim_map f _).trans_le (h.isMoleculeIn_right i hi).2⟩

end Atoms.Molecule.OGP
