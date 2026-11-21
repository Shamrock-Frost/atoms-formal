import Atoms.Molecule.Pasting.Basic

universe u

open Order

namespace Atoms.Molecule.OGP

variable {P : OGP.{u}} {m : ℕ} {X : LowerSet P} {L R M : ℕ → LowerSet P}

variable (P) in
structure IsStagedPasting (m : ℕ) (X : LowerSet P) (L R M : ℕ → LowerSet P) : Prop where
  stage_zero : M 0 = X
  isMoleculeIn_stage : ∀ i ≤ m, IsMoleculeIn P (M i)
  stage_succ : ∀ i < m, P.IsPastingIn i (L (i + 1)) (M i) (L (i + 1) ⊔ M i) ∧
    P.IsPastingIn i (L (i + 1) ⊔ M i) (R (i + 1)) (M (i + 1))
  isMoleculeIn_left : ∀ i < m,
    IsMoleculeIn P (L (i + 1)) ∧ krullDim (L (i + 1)) ≤ ((i + 1 : ℕ) : WithBot ℕ∞)
  isMoleculeIn_right : ∀ i < m,
    IsMoleculeIn P (R (i + 1)) ∧ krullDim (R (i + 1)) ≤ ((i + 1 : ℕ) : WithBot ℕ∞)

instance decidableIsStagedPasting [Fintype P] [DecidableEq P] [DecidableLE P]
    (m : ℕ) (X : LowerSet P) (L R M : ℕ → LowerSet P) [DecidablePred (· ∈ X)]
    [∀ i, DecidablePred (· ∈ L i)] [∀ i, DecidablePred (· ∈ R i)]
    [∀ i, DecidablePred (· ∈ M i)] : Decidable (P.IsStagedPasting m X L R M) :=
  decidable_of_iff (M 0 = X ∧ (∀ i ≤ m, IsMoleculeIn P (M i)) ∧
    ∀ i < m, P.IsPastingIn i (L (i + 1)) (M i) (L (i + 1) ⊔ M i) ∧
      P.IsPastingIn i (L (i + 1) ⊔ M i) (R (i + 1)) (M (i + 1)) ∧
      IsMoleculeIn P (L (i + 1)) ∧ krullDim (L (i + 1)) ≤ ((i + 1 : ℕ) : WithBot ℕ∞) ∧
      IsMoleculeIn P (R (i + 1)) ∧ krullDim (R (i + 1)) ≤ ((i + 1 : ℕ) : WithBot ℕ∞))
    ⟨fun ⟨h0, hM, hs⟩ => ⟨h0, hM, fun i hi => ⟨(hs i hi).1, (hs i hi).2.1⟩,
      fun i hi => ⟨(hs i hi).2.2.1, (hs i hi).2.2.2.1⟩,
      fun i hi => ⟨(hs i hi).2.2.2.2.1, (hs i hi).2.2.2.2.2⟩⟩,
    fun h => ⟨h.stage_zero, h.isMoleculeIn_stage, fun i hi =>
      ⟨(h.stage_succ i hi).1, (h.stage_succ i hi).2, (h.isMoleculeIn_left i hi).1,
        (h.isMoleculeIn_left i hi).2, (h.isMoleculeIn_right i hi).1,
        (h.isMoleculeIn_right i hi).2⟩⟩⟩

namespace IsStagedPasting

theorem of_succ (h : P.IsStagedPasting (m + 1) X L R M) : P.IsStagedPasting m X L R M :=
  ⟨h.stage_zero, fun i hi => h.isMoleculeIn_stage i (by omega),
    fun i hi => h.stage_succ i (by omega), fun i hi => h.isMoleculeIn_left i (by omega),
    fun i hi => h.isMoleculeIn_right i (by omega)⟩

theorem extend (h : P.IsStagedPasting m X L R M) {l r N : LowerSet P}
    (h1 : P.IsPastingIn m l (M m) (l ⊔ M m)) (h2 : P.IsPastingIn m (l ⊔ M m) r N)
    (hl : IsMoleculeIn P l) (dl : krullDim l ≤ ((m + 1 : ℕ) : WithBot ℕ∞))
    (hr : IsMoleculeIn P r) (dr : krullDim r ≤ ((m + 1 : ℕ) : WithBot ℕ∞)) :
    P.IsStagedPasting (m + 1) X (fun i => if i = m + 1 then l else L i)
      (fun i => if i = m + 1 then r else R i) (fun i => if i = m + 1 then N else M i) := by
  obtain ⟨h0, hM, hs, hL, hR⟩ := h
  refine ⟨by simpa using h0, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · by_cases e : i = m + 1
    · simp only [e, if_true]
      exact h2.isMoleculeIn (h1.isMoleculeIn hl (hM m le_rfl)) hr
    · simp only [e, if_false]
      exact hM i (by omega)
  · have e : i ≠ m + 1 := by omega
    by_cases e' : i = m
    · subst e'
      simp only [e, if_true, if_false]
      exact ⟨h1, h2⟩
    · have e'' : i + 1 ≠ m + 1 := by omega
      simp only [e, e'', if_false]
      exact hs i (by omega)
  · by_cases e' : i = m
    · subst e'
      rw [if_pos rfl]
      exact ⟨hl, dl⟩
    · have e'' : i + 1 ≠ m + 1 := by omega
      rw [if_neg e'']
      exact hL i (by omega)
  · by_cases e' : i = m
    · subst e'
      rw [if_pos rfl]
      exact ⟨hr, dr⟩
    · have e'' : i + 1 ≠ m + 1 := by omega
      rw [if_neg e'']
      exact hR i (by omega)

theorem dual (h : P.IsStagedPasting m X L R M) : (dual P ⊤).IsStagedPasting m X R L M :=
  ⟨h.stage_zero, fun i hi => (isMoleculeIn_dual ⊤).2 (h.isMoleculeIn_stage i hi),
    fun i hi => ⟨((isPastingIn_dual ⊤).2 (h.stage_succ i hi).1).isPastingIn_left_sup
      ((isPastingIn_dual ⊤).2 (h.stage_succ i hi).2),
      ((isPastingIn_dual ⊤).2 (h.stage_succ i hi).1).assoc_symm
        ((isPastingIn_dual ⊤).2 (h.stage_succ i hi).2)⟩,
    fun i hi => ⟨(isMoleculeIn_dual ⊤).2 (h.isMoleculeIn_right i hi).1,
      (h.isMoleculeIn_right i hi).2⟩,
    fun i hi => ⟨(isMoleculeIn_dual ⊤).2 (h.isMoleculeIn_left i hi).1,
      (h.isMoleculeIn_left i hi).2⟩⟩

theorem ofDual (h : (OGP.dual P ⊤).IsStagedPasting m X L R M) : P.IsStagedPasting m X R L M :=
  (congrArg (fun o => IsStagedPasting { P with orient := o } m X R L M)
    (orient_dual_dual P ⊤)).mp h.dual

theorem stage_le (h : P.IsStagedPasting m X L R M) : ∀ i j, i ≤ j → j ≤ m → M i ≤ M j := by
  intro i j hij hjm
  induction j with
  | zero =>
    obtain rfl : i = 0 := by omega
    exact le_rfl
  | succ j ih =>
    rcases eq_or_lt_of_le hij with rfl | hlt
    · exact le_rfl
    · refine (ih (by omega) (by omega)).trans ?_
      rw [← (h.stage_succ j (by omega)).2.sup_eq]
      exact le_sup_right.trans le_sup_left

theorem left_sup_right_le_stage (h : P.IsStagedPasting m X L R M) {i : ℕ} (hi : i < m) :
    L (i + 1) ⊔ R (i + 1) ≤ M (i + 1) := by
  obtain ⟨-, h2⟩ := h.stage_succ i hi
  rw [← h2.sup_eq]
  exact sup_le_sup_right le_sup_left _

theorem isSubmoleculeOf_stage (h : P.IsStagedPasting m X L R M) (hX : IsMoleculeIn P X) :
    ∀ i ≤ m, P.IsSubmoleculeOf X (M i) := by
  intro i
  induction i with
  | zero =>
    intro _
    rw [h.stage_zero]
    exact .refl hX
  | succ i ih =>
    intro hi
    obtain ⟨h1, h2⟩ := h.stage_succ i (by omega)
    have hM := h.isMoleculeIn_stage i (by omega)
    have hL := (h.isMoleculeIn_left i (by omega)).1
    exact ((ih (by omega)).tail (h1.isPastingFactorOf true hM hL)).tail
      (h2.isPastingFactorOf false (h1.isMoleculeIn hL hM) (h.isMoleculeIn_right i (by omega)).1)

theorem notMem_of_mem_piece (h : P.IsStagedPasting m X L R M) {i : ℕ} (hi : i < m) {y : P}
    (hy : y ∈ L (i + 1) ⊔ R (i + 1)) (hd : i < grade ℕ y) : y ∉ X := by
  intro hyX
  obtain ⟨h1, h2⟩ := h.stage_succ i hi
  have hyM : y ∈ M i := h.stage_le 0 i (Nat.zero_le i) (by omega) (h.stage_zero ▸ hyX)
  rcases hy with hy | hy
  · have hb : y ∈ P.boundary (L (i + 1)) i true := h1.inf_eq_output ▸ ⟨hy, hyM⟩
    exact absurd (grade_le_of_mem_boundary hb) (by omega)
  · have hb : y ∈ P.boundary (R (i + 1)) i false :=
      h2.inf_eq_input ▸ (⟨Or.inr hyM, hy⟩ : y ∈ (L (i + 1) ⊔ M i) ⊓ R (i + 1))
    exact absurd (grade_le_of_mem_boundary hb) (by omega)

end IsStagedPasting

theorem isStagedPasting_self (hX : IsMoleculeIn P X) (m : ℕ) :
    P.IsStagedPasting m X (fun i => P.boundary X (i - 1) false)
      (fun i => P.boundary X (i - 1) true) (fun _ => X) := by
  refine ⟨rfl, fun _ _ => hX, fun i _ => ?_, fun i _ => ?_, fun i _ => ?_⟩
  · simp only [Nat.add_sub_cancel]
    rw [sup_eq_right.2 (boundary_le X i false)]
    exact ⟨isPastingIn_boundary_false_self X i, isPastingIn_self_boundary_true X i⟩
  · simp only [Nat.add_sub_cancel]
    exact ⟨hX.boundary i false,
      (krullDim_boundary_le X i false).trans (by exact_mod_cast Nat.le_succ i)⟩
  · simp only [Nat.add_sub_cancel]
    exact ⟨hX.boundary i true,
      (krullDim_boundary_le X i true).trans (by exact_mod_cast Nat.le_succ i)⟩

private theorem exists_isStagedPasting_of_isPastingIn_right :
    ∀ (m : ℕ) {X D N : LowerSet P} {j : ℕ} {L R M : ℕ → LowerSet P},
      P.IsStagedPasting m X L R M → IsMoleculeIn P D → krullDim D ≤ m → j < m →
        P.IsPastingIn j (M m) D N →
          ∃ L' R' M' : ℕ → LowerSet P, P.IsStagedPasting m X L' R' M' ∧ M' m = N := by
  intro m
  induction m with
  | zero => intro _ _ _ j _ _ _ _ _ _ hj; omega
  | succ m ih =>
    intro X D N j L R M hs hD hDd hj hp
    obtain ⟨h1, h2⟩ := hs.stage_succ m (Nat.lt_succ_self m)
    obtain ⟨hL, dL⟩ := hs.isMoleculeIn_left m (Nat.lt_succ_self m)
    obtain ⟨hR, dR⟩ := hs.isMoleculeIn_right m (Nat.lt_succ_self m)
    have hMm := hs.isMoleculeIn_stage m (by omega)
    have hLM := h1.isMoleculeIn hL hMm
    rcases eq_or_lt_of_le (Nat.le_of_lt_succ hj) with rfl | hjm
    · refine ⟨_, _, _, hs.of_succ.extend h1 (h2.assoc hp) hL dL
        ((h2.isPastingIn_right_sup hp).isMoleculeIn hR hD) ?_, by simp⟩
      rw [LowerSet.krullDim_sup]
      exact sup_le dR hDd
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
      obtain ⟨L'', R'', M'', hs'', hM''⟩ := ih hs.of_succ hD' hD'le hjm hk4
      have heq : (L (m + 1) ⊔ D') ⊔ M'' m = (L (m + 1) ⊔ M m) ⊔ D' := by
        rw [hM'', sup_sup_sup_comm, sup_idem]
      have hp1 : P.IsPastingIn m (L (m + 1) ⊔ D') (M'' m) ((L (m + 1) ⊔ D') ⊔ M'' m) := by
        rw [heq, hM'']
        exact hk5
      have hp2 : P.IsPastingIn m ((L (m + 1) ⊔ D') ⊔ M'' m) (R (m + 1) ⊔ D) N := by
        rw [heq]
        exact hN
      refine ⟨_, _, _, hs''.extend hp1 hp2 (hk3.isMoleculeIn hL hD') ?_ (hk2.isMoleculeIn hR hD)
        ?_, by simp⟩
      · rw [LowerSet.krullDim_sup]
        exact sup_le dL (hD'le.trans (by exact_mod_cast Nat.le_succ m))
      · rw [LowerSet.krullDim_sup]
        exact sup_le dR hDd

theorem exists_isStagedPasting_of_isPastingIn (β : Bool) (m : ℕ) {X D N : LowerSet P} {j : ℕ}
    {L R M : ℕ → LowerSet P} (hs : P.IsStagedPasting m X L R M) (hD : IsMoleculeIn P D)
    (hDd : krullDim D ≤ m) (hj : j < m) (hp : P.IsPastingIn j (cond β (M m) D) (cond β D (M m)) N) :
    ∃ L' R' M' : ℕ → LowerSet P, P.IsStagedPasting m X L' R' M' ∧ M' m = N := by
  cases β
  · obtain ⟨L', R', M', hs', hM'⟩ := exists_isStagedPasting_of_isPastingIn_right
      (P := dual P ⊤) m hs.dual ((isMoleculeIn_dual ⊤).2 hD) hDd hj ((isPastingIn_dual ⊤).2 hp)
    exact ⟨R', L', M', hs'.ofDual, hM'⟩
  · exact exists_isStagedPasting_of_isPastingIn_right m hs hD hDd hj hp

theorem exists_isStagedPasting_of_isSubmoleculeOf {U : LowerSet P} (h : P.IsSubmoleculeOf X U)
    (n : ℕ) : krullDim U ≤ n →
      ∃ L R M : ℕ → LowerSet P, P.IsStagedPasting n X L R M ∧ M n = U := by
  refine IsSubmoleculeOf.induction_paste (motive := fun X U => krullDim U ≤ n →
      ∃ L R M : ℕ → LowerSet P, P.IsStagedPasting n X L R M ∧ M n = U)
    (fun U hU _ => ⟨_, _, _, isStagedPasting_self hU n, rfl⟩) ?_ h
  intro α k A B U X hp _ hB hkB hAU hBU _ ih hd
  obtain ⟨L, R, M, hs, hMn⟩ := ih ((LowerSet.krullDim_mono hAU).trans hd)
  have hBn : krullDim B ≤ n := (LowerSet.krullDim_mono hBU).trans hd
  have hkn : k < n := by exact_mod_cast hkB.trans_le hBn
  rw [← hMn] at hp
  exact exists_isStagedPasting_of_isPastingIn α n hs hB hBn hkn hp

end Atoms.Molecule.OGP
