import Atoms.Molecule.Pasting.Basic

universe u

open CategoryTheory Order Set

namespace Atoms.Molecule.OGP

variable {P Q : OGP.{u}} {U V S T : LowerSet P} {n k j : ℕ} {α β : Bool} {x : P}

variable (P) in
def properBoundary (U : LowerSet P) : LowerSet P :=
  ⨆ (n : ℕ) (_ : (n : WithBot ℕ∞) < krullDim U), P.boundaryFull U n

variable (P) in
protected def interior (U : LowerSet P) : Set P :=
  (U : Set P) \ P.properBoundary U

theorem mem_boundaryFull : x ∈ P.boundaryFull U n ↔ ∃ α, x ∈ P.boundary U n α := by
  rw [boundaryFull, LowerSet.mem_sup_iff, Bool.exists_bool]

theorem boundary_le_boundaryFull (U : LowerSet P) (n : ℕ) (α : Bool) :
    P.boundary U n α ≤ P.boundaryFull U n :=
  fun _ hx => mem_boundaryFull.2 ⟨α, hx⟩

theorem mem_properBoundary :
    x ∈ P.properBoundary U ↔
      ∃ n : ℕ, (n : WithBot ℕ∞) < krullDim U ∧ ∃ α, x ∈ P.boundary U n α := by
  simp only [properBoundary, LowerSet.mem_iSup₂_iff, mem_boundaryFull, exists_prop]

theorem boundaryFull_le_properBoundary (hn : (n : WithBot ℕ∞) < krullDim U) :
    P.boundaryFull U n ≤ P.properBoundary U :=
  le_iSup₂_of_le n hn le_rfl

theorem boundary_le_properBoundary (hn : (n : WithBot ℕ∞) < krullDim U) (α : Bool) :
    P.boundary U n α ≤ P.properBoundary U :=
  (boundary_le_boundaryFull U n α).trans (boundaryFull_le_properBoundary hn)

theorem properBoundary_le (U : LowerSet P) : P.properBoundary U ≤ U :=
  iSup₂_le fun n _ => sup_le (boundary_le U n false) (boundary_le U n true)

theorem properBoundary_eq_bot (h : krullDim U ≤ 0) : P.properBoundary U = ⊥ :=
  iSup₂_eq_bot.2 fun n hn => absurd (hn.trans_le h) (not_lt.2 (by exact_mod_cast n.zero_le))

theorem bdry_le_properBoundary (U : LowerSet P) (α : Bool) : P.bdry U α ≤ P.properBoundary U :=
  iSup₂_le fun m hm => boundary_le_properBoundary (by rw [hm]; exact_mod_cast m.lt_succ_self) α

theorem bdryFull_le_properBoundary (U : LowerSet P) : P.bdryFull U ≤ P.properBoundary U :=
  sup_le (bdry_le_properBoundary U false) (bdry_le_properBoundary U true)

theorem IsGlobular.properBoundary_eq_bdryFull (hU : P.IsGlobular U) (hd : krullDim U ≠ ⊤) :
    P.properBoundary U = P.bdryFull U := by
  refine le_antisymm (iSup₂_le fun k hk => ?_) (bdryFull_le_properBoundary U)
  obtain ⟨d, hd'⟩ : ∃ d : ℕ, krullDim U = d := by
    match h : krullDim U with
    | ⊥ => exact absurd (h ▸ hk) not_lt_bot
    | some ⊤ => exact absurd h hd
    | some (some d) => exact ⟨d, rfl⟩
  rw [hd'] at hk
  have hkd : k < d := by exact_mod_cast hk
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  exact hU.boundaryFull_le_bdryFull (by rw [hd']; push_cast; rfl) (by omega)

theorem IsMoleculeIn.properBoundary_eq_bdryFull (h : IsMoleculeIn P U) :
    P.properBoundary U = P.bdryFull U := by
  obtain ⟨d, hd⟩ := h.exists_krullDim_eq
  exact h.isGlobular.properBoundary_eq_bdryFull (by rw [hd]; nofun)

@[simp] protected theorem mem_interior : x ∈ P.interior U ↔ x ∈ U ∧ x ∉ P.properBoundary U :=
  Iff.rfl

protected theorem interior_subset (U : LowerSet P) : P.interior U ⊆ U :=
  sdiff_subset

theorem diff_interior (U : LowerSet P) : (U : Set P) \ P.interior U = P.properBoundary U :=
  sdiff_sdiff_cancel_left (properBoundary_le U)

theorem mem_properBoundary_of_notMem_interior (hx : x ∈ U) (hi : x ∉ P.interior U) :
    x ∈ P.properBoundary U :=
  not_not.1 fun h => hi ⟨hx, h⟩

theorem mem_diff_interior_iff_of_mem {X : Set P} (hX : (P.properBoundary U : Set P) ⊆ X)
    (hx : x ∈ U) : x ∈ X \ P.interior U ↔ x ∈ P.properBoundary U :=
  ⟨fun h => mem_properBoundary_of_notMem_interior hx h.2, fun h => ⟨hX h, fun h' => h'.2 h⟩⟩

theorem interior_eq_self (h : krullDim U ≤ 0) : P.interior U = U := by
  rw [OGP.interior, properBoundary_eq_bot h, LowerSet.coe_bot, sdiff_empty]

theorem mem_interior_of_krullDim_le (hx : x ∈ U) (h : krullDim U ≤ grade ℕ x) :
    x ∈ P.interior U := by
  refine ⟨hx, fun hb => ?_⟩
  obtain ⟨n, hn, α, hxn⟩ := mem_properBoundary.1 hb
  exact (hn.trans_le h).not_ge (by exact_mod_cast grade_le_of_mem_boundary hxn)

theorem IsMoleculeIn.interior_Iic {x : P} (h : IsMoleculeIn P (LowerSet.Iic x)) :
    P.interior (LowerSet.Iic x) = {x} := by
  ext y
  have hb : y ∈ P.properBoundary (LowerSet.Iic x) ↔ y < x := by
    rw [h.properBoundary_eq_bdryFull, ← SetLike.mem_coe, bdryFull, coe_bdry_Iic_sup, Set.mem_Iio]
  rw [OGP.mem_interior, LowerSet.mem_Iic_iff, hb, Set.mem_singleton_iff, lt_iff_le_and_ne]
  exact ⟨fun ⟨hle, hn⟩ => by_contra fun hne => hn ⟨hle, hne⟩,
    fun h => ⟨h.le, fun ⟨_, hne⟩ => hne h⟩⟩

theorem IsGlobular.exists_mem_interior_boundary (hU : P.IsGlobular U)
    (hx : x ∈ P.boundary U k α) : ∃ j ≤ k, ∃ β, x ∈ P.interior (P.boundary U j β) := by
  induction k using Nat.strong_induction_on generalizing α with
  | _ k ih =>
    by_cases hi : x ∈ P.interior (P.boundary U k α)
    · exact ⟨k, le_rfl, α, hi⟩
    obtain ⟨m, hm, γ, hxm⟩ := mem_properBoundary.1 (mem_properBoundary_of_notMem_interior hx hi)
    have hmk : m < k := by exact_mod_cast hm.trans_le (krullDim_boundary_le U k α)
    rw [hU m k hmk γ α] at hxm
    obtain ⟨j, hj, β, hβ⟩ := ih m hmk hxm
    exact ⟨j, hj.trans hmk.le, β, hβ⟩

theorem IsGlobular.mem_interior_or_exists_mem_interior_boundary (hU : P.IsGlobular U)
    (hx : x ∈ U) :
    x ∈ P.interior U ∨
      ∃ k : ℕ, (k : WithBot ℕ∞) < krullDim U ∧ ∃ α, x ∈ P.interior (P.boundary U k α) := by
  by_cases hi : x ∈ P.interior U
  · exact Or.inl hi
  obtain ⟨n, hn, α, hxn⟩ := mem_properBoundary.1 (mem_properBoundary_of_notMem_interior hx hi)
  obtain ⟨k, hk, β, hβ⟩ := hU.exists_mem_interior_boundary hxn
  exact Or.inr ⟨k, lt_of_le_of_lt (by exact_mod_cast hk) hn, β, hβ⟩

theorem disjoint_interior_interior_boundary (hk : (k : WithBot ℕ∞) < krullDim U) (α : Bool) :
    Disjoint (P.interior U) (P.interior (P.boundary U k α)) :=
  disjoint_left.2 fun _ hx hxk => hx.2 (boundary_le_properBoundary hk α hxk.1)

theorem IsGlobular.notMem_boundary_of_mem_interior_boundary (hU : P.IsGlobular U)
    (hj : (j : WithBot ℕ∞) < krullDim (P.boundary U k α)) (β : Bool)
    (hx : x ∈ P.interior (P.boundary U k α)) : x ∉ P.boundary U j β := fun hxj => by
  have hjk : j < k := by exact_mod_cast hj.trans_le (krullDim_boundary_le U k α)
  rw [← hU j k hjk β α] at hxj
  exact hx.2 (boundary_le_properBoundary hj β hxj)

theorem IsMoleculeIn.properBoundary_boundary_succ (h : IsMoleculeIn P U)
    (hk : ((k + 1 : ℕ) : WithBot ℕ∞) ≤ krullDim U) (α : Bool) :
    P.properBoundary (P.boundary U (k + 1) α) = P.boundaryFull U k := by
  have hd : krullDim (P.boundary U (k + 1) α) = k + 1 := by
    rw [h.krullDim_boundary hk]
    push_cast
    rfl
  rw [(h.boundary (k + 1) α).properBoundary_eq_bdryFull, bdryFull, bdry_eq_boundary hd,
    bdry_eq_boundary hd, h.isGlobular k (k + 1) k.lt_succ_self false α,
    h.isGlobular k (k + 1) k.lt_succ_self true α, boundaryFull]

theorem IsMoleculeIn.interior_boundary_succ (h : IsMoleculeIn P U)
    (hk : ((k + 1 : ℕ) : WithBot ℕ∞) ≤ krullDim U) (α : Bool) :
    P.interior (P.boundary U (k + 1) α) =
      (P.boundary U (k + 1) α : Set P) \ P.boundaryFull U k := by
  rw [OGP.interior, h.properBoundary_boundary_succ hk]

theorem IsRound.inf_boundary_eq_properBoundary (hr : P.IsRound U) (h : IsMoleculeIn P U)
    (hk : (k : WithBot ℕ∞) < krullDim U) (α : Bool) :
    P.boundary U k α ⊓ P.boundary U k (!α) = P.properBoundary (P.boundary U k α) := by
  have hc : P.boundary U k α ⊓ P.boundary U k (!α) =
      P.boundary U k false ⊓ P.boundary U k true := by
    cases α
    · rfl
    · exact inf_comm _ _
  rw [hc]
  cases k with
  | zero =>
    rw [properBoundary_eq_bot (krullDim_boundary_le U 0 α)]
    exact hr.inf_boundary_zero hk
  | succ m => rw [hr.inf_boundary_succ m hk, h.properBoundary_boundary_succ hk.le]

theorem IsRound.disjoint_interior_boundary_not (hr : P.IsRound U) (h : IsMoleculeIn P U)
    (hk : (k : WithBot ℕ∞) < krullDim U) (α : Bool) :
    Disjoint (P.interior (P.boundary U k α)) (P.interior (P.boundary U k (!α))) :=
  disjoint_left.2 fun _ hx hx' =>
    hx.2 ((hr.inf_boundary_eq_properBoundary h hk α).le ⟨hx.1, hx'.1⟩)

theorem IsRound.eq_of_mem_interior_boundary (hr : P.IsRound U) (h : IsMoleculeIn P U)
    (hk : (k : WithBot ℕ∞) < krullDim U) (hj : (j : WithBot ℕ∞) < krullDim U)
    (hxk : x ∈ P.interior (P.boundary U k α)) (hxj : x ∈ P.interior (P.boundary U j β)) :
    k = j ∧ α = β := by
  rcases lt_trichotomy j k with hjk | rfl | hkj
  · refine absurd hxj.1 (h.isGlobular.notMem_boundary_of_mem_interior_boundary ?_ β hxk)
    rw [h.krullDim_boundary hk.le]
    exact_mod_cast hjk
  · refine ⟨rfl, ?_⟩
    by_contra hne
    rw [Bool.eq_not_of_ne (Ne.symm hne)] at hxj
    exact disjoint_left.1 (hr.disjoint_interior_boundary_not h hk α) hxk hxj
  · refine absurd hxk.1 (h.isGlobular.notMem_boundary_of_mem_interior_boundary ?_ α hxj)
    rw [h.krullDim_boundary hj.le]
    exact_mod_cast hkj

theorem IsGlobular.properBoundary_boundary_le_boundary (hU : P.IsGlobular U) (k : ℕ)
    (α β : Bool) : P.properBoundary (P.boundary U k β) ≤ P.boundary U k α :=
  iSup₂_le fun n hn => by
    have hnk : n < k := by exact_mod_cast hn.trans_le (krullDim_boundary_le U k β)
    rw [boundaryFull, hU n k hnk false β, hU n k hnk true β]
    exact sup_le (hU.boundary_le_boundary hnk _ _) (hU.boundary_le_boundary hnk _ _)

theorem IsSubmoleculeOf.interior_subset_interior (h : P.IsSubmoleculeOf V U)
    (hd : krullDim V = krullDim U) : P.interior V ⊆ P.interior U := fun x hx => by
  refine ⟨h.le hx.1, fun hxU => hx.2 ?_⟩
  obtain ⟨n, hn, α, hxn⟩ := mem_properBoundary.1 hxU
  exact boundary_le_properBoundary (hd ▸ hn) α (h.inf_boundary_le n α ⟨hx.1, hxn⟩)

theorem IsSubmoleculeOf.disjoint_interior_of_inf_le_boundary (h : P.IsSubmoleculeOf V S)
    (hd : krullDim V = krullDim S) (hk : (k : WithBot ℕ∞) < krullDim S)
    (hST : S ⊓ T ≤ P.boundary S k β) : Disjoint (P.interior V) T :=
  disjoint_left.2 fun _ hxV hxT => by
    have hxS := h.interior_subset_interior hd hxV
    exact hxS.2 (boundary_le_properBoundary hk β (hST ⟨hxS.1, hxT⟩))

theorem map_properBoundary (f : P ⟶ Q) [IsInclusion f] (U : LowerSet P) :
    map f (P.properBoundary U) = Q.properBoundary (map f U) := by
  simp only [properBoundary, krullDim_map, map_iSup, map_boundaryFull]

theorem image_interior (f : P ⟶ Q) [IsInclusion f] (U : LowerSet P) :
    f '' P.interior U = Q.interior (map f U) := by
  rw [OGP.interior, OGP.interior, image_sdiff IsInclusion.injective, ← map_properBoundary,
    coe_map, coe_map]

section Decide

variable [Fintype P] [DecidableEq P] [DecidableLE P] (U : LowerSet P) [DecidablePred (· ∈ U)]

instance decidableMemProperBoundary : DecidablePred (· ∈ P.properBoundary U) := fun x =>
  decidable_of_iff (∃ n < P.gradeBound, (n : WithBot ℕ∞) < krullDim U ∧ x ∈ P.boundaryFull U n)
    (by
      refine Iff.trans ?_ mem_properBoundary.symm
      constructor
      · rintro ⟨n, -, hn, hx⟩
        exact ⟨n, hn, mem_boundaryFull.1 hx⟩
      · rintro ⟨n, hn, hx⟩
        refine ⟨n, ?_, hn, mem_boundaryFull.2 hx⟩
        have h := hn.trans_le (krullDim_le_gradeBound U)
        exact_mod_cast h)

instance decidableMemInterior : DecidablePred (· ∈ P.interior U) := fun x =>
  inferInstanceAs (Decidable (x ∈ U ∧ x ∉ P.properBoundary U))

end Decide

theorem properBoundary_dual (J : ℕ → Bool) (U : LowerSet P) :
    (dual P J).properBoundary U = P.properBoundary U := by
  simp only [properBoundary, boundaryFull_dual]

theorem interior_dual (J : ℕ → Bool) (U : LowerSet P) : (dual P J).interior U = P.interior U := by
  rw [OGP.interior, OGP.interior, properBoundary_dual]

end Atoms.Molecule.OGP
