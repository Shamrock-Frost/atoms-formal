import Atoms.Molecule.Rewritable.Substitution

universe u

open Order Set

namespace Atoms.Molecule.OGP

variable {P : OGP.{u}} {k : ℕ} {α : Bool} {S T R V W R' U E : LowerSet P} {x : P}

namespace IsPastingAtIn

theorem subst_left (hp : P.IsPastingAtIn k α S T R) (hs : P.IsSubstitutionIn R V W R')
    (hV : P.IsRewritableSubmolecule V S) (hkS : (k : WithBot ℕ∞) < krullDim S) :
    P.IsSubstitutionIn S V W (hV.complement ⊔ W) ∧
      P.IsPastingAtIn k α (hV.complement ⊔ W) T R' := by
  have hs' := hs.ofIsSubmoleculeOf hp.isSubmoleculeOf_left hV
  have hdisj : Disjoint (P.interior V) (T : Set P) :=
    hV.isSubmoleculeOf.disjoint_interior_of_inf_le_boundary hV.krullDim_eq hkS hp.inf_eq.le
  have hinter := hs.sup_inf_eq_of_disjoint hV hp.right_le hdisj
  refine ⟨hs', hs'.isMoleculeIn, hp.isMoleculeIn_right,
    hs.eq_sup_sup_of_disjoint hp.eq_sup hdisj hV, ?_, ?_⟩
  · rw [hinter, hp.inf_eq, hs'.boundary_eq hkS (!α)]
  · rw [hinter]
    exact hp.isSubmoleculeOf_inf

theorem subst_right (hp : P.IsPastingAtIn k α S T R) (hs : P.IsSubstitutionIn R V W R')
    (hV : P.IsRewritableSubmolecule V T) (hkT : (k : WithBot ℕ∞) < krullDim T) :
    P.IsSubstitutionIn T V W (hV.complement ⊔ W) ∧
      P.IsPastingAtIn k α S (hV.complement ⊔ W) R' := by
  have hs' := hs.ofIsSubmoleculeOf hp.isSubmoleculeOf_right hV
  have hdisj : Disjoint (P.interior V) (S : Set P) :=
    hV.isSubmoleculeOf.disjoint_interior_of_inf_le_boundary hV.krullDim_eq hkT
      ((inf_comm T S).le.trans hp.inf_le_boundary)
  have hinter : S ⊓ (hV.complement ⊔ W) = S ⊓ T := by
    rw [inf_comm, hs.sup_inf_eq_of_disjoint hV hp.left_le hdisj, inf_comm]
  refine ⟨hs', hp.isMoleculeIn_left, hs'.isMoleculeIn, ?_, ?_, ?_⟩
  · rw [hs.eq_sup_sup_of_disjoint (hp.eq_sup.trans (sup_comm S T)) hdisj hV, sup_comm]
  · rw [hinter]
    exact hp.inf_eq
  · rw [hinter, hs'.boundary_eq hkT α]
    exact hp.isSubmoleculeOf_inf

theorem subst_left_self (hp : P.IsPastingAtIn k α S T R) (hs : P.IsSubstitutionIn R S W R')
    (hkS : (k : WithBot ℕ∞) < krullDim S) : P.IsPastingAtIn k α W T R' := by
  obtain ⟨hs', hp'⟩ := hp.subst_left hs ⟨.refl hp.isMoleculeIn_left, rfl, hs.rewritable.isRound⟩ hkS
  rw [hs'.eq_target_of_eq_source rfl] at hp'
  exact hp'

theorem subst_right_self (hp : P.IsPastingAtIn k α S T R) (hs : P.IsSubstitutionIn R T W R')
    (hkT : (k : WithBot ℕ∞) < krullDim T) : P.IsPastingAtIn k α S W R' := by
  obtain ⟨hs', hp'⟩ :=
    hp.subst_right hs ⟨.refl hp.isMoleculeIn_right, rfl, hs.rewritable.isRound⟩ hkT
  rw [hs'.eq_target_of_eq_source rfl] at hp'
  exact hp'

end IsPastingAtIn

private theorem mixed_prologue (h₁ : P.IsPastingAtIn k (!α) V E (V ⊔ E))
    (hkV : (k : WithBot ℕ∞) ≤ krullDim V) (hkE : (k : WithBot ℕ∞) ≤ krullDim E) :
    V ⊓ E = P.boundary V k α ∧ P.IsSubmoleculeOf (P.boundary V k α) (P.boundary E k (!α)) ∧
      ((P.boundary (V ⊔ E) k (!α) : LowerSet P) : Set P) =
        ((P.boundary E k (!α) : Set P) \ P.interior (P.boundary V k α)) ∪
          P.boundary V k (!α) := by
  have hVE : V ⊓ E = P.boundary V k α := by
    have h := h₁.inf_eq
    rwa [Bool.not_not] at h
  refine ⟨hVE, ?_, ?_⟩
  · have h := h₁.isSubmoleculeOf_boundary
    rwa [Bool.not_not] at h
  · rw [h₁.coe_boundary_eq hkV hkE, hVE]

theorem disjoint_boundary_not_interior_boundary (hU : IsMoleculeIn P U) (hr : P.IsRound U)
    (hd : krullDim U = k + 1) (α : Bool) :
    Disjoint (P.boundary U k (!α) : Set P) (P.interior (P.boundary U k α)) :=
  disjoint_left.2 fun x hx hxi => hxi.2
    (hr.inf_boundary_eq_properBoundary hU (by rw [hd]; exact_mod_cast k.lt_succ_self) α ▸
      (⟨hxi.1, hx⟩ : x ∈ P.boundary U k α ⊓ P.boundary U k (!α)))

namespace IsPastingAtIn

theorem assoc_mixed_right (h₁ : P.IsPastingAtIn k (!α) V E (V ⊔ E))
    (h₂ : P.IsPastingAtIn k α (V ⊔ E) U R) (hV : P.IsRound V) (hdV : krullDim V = k + 1)
    (hkE : (k : WithBot ℕ∞) ≤ krullDim E) (hkU : (k : WithBot ℕ∞) ≤ krullDim U) :
    P.IsPastingAtIn k α V U (V ⊔ U) ∧ P.IsPastingAtIn k α E (V ⊔ U) R := by
  have hVm := h₁.isMoleculeIn_left
  have hEm := h₁.isMoleculeIn_right
  have hkV : (k : WithBot ℕ∞) ≤ krullDim V := by rw [hdV]; exact_mod_cast k.le_succ
  obtain ⟨hVE, hsubVE, hb₁⟩ := mixed_prologue h₁ hkV hkE
  have hbf : P.properBoundary (P.boundary V k α) ≤ P.boundary V k (!α) :=
    hVm.isGlobular.properBoundary_boundary_le_boundary k (!α) α
  have hbf' : P.properBoundary (P.boundary V k (!α)) ≤ P.boundary V k α :=
    hVm.isGlobular.properBoundary_boundary_le_boundary k α (!α)
  have hdisj := disjoint_boundary_not_interior_boundary hVm hV hdV (!α)
  rw [Bool.not_not] at hdisj
  have hVEU : (V ⊔ E) ⊓ U = P.boundary (V ⊔ E) k (!α) := h₂.inf_eq
  have hVU : V ⊓ U = P.boundary V k (!α) := by
    refine le_antisymm ?_ ?_
    · rintro x ⟨hxV, hxU⟩
      have hx' : x ∈ ((P.boundary (V ⊔ E) k (!α) : LowerSet P) : Set P) :=
        hVEU ▸ (⟨Or.inl hxV, hxU⟩ : x ∈ (V ⊔ E) ⊓ U)
      rw [hb₁] at hx'
      rcases hx' with ⟨hxE', hxni⟩ | hx1
      · have hxαV : x ∈ P.boundary V k α := hVE ▸ (⟨hxV, boundary_le E k (!α) hxE'⟩ : x ∈ V ⊓ E)
        exact hbf (mem_properBoundary_of_notMem_interior hxαV hxni)
      · exact hx1
    · intro x hx
      refine ⟨boundary_le V k (!α) hx, ?_⟩
      have hx' : x ∈ ((P.boundary (V ⊔ E) k (!α) : LowerSet P) : Set P) := by
        rw [hb₁]
        exact Or.inr hx
      rw [← hVEU] at hx'
      exact hx'.2
  have hsub₂ : P.IsSubmoleculeOf (P.boundary (V ⊔ E) k (!α)) (P.boundary U k α) :=
    h₂.isSubmoleculeOf_boundary
  have h₃ : P.IsPastingAtIn k α V U (V ⊔ U) :=
    ⟨hVm, h₂.isMoleculeIn_right, rfl, hVU, by
      rw [hVU]
      exact h₁.isSubmoleculeOf_boundary_left.trans hsub₂⟩
  have hEVU : E ⊓ (V ⊔ U) = P.boundary E k (!α) := by
    refine le_antisymm ?_ ?_
    · rintro x ⟨hxE, hxV | hxU⟩
      · exact hsubVE.le (hVE ▸ (⟨hxV, hxE⟩ : x ∈ V ⊓ E))
      · have hx' : x ∈ ((P.boundary (V ⊔ E) k (!α) : LowerSet P) : Set P) :=
          hVEU ▸ (⟨Or.inr hxE, hxU⟩ : x ∈ (V ⊔ E) ⊓ U)
        rw [hb₁] at hx'
        rcases hx' with ⟨hx1, -⟩ | hx1
        · exact hx1
        · exact hsubVE.le (hVE ▸ (⟨boundary_le V k (!α) hx1, hxE⟩ : x ∈ V ⊓ E))
    · intro x hx
      refine ⟨boundary_le E k (!α) hx, ?_⟩
      by_cases hxi : x ∈ P.interior (P.boundary V k α)
      · exact Or.inl (boundary_le V k α hxi.1)
      · have hx' : x ∈ ((P.boundary (V ⊔ E) k (!α) : LowerSet P) : Set P) := by
          rw [hb₁]
          exact Or.inl ⟨hx, hxi⟩
        rw [← hVEU] at hx'
        exact Or.inr hx'.2
  have hsubst := h₃.isSubstitutionIn_boundary hV hdV hkU
  rw [hVU] at hsubst
  have hdB : krullDim (P.boundary (V ⊔ E) k (!α)) = k :=
    h₁.isMoleculeIn.krullDim_boundary (hkV.trans (LowerSet.krullDim_mono le_sup_left)) (!α)
  have hVB : P.IsRewritableSubmolecule (P.boundary V k (!α)) (P.boundary (V ⊔ E) k (!α)) :=
    ⟨h₁.isSubmoleculeOf_boundary_left, (hVm.krullDim_boundary hkV (!α)).trans hdB.symm,
      hV.boundary k (!α)⟩
  have hS := hsubst.isSubmoleculeOf_of_isSubmoleculeOf hsub₂ hVB
  have hset : hVB.complement ⊔ P.boundary V k α = P.boundary E k (!α) := by
    refine SetLike.coe_injective ?_
    rw [LowerSet.coe_sup, IsSubmoleculeOf.coe_complement, hb₁]
    refine subset_antisymm ?_ ?_
    · rintro x (⟨hx1 | hx1, hxni⟩ | hx)
      · exact hx1.1
      · exact hsubVE.le (hbf' (mem_properBoundary_of_notMem_interior hx1 hxni))
      · exact hsubVE.le hx
    · intro x hx
      by_cases hxi : x ∈ P.interior (P.boundary V k α)
      · exact Or.inr hxi.1
      · refine Or.inl ⟨Or.inl ⟨hx, hxi⟩, fun hxi' => ?_⟩
        have hxV : x ∈ P.boundary V k α :=
          hVE ▸ (⟨boundary_le V k (!α) hxi'.1, boundary_le E k (!α) hx⟩ : x ∈ V ⊓ E)
        exact disjoint_left.1 hdisj hxV hxi'
  rw [hset] at hS
  refine ⟨h₃, hEm, h₃.isMoleculeIn, ?_, hEVU, by rw [hEVU]; exact hS⟩
  rw [h₂.eq_sup, sup_comm V E, sup_assoc]

theorem assoc_mixed_left (h₁ : P.IsPastingAtIn k (!α) V E (V ⊔ E))
    (h₃ : P.IsPastingAtIn k α V U (V ⊔ U)) (h₂ : P.IsPastingAtIn k α E (V ⊔ U) R)
    (hV : P.IsRound V) (hdV : krullDim V = k + 1) (hkE : (k : WithBot ℕ∞) ≤ krullDim E)
    (hkU : (k : WithBot ℕ∞) ≤ krullDim U) : P.IsPastingAtIn k α (V ⊔ E) U R := by
  have hVm := h₁.isMoleculeIn_left
  have hEm := h₁.isMoleculeIn_right
  have hkV : (k : WithBot ℕ∞) ≤ krullDim V := by rw [hdV]; exact_mod_cast k.le_succ
  obtain ⟨hVE, hsubVE, hb₁⟩ := mixed_prologue h₁ hkV hkE
  have hbf : P.properBoundary (P.boundary V k α) ≤ P.boundary V k (!α) :=
    hVm.isGlobular.properBoundary_boundary_le_boundary k (!α) α
  have hdisj := disjoint_boundary_not_interior_boundary hVm hV hdV α
  have hmeet : (V ⊔ E) ⊓ U = P.boundary (V ⊔ E) k (!α) := by
    refine SetLike.coe_injective ?_
    rw [hb₁]
    refine subset_antisymm ?_ ?_
    · rintro x ⟨hxV | hxE, hxU⟩
      · exact Or.inr (h₃.inf_eq ▸ (⟨hxV, hxU⟩ : x ∈ V ⊓ U))
      · have hxE' : x ∈ P.boundary E k (!α) := h₂.inf_eq ▸ (⟨hxE, Or.inr hxU⟩ : x ∈ E ⊓ (V ⊔ U))
        by_cases hxi : x ∈ P.interior (P.boundary V k α)
        · have hxV : x ∈ P.boundary V k (!α) :=
            h₃.inf_eq ▸ (⟨boundary_le V k α hxi.1, hxU⟩ : x ∈ V ⊓ U)
          exact absurd hxi (disjoint_left.1 hdisj hxV)
        · exact Or.inl ⟨hxE', hxi⟩
    · rintro x (⟨hxE, hxni⟩ | hx)
      · have hxE' : x ∈ E ⊓ (V ⊔ U) := by
          rw [h₂.inf_eq]
          exact hxE
        refine ⟨Or.inr hxE'.1, ?_⟩
        rcases hxE'.2 with hxV | hxU
        · have hxb : x ∈ P.boundary V k α := hVE ▸ (⟨hxV, hxE'.1⟩ : x ∈ V ⊓ E)
          have hxb' : x ∈ P.boundary V k (!α) :=
            hbf (mem_properBoundary_of_notMem_interior hxb hxni)
          have hxVU : x ∈ V ⊓ U := by
            rw [h₃.inf_eq]
            exact hxb'
          exact hxVU.2
        · exact hxU
      · have hxVU : x ∈ V ⊓ U := by
          rw [h₃.inf_eq]
          exact hx
        exact ⟨Or.inl hxVU.1, hxVU.2⟩
  have hsubst := (h₃.isSubstitutionIn_boundary hV hdV hkU).symm
  rw [h₃.inf_eq] at hsubst
  have hB : P.IsSubmoleculeOf (P.boundary E k (!α)) (P.boundary (V ⊔ U) k α) :=
    h₂.isSubmoleculeOf_boundary
  have hdB : krullDim (P.boundary E k (!α)) = k := hEm.krullDim_boundary hkE (!α)
  have hVB : P.IsRewritableSubmolecule (P.boundary V k α) (P.boundary E k (!α)) :=
    ⟨hsubVE, (hVm.krullDim_boundary hkV α).trans hdB.symm, hV.boundary k α⟩
  have hS := hsubst.isSubmoleculeOf_of_isSubmoleculeOf hB hVB
  have hset : hVB.complement ⊔ P.boundary V k (!α) = P.boundary (V ⊔ E) k (!α) :=
    SetLike.coe_injective (by rw [LowerSet.coe_sup, IsSubmoleculeOf.coe_complement, hb₁])
  rw [hset] at hS
  exact ⟨h₁.isMoleculeIn, h₃.isMoleculeIn_right, by rw [h₂.eq_sup, sup_left_comm, ← sup_assoc],
    hmeet, by rw [hmeet]; exact hS⟩

end IsPastingAtIn

end Atoms.Molecule.OGP
