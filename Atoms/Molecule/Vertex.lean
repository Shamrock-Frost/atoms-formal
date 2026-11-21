import Atoms.Molecule.Rewritable.Basic

universe u

open Order

namespace Atoms.Molecule.OGP

variable {P : OGP.{u}} {U W : LowerSet P} {x v : P} {n : ℕ} {α : Bool}

theorem exists_boundary_zero_eq_Iic (hU : IsMoleculeIn P U) (α : Bool) :
    ∃ v, IsMin v ∧ P.boundary U 0 α = LowerSet.Iic v := by
  obtain ⟨m, hm⟩ := hU.exists_krullDim_eq
  refine (hU.boundary 0 α).exists_eq_Iic_of_krullDim_eq_zero ?_
  rw [hU.krullDim_boundary (by rw [hm]; exact_mod_cast m.zero_le) α, Nat.cast_zero]

theorem boundary_Iic_of_isMin (hv : IsMin v) (n : ℕ) (α : Bool) :
    P.boundary (LowerSet.Iic v) n α = LowerSet.Iic v := by
  refine boundary_eq_self ?_ α
  rw [LowerSet.krullDim_Iic, grade_eq_zero_iff.2 hv]
  exact_mod_cast n.zero_le

theorem boundary_zero_eq_Iic_iff (hU : IsMoleculeIn P U) (hv : v ∈ U) (hd : grade ℕ v = 0)
    (α : Bool) : P.boundary U 0 α = LowerSet.Iic v ↔ ∀ e ∈ U, ∀ h : v ⋖ e, P.orient h = α := by
  have hface : v ∈ P.boundary U 0 α ↔ ∀ e ∈ U, ∀ h : v ⋖ e, P.orient h = α := by
    have key : v ∈ P.boundary U 0 α ↔ ∃ z, ((z ∈ U ∧ grade ℕ z = 0 ∧
        ∀ c, c ∈ P.cofaces (!α) z → c ∉ U) ∨ (Maximal (· ∈ U) z ∧ grade ℕ z < 0)) ∧ v ≤ z :=
      mem_boundary.trans (by simp [facesIn, Set.disjoint_left])
    rw [key]
    constructor
    · rintro ⟨z, ⟨-, hz0, hc⟩ | ⟨-, hz⟩, hvz⟩
      · obtain rfl : v = z := GradeOrder.eq_of_le_of_grade_le hvz (by rw [hz0, hd])
        intro e he h
        by_contra hne
        exact hc e ⟨h, Bool.eq_not_iff.2 hne⟩ he
      · exact absurd hz (Nat.not_lt_zero _)
    · exact fun h => ⟨v, Or.inl ⟨hv, hd, fun c ⟨hc, ho⟩ hcU =>
        Bool.not_ne_self α (ho.symm.trans (h c hcU hc))⟩, le_rfl⟩
  rw [← hface]
  obtain ⟨w, hw, hUw⟩ := exists_boundary_zero_eq_Iic hU α
  rw [hUw, LowerSet.mem_Iic_iff]
  constructor
  · intro h
    exact LowerSet.mem_Iic_iff.1 (h ▸ LowerSet.mem_Iic_iff.2 (le_refl v) : v ∈ LowerSet.Iic w)
  · intro h
    rw [(hw h).antisymm h]

theorem isRewritableSubmolecule_Iic_of_maximal (hW : IsMoleculeIn P W) (hr : P.IsRound W)
    (hx : Maximal (· ∈ W) x) : P.IsRewritableSubmolecule (LowerSet.Iic x) W := by
  obtain ⟨n, hn⟩ := hW.exists_krullDim_eq
  exact ⟨hW.Iic_isSubmoleculeOf hx.prop,
    by rw [LowerSet.krullDim_Iic, hr.grade_eq_of_maximal hn hx, hn],
    (hW.isAtomIn_Iic hx.prop).isRound⟩

theorem exists_maximal_boundary_Iic_zero_eq (hW : IsMoleculeIn P W) (γ : Bool) :
    ∃ x, Maximal (· ∈ W) x ∧ P.boundary (LowerSet.Iic x) 0 γ = P.boundary W 0 γ := by
  obtain ⟨w, hwmin, hw⟩ := exists_boundary_zero_eq_Iic hW γ
  have hwW : w ∈ W := boundary_le W 0 γ (hw ▸ LowerSet.mem_Iic_iff.2 le_rfl)
  have hwd : grade ℕ w = 0 := grade_eq_zero_iff.2 hwmin
  obtain ⟨x, hwx, hx⟩ := hW.exists_le_maximal hwW
  refine ⟨x, hx, ?_⟩
  rw [hw, boundary_zero_eq_Iic_iff (hW.isAtomIn_Iic hx.prop).isMoleculeIn
    (LowerSet.mem_Iic_iff.2 hwx) hwd]
  exact fun e he h => (boundary_zero_eq_Iic_iff hW hwW hwd γ).1 hw e
    (W.lower (LowerSet.mem_Iic_iff.1 he) hx.prop) h

theorem exists_maximal_boundary_boundary_Iic_zero_eq (hU : IsMoleculeIn P U) (hr : P.IsRound U)
    (hn : 0 < n) (β γ : Bool) :
    ∃ x, Maximal (· ∈ P.boundary U n β) x ∧ P.boundary (LowerSet.Iic x) 0 γ = P.boundary U 0 γ ∧
      P.IsRewritableSubmolecule (LowerSet.Iic x) (P.boundary U n β) := by
  obtain ⟨x, hx, hb⟩ := exists_maximal_boundary_Iic_zero_eq (hU.boundary n β) γ
  exact ⟨x, hx, hb.trans (hU.isGlobular 0 n hn γ β),
    isRewritableSubmolecule_Iic_of_maximal (hU.boundary n β) (hr.boundary n β) hx⟩

end Atoms.Molecule.OGP
