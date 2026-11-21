import Atoms.Molecule.ShapeData
import Atoms.Molecule.Submolecule
import Atoms.Molecule.Transport

namespace Atoms.Molecule.RoundNotSubmolecule

open OGP

def molecule : FiniteOGP :=
  ⟨⟨[[⟨[], []⟩, ⟨[], []⟩, ⟨[], []⟩],
      [⟨[0], [1]⟩, ⟨[0], [2]⟩, ⟨[2], [1]⟩, ⟨[0], [2]⟩, ⟨[0], [1]⟩, ⟨[0], [2]⟩, ⟨[2], [1]⟩],
      [⟨[0], [1, 2]⟩, ⟨[1], [3]⟩, ⟨[2, 3], [4]⟩, ⟨[1], [5]⟩, ⟨[2], [6]⟩, ⟨[0], [5, 6]⟩,
        ⟨[5], [3]⟩, ⟨[5, 6], [4]⟩],
      [⟨[0, 3, 4], [5]⟩, ⟨[1], [3, 6]⟩, ⟨[2, 6], [4, 7]⟩]]⟩, by decide +kernel⟩

local notation "⟪" n ", " k "⟫" => @id molecule.ogp ⟨⟨n, by decide⟩, ⟨k, by decide⟩⟩

local notation "cl⟪" n ", " k "⟫" => LowerSet.Iic ⟪n, k⟫

abbrev subset : LowerSet molecule.ogp := cl⟪3, 0⟫ ⊔ cl⟪3, 1⟫

private theorem isMoleculeIn_Iic {t : molecule.ogp}
    (hr : (molecule.ogp.restrict (LowerSet.Iic t)).IsRound ⊤)
    (hb : ∀ α, IsMoleculeIn molecule.ogp (lowerClosure (molecule.ogp.faces α t))) :
    IsMoleculeIn molecule.ogp (LowerSet.Iic t) :=
  .atom t (map_incl_top (LowerSet.Iic t) ▸ (isRound_map_iff (incl _) ⊤).2 hr)
    fun α => (bdry_Iic t α).symm ▸ hb α

private theorem isAtomIn_Iic (x : molecule.ogp) : molecule.ogp.IsAtomIn (LowerSet.Iic x) := by
  have h20 := (isMolecule_restrict_iff cl⟪2, 0⟫).1 (by decide +kernel)
  have h21 := (isMolecule_restrict_iff cl⟪2, 1⟫).1 (by decide +kernel)
  have h22 := (isMolecule_restrict_iff cl⟪2, 2⟫).1 (by decide +kernel)
  have h23 := (isMolecule_restrict_iff cl⟪2, 3⟫).1 (by decide +kernel)
  have h24 := (isMolecule_restrict_iff cl⟪2, 4⟫).1 (by decide +kernel)
  have h25 := (isMolecule_restrict_iff cl⟪2, 5⟫).1 (by decide +kernel)
  have h26 := (isMolecule_restrict_iff cl⟪2, 6⟫).1 (by decide +kernel)
  have h27 := (isMolecule_restrict_iff cl⟪2, 7⟫).1 (by decide +kernel)
  have h12 := (h20.isAtomIn_Iic (by decide +kernel : ⟪1, 2⟫ ∈ cl⟪2, 0⟫)).isMoleculeIn
  have h15 := (h23.isAtomIn_Iic (by decide +kernel : ⟪1, 5⟫ ∈ cl⟪2, 3⟫)).isMoleculeIn
  have h31 : IsMoleculeIn molecule.ogp cl⟪3, 1⟫ := isMoleculeIn_Iic (by decide +kernel) <|
    Bool.forall_bool.2 ⟨(by decide +kernel :
      lowerClosure (molecule.ogp.faces false ⟪3, 1⟫) = cl⟪2, 1⟫) ▸ h21, (by decide +kernel :
      molecule.ogp.IsPastingIn 1 cl⟪2, 3⟫ cl⟪2, 6⟫
        (lowerClosure (molecule.ogp.faces true ⟪3, 1⟫))).isMoleculeIn h23 h26⟩
  have h54 := (by decide +kernel : molecule.ogp.IsPastingIn 0 cl⟪1, 5⟫ cl⟪2, 4⟫
    (cl⟪1, 5⟫ ⊔ cl⟪2, 4⟫)).isMoleculeIn h15 h24
  have h32 : IsMoleculeIn molecule.ogp cl⟪3, 2⟫ := isMoleculeIn_Iic (by decide +kernel) <|
    Bool.forall_bool.2 ⟨(by decide +kernel : molecule.ogp.IsPastingIn 1 (cl⟪2, 6⟫ ⊔ cl⟪1, 2⟫)
      cl⟪2, 2⟫ (lowerClosure (molecule.ogp.faces false ⟪3, 2⟫))).isMoleculeIn
      ((by decide +kernel : molecule.ogp.IsPastingIn 0 cl⟪2, 6⟫ cl⟪1, 2⟫
        (cl⟪2, 6⟫ ⊔ cl⟪1, 2⟫)).isMoleculeIn h26 h12) h22,
      (by decide +kernel : molecule.ogp.IsPastingIn 1 (cl⟪1, 5⟫ ⊔ cl⟪2, 4⟫) cl⟪2, 7⟫
        (lowerClosure (molecule.ogp.faces true ⟪3, 2⟫))).isMoleculeIn h54 h27⟩
  have h30 : IsMoleculeIn molecule.ogp cl⟪3, 0⟫ := isMoleculeIn_Iic (by decide +kernel) <|
    Bool.forall_bool.2 ⟨(by decide +kernel : molecule.ogp.IsPastingIn 1
      (cl⟪2, 0⟫ ⊔ cl⟪2, 3⟫ ⊔ cl⟪1, 2⟫) (cl⟪1, 5⟫ ⊔ cl⟪2, 4⟫)
        (lowerClosure (molecule.ogp.faces false ⟪3, 0⟫))).isMoleculeIn
      ((by decide +kernel : molecule.ogp.IsPastingIn 1 cl⟪2, 0⟫ (cl⟪2, 3⟫ ⊔ cl⟪1, 2⟫)
        (cl⟪2, 0⟫ ⊔ cl⟪2, 3⟫ ⊔ cl⟪1, 2⟫)).isMoleculeIn h20
        ((by decide +kernel : molecule.ogp.IsPastingIn 0 cl⟪2, 3⟫ cl⟪1, 2⟫
          (cl⟪2, 3⟫ ⊔ cl⟪1, 2⟫)).isMoleculeIn h23 h12)) h54,
      (by decide +kernel : lowerClosure (molecule.ogp.faces true ⟪3, 0⟫) = cl⟪2, 5⟫) ▸ h25⟩
  obtain h | h | h := (by decide +kernel :
    ∀ y : molecule.ogp, y ≤ ⟪3, 0⟫ ∨ y ≤ ⟪3, 1⟫ ∨ y ≤ ⟪3, 2⟫) x
  exacts [h30.isAtomIn_Iic h, h31.isAtomIn_Iic h, h32.isAtomIn_Iic h]

private theorem isMolecule_molecule : molecule.ogp.IsMolecule := by
  have h (x : molecule.ogp) := (isAtomIn_Iic x).isMoleculeIn
  have hL₁ := (by decide +kernel : molecule.ogp.IsPastingIn 1 cl⟪2, 0⟫ (cl⟪3, 1⟫ ⊔ cl⟪2, 2⟫)
    (cl⟪2, 0⟫ ⊔ cl⟪3, 1⟫ ⊔ cl⟪2, 2⟫)).isMoleculeIn (h _) <|
    (by decide +kernel : molecule.ogp.IsPastingIn 1 (cl⟪3, 1⟫ ⊔ cl⟪1, 2⟫) cl⟪2, 2⟫
      (cl⟪3, 1⟫ ⊔ cl⟪2, 2⟫)).isMoleculeIn
      ((by decide +kernel : molecule.ogp.IsPastingIn 0 cl⟪3, 1⟫ cl⟪1, 2⟫
        (cl⟪3, 1⟫ ⊔ cl⟪1, 2⟫)).isMoleculeIn (h _) (h _)) (h _)
  have hL₂ := (by decide +kernel : molecule.ogp.IsPastingIn 1 (cl⟪2, 0⟫ ⊔ cl⟪2, 3⟫ ⊔ cl⟪1, 2⟫)
    cl⟪3, 2⟫ (cl⟪2, 0⟫ ⊔ cl⟪2, 3⟫ ⊔ cl⟪3, 2⟫)).isMoleculeIn
    ((by decide +kernel : molecule.ogp.IsPastingIn 1 cl⟪2, 0⟫ (cl⟪2, 3⟫ ⊔ cl⟪1, 2⟫)
      (cl⟪2, 0⟫ ⊔ cl⟪2, 3⟫ ⊔ cl⟪1, 2⟫)).isMoleculeIn (h _)
      ((by decide +kernel : molecule.ogp.IsPastingIn 0 cl⟪2, 3⟫ cl⟪1, 2⟫
        (cl⟪2, 3⟫ ⊔ cl⟪1, 2⟫)).isMoleculeIn (h _) (h _))) (h _)
  have hL₃ := (by decide +kernel : molecule.ogp.IsPastingIn 1 cl⟪3, 0⟫ cl⟪2, 7⟫
    (cl⟪3, 0⟫ ⊔ cl⟪2, 7⟫)).isMoleculeIn (h _) (h _)
  exact (by decide +kernel : molecule.ogp.IsPastingIn 2 (cl⟪2, 0⟫ ⊔ cl⟪3, 1⟫ ⊔ cl⟪2, 2⟫)
    (cl⟪3, 2⟫ ⊔ cl⟪3, 0⟫) ⊤).isMoleculeIn hL₁ <|
    (by decide +kernel : molecule.ogp.IsPastingIn 2 (cl⟪2, 0⟫ ⊔ cl⟪2, 3⟫ ⊔ cl⟪3, 2⟫)
      (cl⟪3, 0⟫ ⊔ cl⟪2, 7⟫) (cl⟪3, 2⟫ ⊔ cl⟪3, 0⟫)).isMoleculeIn hL₂ hL₃

private theorem isMoleculeIn_subset : IsMoleculeIn molecule.ogp subset := by
  have h (x : molecule.ogp) := (isAtomIn_Iic x).isMoleculeIn
  exact (by decide +kernel : molecule.ogp.IsPastingIn 2 (cl⟪2, 0⟫ ⊔ cl⟪3, 1⟫ ⊔ cl⟪2, 4⟫)
    (cl⟪3, 0⟫ ⊔ cl⟪2, 6⟫ ⊔ cl⟪1, 6⟫) subset).isMoleculeIn
    ((by decide +kernel : molecule.ogp.IsPastingIn 1 cl⟪2, 0⟫ (cl⟪3, 1⟫ ⊔ cl⟪2, 4⟫)
      (cl⟪2, 0⟫ ⊔ cl⟪3, 1⟫ ⊔ cl⟪2, 4⟫)).isMoleculeIn (h _)
      ((by decide +kernel : molecule.ogp.IsPastingIn 0 cl⟪3, 1⟫ cl⟪2, 4⟫
        (cl⟪3, 1⟫ ⊔ cl⟪2, 4⟫)).isMoleculeIn (h _) (h _)))
    ((by decide +kernel : molecule.ogp.IsPastingIn 1 cl⟪3, 0⟫ (cl⟪2, 6⟫ ⊔ cl⟪1, 6⟫)
      (cl⟪3, 0⟫ ⊔ cl⟪2, 6⟫ ⊔ cl⟪1, 6⟫)).isMoleculeIn (h _)
      ((by decide +kernel : molecule.ogp.IsPastingIn 0 cl⟪2, 6⟫ cl⟪1, 6⟫
        (cl⟪2, 6⟫ ⊔ cl⟪1, 6⟫)).isMoleculeIn (h _) (h _)))

private theorem isRound_subset : molecule.ogp.IsRound subset where
  isGlobular := isMoleculeIn_subset.isGlobular
  inf_boundary_zero _ := by decide +kernel
  inf_boundary_succ n hn := by
    have hb : (molecule.ogp.gradeBound : WithBot ℕ∞) ≤ (3 : ℕ) := by
      exact_mod_cast (by decide +kernel : molecule.ogp.gradeBound ≤ 3)
    have h3 : n + 1 < 3 := by
      exact_mod_cast hn.trans_le ((krullDim_le_gradeBound subset).trans hb)
    obtain rfl | rfl : n = 0 ∨ n = 1 := by omega
    all_goals decide +kernel

private theorem not_isSubmoleculeOf_subset : ¬ molecule.ogp.IsSubmoleculeOf subset ⊤ := by
  intro h
  obtain ⟨Y, ⟨k, α, Z, hp, -, -⟩, hY, hVY⟩ := h.exists_isPastingFactorOf_of_ne fun h =>
    (by decide +kernel : ⟪3, 2⟫ ∉ subset) (h ▸ LowerSet.mem_top)
  obtain ⟨hsup, hinf, -⟩ := (isPastingIn_cond_iff α).1 hp
  have hY32 : ⟪3, 2⟫ ∉ Y := fun h32 => hY (top_le_iff.1 ((by decide +kernel :
    subset ⊔ cl⟪3, 2⟫ = ⊤) ▸ sup_le hVY.le (LowerSet.Iic_le.2 h32)))
  have hZ32 : ⟪3, 2⟫ ∈ Z :=
    (LowerSet.mem_sup_iff.1 (hsup ▸ LowerSet.mem_top : ⟪3, 2⟫ ∈ Z ⊔ Y)).resolve_right hY32
  have hk : (k : WithBot ℕ∞) < 3 := by
    refine (hp.lt_krullDim ?_).trans_le ((krullDim_le_gradeBound _).trans ?_)
    · have hZY : Z ≠ Y := fun h => hY32 (h ▸ hZ32)
      cases α
      · exact hZY.symm
      · exact hZY
    · exact_mod_cast (by decide +kernel : molecule.ogp.gradeBound ≤ 3)
  obtain ⟨⟨hc, hcα⟩, hw32, htV⟩ := (by decide +kernel : ∀ β : Bool,
    cond β ⟪2, 6⟫ ⟪2, 4⟫ ∈ molecule.ogp.faces β (cond β ⟪3, 1⟫ ⟪3, 0⟫) ∧
      cond β ⟪2, 6⟫ ⟪2, 4⟫ ≤ ⟪3, 2⟫ ∧ cond β ⟪3, 1⟫ ⟪3, 0⟫ ∈ subset) α
  have hmem : cond α ⟪2, 6⟫ ⟪2, 4⟫ ∈ Z ⊓ Y :=
    LowerSet.mem_inf_iff.2 ⟨Z.lower hw32 hZ32, Y.lower hc.le (hVY.le htV)⟩
  rw [hinf] at hmem
  have hg : grade ℕ (cond α ⟪2, 6⟫ ⟪2, 4⟫) = 2 := by cases α <;> rfl
  obtain rfl : k = 2 := by
    have := grade_le_of_mem_boundary hmem
    have : k < 3 := by exact_mod_cast hk
    omega
  have hf := (mem_facesIn_of_mem_boundary hmem hg).2.2
  rw [Bool.not_not] at hf
  exact Set.disjoint_left.1 hf ⟨hc, hcα⟩ (hVY.le htV)

theorem isMolecule_and_isRound_and_not_isSubmoleculeOf : molecule.ogp.IsMolecule ∧
    molecule.ogp.IsRound subset ∧ ¬ molecule.ogp.IsSubmoleculeOf subset ⊤ :=
  ⟨isMolecule_molecule, isRound_subset, not_isSubmoleculeOf_subset⟩

end Atoms.Molecule.RoundNotSubmolecule
