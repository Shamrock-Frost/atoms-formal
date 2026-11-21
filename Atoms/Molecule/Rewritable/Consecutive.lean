import Atoms.Molecule.Layering.Ordering
import Atoms.Molecule.Path

universe u

open Order

namespace Atoms.Molecule.OGP

variable {P : OGP.{u}} {k q : ℕ} {U V : LowerSet P} {L LV : List (LowerSet P)}

section Consecutive

variable (hL : IsLayering P k U L) (hU : krullDim U = (k + 1 : ℕ)) (hLV : IsLayering P k V LV)
  (hV : krullDim V = (k + 1 : ℕ)) (hq : q + LV.length ≤ L.length)
  (htop : ∀ i < LV.length, ∃ t ∈ LV.getD i ⊥, t ∈ L.getD (q + i) ⊥ ∧ grade ℕ t = k + 1)

include hLV hV htop in
private theorem le_layerSegment
    (hbd : P.boundary V k false ≤ P.boundary (L.getD q ⊥) k false) :
    V ≤ layerSegment L q LV.length := by
  have hp : 0 < LV.length := List.length_pos_iff.2 hLV.ne_nil
  suffices ∀ j ≤ LV.length, layerPrefix V k LV j ≤ layerSegment L q LV.length by
    simpa only [hLV.layerPrefix_length] using this _ le_rfl
  intro j
  induction j with
  | zero =>
    intro _
    refine hbd.trans ?_
    have := getD_le_layerSegment (L := L) (q := q) hp
    rw [Nat.add_zero] at this
    exact (boundary_le _ k false).trans this
  | succ j ih =>
    intro hj
    obtain ⟨t, htV, htU, hdt⟩ := htop j hj
    rw [hLV.layerPrefix_succ hV hj htV hdt]
    exact sup_le (ih (by omega)) (LowerSet.Iic_le.2 (getD_le_layerSegment hj htU))

include hL hU hLV hq htop in
private theorem layerSegment_le_sup :
    layerSegment L q LV.length ≤ V ⊔ P.boundary (layerSegment L q LV.length) k false := by
  have hp : 0 < LV.length := List.length_pos_iff.2 hLV.ne_nil
  have hA := (hL.isPastingIn_layerPrefix_layerSegment hp hq).1
  suffices ∀ i ≤ LV.length, layerSegment L q LV.length ⊓ layerPrefix U k L (q + i) ≤
      V ⊔ P.boundary (layerSegment L q LV.length) k false by
    simpa only [inf_eq_left.2 hA.right_le] using this _ le_rfl
  intro i
  induction i with
  | zero =>
    intro _
    rw [Nat.add_zero, inf_comm, ← hA.inf_eq_input]
    exact le_sup_right
  | succ i ih =>
    intro hi
    obtain ⟨t, htV, htU, hdt⟩ := htop i hi
    rw [← Nat.add_assoc, hL.layerPrefix_succ hU (by omega) htU hdt, inf_sup_left]
    exact sup_le (ih (by omega)) (inf_le_right.trans ((LowerSet.Iic_le.2 htV).trans
      ((hLV.le hi).trans le_sup_left)))

include hL hU hLV hV hq htop in
private theorem inf_boundary_layerSegment_le :
    V ⊓ P.boundary (layerSegment L q LV.length) k false ≤ P.boundary V k false := by
  have hp : 0 < LV.length := List.length_pos_iff.2 hLV.ne_nil
  have hA := (hL.isPastingIn_layerPrefix_layerSegment hp hq).1
  have hW : P.boundary (layerSegment L q LV.length) k false ≤ layerPrefix U k L q :=
    hA.inf_eq_input ▸ inf_le_left
  suffices ∀ j ≤ LV.length,
      layerPrefix V k LV j ⊓ P.boundary (layerSegment L q LV.length) k false ≤
        P.boundary V k false by
    simpa only [hLV.layerPrefix_length] using this _ le_rfl
  intro j
  induction j with
  | zero => exact fun _ => inf_le_left
  | succ j ih =>
    intro hj
    obtain ⟨t, htV, htU, hdt⟩ := htop j hj
    have hcl : .Iic t ⊓ layerPrefix U k L (q + j) ≤ layerPrefix V k LV j := by
      rw [hL.Iic_inf_layerPrefix hU (by omega) htU hdt,
        ← hLV.Iic_inf_layerPrefix hV hj htV hdt]
      exact inf_le_right
    have hqj := hL.layerPrefix_mono (Nat.le_add_right q j) (by omega)
    rw [hLV.layerPrefix_succ hV hj htV hdt, inf_sup_right]
    refine sup_le (ih (by omega)) ((le_inf ?_ inf_le_right).trans (ih (by omega)))
    exact (inf_le_inf_left _ (hW.trans hqj)).trans hcl

include hL hU hLV hV hq htop in
theorem isSubmoleculeOf_of_consecutive
    (hbd : P.IsSubmoleculeOf (P.boundary V k false) (P.boundary (L.getD q ⊥) k false)) :
    P.IsSubmoleculeOf V U := by
  have hp : 0 < LV.length := List.length_pos_iff.2 hLV.ne_nil
  have hbW := hL.boundary_false_layerSegment hp hq
  have hVW : V ⊔ P.boundary (layerSegment L q LV.length) k false = layerSegment L q LV.length :=
    le_antisymm
      (sup_le (le_layerSegment hLV hV htop hbd.le) (boundary_le _ k false))
      (layerSegment_le_sup hL hU hLV hq htop)
  have hsup := IsSubmoleculeOf.isSubmoleculeOf_sup (hbW ▸ hbd) hLV.isMoleculeIn_self
    (krullDim_boundary_le _ k false) (inf_boundary_layerSegment_le hL hU hLV hV hq htop)
  rw [hVW] at hsup
  exact hsup.trans (hL.isSubmoleculeOf_layerSegment hp hq)

include hL hU hLV hV hq htop in
theorem isRewritableSubmolecule_of_consecutive (hr : P.IsRound V)
    (hbd : P.IsSubmoleculeOf (P.boundary V k false) (P.boundary (L.getD q ⊥) k false)) :
    P.IsRewritableSubmolecule V U :=
  ⟨isSubmoleculeOf_of_consecutive hL hU hLV hV hq htop hbd, hV.trans hU.symm, hr⟩

end Consecutive

theorem isSubmoleculeOf_of_consecutive_one [Finite P] (hL : IsLayering P 1 U L)
    (hU : krullDim U = (1 + 1 : ℕ)) (hLV : IsLayering P 1 V LV) (hV : krullDim V = (1 + 1 : ℕ))
    (hq : q + LV.length ≤ L.length)
    (htop : ∀ i < LV.length, ∃ t ∈ LV.getD i ⊥, t ∈ L.getD (q + i) ⊥ ∧ grade ℕ t = 2)
    (hbd : P.boundary V 1 false ≤ P.boundary (L.getD q ⊥) 1 false) : P.IsSubmoleculeOf V U := by
  have hp : 0 < LV.length := List.length_pos_iff.2 hLV.ne_nil
  have hVm := hLV.isMoleculeIn_self
  have h1V : ((1 : ℕ) : WithBot ℕ∞) ≤ krullDim V := by rw [hV]; exact_mod_cast Nat.le_succ 1
  have hdV : krullDim (P.boundary V 1 false) = 1 := by
    rw [hVm.krullDim_boundary h1V false, Nat.cast_one]
  refine isSubmoleculeOf_of_consecutive hL hU hLV hV hq htop
    (isSubmoleculeOf_of_le ((hL.isMoleculeIn_getD (by omega)).boundary 1 false) ?_
      (hVm.boundary 1 false) hdV hbd)
  simpa only [Nat.cast_one] using krullDim_boundary_le (L.getD q ⊥) 1 false

inductive IsLayeredOccurrence (P : OGP.{u}) : LowerSet P → LowerSet P → Prop
  | refl {U : LowerSet P} : IsMoleculeIn P U → IsLayeredOccurrence P U U
  | step {k q : ℕ} {U V : LowerSet P} {L LV : List (LowerSet P)} :
      IsLayering P k U L → krullDim U = (k + 1 : ℕ) → IsLayering P k V LV →
      krullDim V = (k + 1 : ℕ) → q + LV.length ≤ L.length →
      (∀ i < LV.length, ∃ t ∈ LV.getD i ⊥, t ∈ L.getD (q + i) ⊥ ∧ grade ℕ t = k + 1) →
      IsLayeredOccurrence P (P.boundary V k false) (P.boundary (L.getD q ⊥) k false) →
      IsLayeredOccurrence P V U

theorem IsLayeredOccurrence.isSubmoleculeOf (h : P.IsLayeredOccurrence V U) :
    P.IsSubmoleculeOf V U := by
  induction h with
  | refl hU => exact .refl hU
  | step hL hU hLV hV hq htop _ ih => exact isSubmoleculeOf_of_consecutive hL hU hLV hV hq htop ih

private theorem boundary_getD_eq_boundary_Iic (hL : IsLayering P 0 U L)
    (hU : krullDim U = (0 + 1 : ℕ)) {j : ℕ} (hj : j < L.length) {t : P} (ht : t ∈ L.getD j ⊥)
    (hdt : grade ℕ t = 0 + 1) :
    P.boundary (L.getD j ⊥) 0 false = P.boundary (.Iic t) 0 false := by
  obtain ⟨t', ht', hdt', hdl, huniq⟩ := hL.exists_top_getD hU hj
  obtain rfl : t = t' := huniq t ht hdt
  have hLm := hL.isMoleculeIn_getD hj
  have hsub := (isSubmoleculeOf_and_boundary_eq_of_topsAbove_eq hLm _ _
    (topsAbove_eq_singleton_of_unique_top ht hdt hdl huniq) false).1
  have h0L : ((0 : ℕ) : WithBot ℕ∞) ≤ krullDim (L.getD j ⊥) := by
    rw [hdl]; exact_mod_cast Nat.zero_le _
  have h0t : ((0 : ℕ) : WithBot ℕ∞) ≤ krullDim (LowerSet.Iic t) := by
    rw [LowerSet.krullDim_Iic]; exact_mod_cast Nat.zero_le _
  obtain ⟨x, hx, hLx⟩ := (hLm.boundary 0 false).exists_eq_Iic_of_krullDim_eq_zero
    (by rw [hLm.krullDim_boundary h0L false, Nat.cast_zero])
  obtain ⟨y, -, hty⟩ := hsub.isMoleculeIn.exists_eq_Iic_of_krullDim_eq_zero
    (by rw [((hLm.isAtomIn_Iic ht).isMoleculeIn).krullDim_boundary h0t false, Nat.cast_zero])
  have hyx : y ≤ x := LowerSet.Iic_le.1 (hty ▸ hLx ▸ hsub.le)
  rw [hLx, hty, le_antisymm hyx (hx hyx)]

theorem IsLayeredOccurrence.step_zero (hL : IsLayering P 0 U L) (hU : krullDim U = (0 + 1 : ℕ))
    (hLV : IsLayering P 0 V LV) (hV : krullDim V = (0 + 1 : ℕ)) (hq : q + LV.length ≤ L.length)
    (htop : ∀ i < LV.length, ∃ t ∈ LV.getD i ⊥, t ∈ L.getD (q + i) ⊥ ∧ grade ℕ t = 0 + 1) :
    P.IsLayeredOccurrence V U := by
  have hp : 0 < LV.length := List.length_pos_iff.2 hLV.ne_nil
  obtain ⟨t, htV, htU, hdt⟩ := htop 0 hp
  rw [Nat.add_zero] at htU
  have hb : P.boundary V 0 false = P.boundary (L.getD q ⊥) 0 false := by
    rw [← hLV.boundary_false_getD_zero, boundary_getD_eq_boundary_Iic hLV hV hp htV hdt,
      boundary_getD_eq_boundary_Iic hL hU (by omega) htU hdt]
  refine .step hL hU hLV hV hq htop ?_
  rw [hb]
  exact .refl ((hL.isMoleculeIn_getD (by omega)).boundary 0 false)

end Atoms.Molecule.OGP
