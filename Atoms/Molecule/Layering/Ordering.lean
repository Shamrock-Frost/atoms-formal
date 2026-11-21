import Atoms.Molecule.Layering.Boundary
import Atoms.Molecule.Rewritable.Substitution

universe u

open Order Set

namespace Atoms.Molecule.OGP

variable {P : OGP.{u}}

def layerPrefix (U : LowerSet P) (k : ℕ) (L : List (LowerSet P)) : ℕ → LowerSet P
  | 0 => P.boundary U k false
  | j + 1 => prefixUnion L j

section Prefix

variable {k : ℕ} {U : LowerSet P} {L : List (LowerSet P)} (h : IsLayering P k U L)
  (hU : krullDim U = (k + 1 : ℕ))

namespace IsLayering

variable {j : ℕ} (hj : j < L.length) {t : P} (ht : t ∈ L.getD j ⊥) (hdt : grade ℕ t = k + 1)

include h hU hj ht hdt in
private theorem top_spec :
    krullDim (L.getD j ⊥) = (k + 1 : ℕ) ∧ ∀ y ∈ L.getD j ⊥, grade ℕ y = k + 1 → y = t := by
  obtain ⟨t', -, -, hdl, huniq⟩ := h.exists_top_getD hU hj
  obtain rfl : t = t' := huniq t ht hdt
  exact ⟨hdl, huniq⟩

include h in
theorem inf_layerPrefix (hj : j < L.length) :
    L.getD j ⊥ ⊓ layerPrefix U k L j = P.boundary (L.getD j ⊥) k false := by
  cases j with
  | zero =>
    rw [layerPrefix, ← h.boundary_false_getD_zero]
    exact inf_eq_right.2 (boundary_le (L.getD 0 ⊥) k false)
  | succ i => exact (inf_comm _ _).trans (h.isPastingIn i hj).inf_eq_input

include h in
theorem boundary_layerPrefix (hj : j < L.length) :
    P.boundary (layerPrefix U k L j) k true = P.boundary (L.getD j ⊥) k false := by
  cases j with
  | zero =>
    rw [layerPrefix, h.boundary_false_getD_zero]
    exact boundary_eq_self (krullDim_boundary_le U k false) true
  | succ i =>
    exact (h.boundary_true_prefixUnion (by omega)).trans (h.boundary_false_getD_succ hj).symm

include h in
theorem isPastingIn_layerPrefix (hj : j < L.length) :
    P.IsPastingIn k (layerPrefix U k L j) (L.getD j ⊥) (layerPrefix U k L (j + 1)) := by
  cases j with
  | zero =>
    rw [layerPrefix, layerPrefix, ← h.boundary_false_getD_zero]
    exact isPastingIn_boundary_false_self (L.getD 0 ⊥) k
  | succ i => exact h.isPastingIn i hj

include h hU hj ht hdt in
theorem layerPrefix_succ :
    layerPrefix U k L (j + 1) = layerPrefix U k L j ⊔ .Iic t := by
  obtain ⟨hdl, huniq⟩ := h.top_spec hU hj ht hdt
  have hsplit := eq_boundary_sup_Iic_of_unique_top (h.isMoleculeIn_getD hj) ht
    hdt hdl huniq false
  have hsub : P.boundary (L.getD j ⊥) k false ≤ layerPrefix U k L j :=
    h.inf_layerPrefix hj ▸ inf_le_right
  rw [← (h.isPastingIn_layerPrefix hj).sup_eq, hsplit, ← sup_assoc, sup_eq_left.2 hsub]

include h hU hj ht hdt in
theorem Iic_inf_layerPrefix :
    .Iic t ⊓ layerPrefix U k L j = P.boundary (.Iic t) k false := by
  have hct : .Iic t ≤ L.getD j ⊥ := LowerSet.Iic_le.2 ht
  obtain ⟨hdl, huniq⟩ := h.top_spec hU hj ht hdt
  rw [← Iic_inf_boundary_of_unique_top (h.isMoleculeIn_getD hj) ht hdt hdl huniq false,
    ← h.inf_layerPrefix hj, ← inf_assoc, inf_eq_left.2 hct]

include h hU hj ht hdt in
theorem isSubmoleculeOf_boundary_Iic_layerPrefix :
    P.IsSubmoleculeOf (P.boundary (.Iic t) k false)
      (P.boundary (layerPrefix U k L j) k true) := by
  obtain ⟨hdl, huniq⟩ := h.top_spec hU hj ht hdt
  rw [h.boundary_layerPrefix hj]
  exact (isSubmoleculeOf_and_boundary_eq_of_topsAbove_eq (h.isMoleculeIn_getD hj) _ _
    (topsAbove_eq_singleton_of_unique_top ht hdt hdl huniq) false).1

include h hU hj ht hdt in
theorem boundary_layerPrefix_succ :
    (P.boundary (layerPrefix U k L (j + 1)) k true : Set P) =
      ((P.boundary (layerPrefix U k L j) k true : Set P) \
        P.interior (P.boundary (.Iic t) k false)) ∪ P.boundary (.Iic t) k true := by
  obtain ⟨hdl, -⟩ := h.top_spec hU hj ht hdt
  rw [h.boundary_layerPrefix hj, layerPrefix, h.boundary_true_prefixUnion hj]
  exact h.boundary_true_getD_eq hj
    (maximal_mem_of_krullDim_le ht (by rw [hdl, hdt])) (by omega)

include h in
theorem boundary_le_layerPrefix {j : ℕ} (hj : j ≤ L.length) :
    P.boundary U k false ≤ layerPrefix U k L j := by
  cases j with
  | zero => exact le_rfl
  | succ i =>
    change P.boundary U k false ≤ prefixUnion L i
    rw [← h.boundary_false_getD_zero, ← h.boundary_false_prefixUnion (i := i) (by omega)]
    exact boundary_le (prefixUnion L i) k false

include h in
theorem layerPrefix_length : layerPrefix U k L L.length = U := by
  obtain ⟨m, hm⟩ : ∃ m, L.length = m + 1 :=
    ⟨L.length - 1, by have := List.length_pos_iff.2 h.ne_nil; omega⟩
  rw [hm, layerPrefix, ← h.prefixUnion_eq, hm, Nat.add_sub_cancel]

end IsLayering

end Prefix

theorem isPastingAtIn_Iic_of_isPastingIn {k : ℕ} {L : LowerSet P}
    {t : P} (hL : IsMoleculeIn P L) (ht : t ∈ L) (hdt : grade ℕ t = k + 1)
    (hdim : krullDim L = (k + 1 : ℕ)) (huniq : ∀ y ∈ L, grade ℕ y = k + 1 → y = t) (α : Bool)
    {Y R : LowerSet P} (hp : P.IsPastingIn k (cond α Y L) (cond α L Y) R)
    (hY : IsMoleculeIn P Y) :
    P.IsPastingAtIn k α (.Iic t) Y R := by
  have hcL : .Iic t ≤ L := LowerSet.Iic_le.2 ht
  obtain ⟨hR, hYL, hYL'⟩ := (isPastingIn_cond_iff α).1 hp
  rw [inf_comm] at hYL hYL'
  have hinf : .Iic t ⊓ Y = P.boundary (.Iic t) k (!α) := by
    rw [← Iic_inf_boundary_of_unique_top hL ht hdt hdim huniq (!α), ← hYL, ← inf_assoc,
      inf_eq_left.2 hcL]
  refine ⟨(hL.isAtomIn_Iic ht).isMoleculeIn, hY, ?_, hinf, ?_⟩
  · rw [← hR, sup_comm Y L, eq_boundary_sup_Iic_of_unique_top hL ht hdt hdim huniq (!α), ← hYL,
      sup_right_comm, sup_comm (L ⊓ Y) Y, inf_comm L Y, sup_inf_self, sup_comm]
  · rw [hinf, ← hYL', hYL]
    exact (isSubmoleculeOf_and_boundary_eq_of_topsAbove_eq hL _ _
      (topsAbove_eq_singleton_of_unique_top ht hdt hdim huniq) (!α)).1

section Stages

def layerSuffix (U : LowerSet P) (k : ℕ) (L : List (LowerSet P)) (j : ℕ) : LowerSet P :=
  P.boundary U k true ⊔ ((Finset.range L.length).filter (j ≤ ·)).sup (L.getD · ⊥)

variable {k : ℕ} {U : LowerSet P} {L : List (LowerSet P)}

theorem layerSuffix_length : layerSuffix U k L L.length = P.boundary U k true := by
  rw [layerSuffix, Finset.filter_false_of_mem fun i hi => not_le.2 (Finset.mem_range.1 hi),
    Finset.sup_empty, sup_bot_eq]

theorem layerSuffix_of_lt {j : ℕ} (hj : j < L.length) :
    layerSuffix U k L j = L.getD j ⊥ ⊔ layerSuffix U k L (j + 1) := by
  have hsplit : (Finset.range L.length).filter (j ≤ ·) =
      insert j ((Finset.range L.length).filter (j + 1 ≤ ·)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
    omega
  rw [layerSuffix, layerSuffix, hsplit, Finset.sup_insert, sup_left_comm]

variable (h : IsLayering P k U L)
include h

theorem IsLayering.isPastingIn_layerPrefix_layerSuffix {j : ℕ} (hj : j ≤ L.length) :
    P.IsPastingIn k (layerPrefix U k L j) (layerSuffix U k L j) U ∧
      IsMoleculeIn P (layerSuffix U k L j) := by
  obtain ⟨d, hd⟩ : ∃ d, j + d = L.length := ⟨L.length - j, by omega⟩
  induction d generalizing j with
  | zero =>
    obtain rfl : j = L.length := by omega
    rw [layerSuffix_length, h.layerPrefix_length]
    exact ⟨isPastingIn_self_boundary_true U k, h.isMoleculeIn_self.boundary k true⟩
  | succ d ih =>
    have hjl : j < L.length := by omega
    obtain ⟨hX, hS⟩ := ih (j := j + 1) hjl (by omega)
    have hp₁ := (h.isPastingIn_layerPrefix hjl).isPastingIn_right_sup hX
    have hp₂ := (h.isPastingIn_layerPrefix hjl).assoc hX
    rw [← layerSuffix_of_lt hjl] at hp₁ hp₂
    exact ⟨hp₂, hp₁.isMoleculeIn (h.isMoleculeIn_getD hjl) hS⟩

theorem IsLayering.isPastingIn_layerSuffix {j : ℕ} (hj : j < L.length) :
    P.IsPastingIn k (L.getD j ⊥) (layerSuffix U k L (j + 1)) (layerSuffix U k L j) := by
  obtain ⟨hX, -⟩ := h.isPastingIn_layerPrefix_layerSuffix (j := j + 1) hj
  have hp₁ := (h.isPastingIn_layerPrefix hj).isPastingIn_right_sup hX
  rwa [← layerSuffix_of_lt hj] at hp₁

theorem IsLayering.layerSuffix_zero : layerSuffix U k L 0 = U := by
  have hp := (h.isPastingIn_layerPrefix_layerSuffix (j := 0) (Nat.zero_le _)).1
  refine le_antisymm (le_sup_right.trans hp.sup_eq.le) fun x hx => ?_
  obtain ⟨i, hi, hxi⟩ := h.exists_mem_getD hx
  refine Or.inr (Finset.le_sup (f := (L.getD · ⊥)) ?_ hxi)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨hi, Nat.zero_le _⟩

omit h

def layerStage (α : Bool) (U : LowerSet P) (k : ℕ) (L : List (LowerSet P)) (i : ℕ) : LowerSet P :=
  cond α (layerPrefix U k L i) (layerSuffix U k L (L.length - i))

def layerIndex (α : Bool) (L : List (LowerSet P)) (i : ℕ) : ℕ :=
  cond α i (L.length - 1 - i)

theorem layerIndex_lt (α : Bool) {i : ℕ} (hi : i < L.length) : layerIndex α L i < L.length := by
  cases α
  · change L.length - 1 - i < L.length; omega
  · exact hi

theorem layerStage_zero (α : Bool) : layerStage α U k L 0 = P.boundary U k (!α) := by
  cases α
  · exact layerSuffix_length
  · rfl

include h

theorem IsLayering.layerStage_length (α : Bool) : layerStage α U k L L.length = U := by
  cases α
  · change layerSuffix U k L (L.length - L.length) = U
    rw [Nat.sub_self, h.layerSuffix_zero]
  · exact h.layerPrefix_length

theorem IsLayering.isPastingIn_layerStage (α : Bool) {i : ℕ} (hi : i < L.length) :
    P.IsPastingIn k (cond α (layerStage α U k L i) (L.getD (layerIndex α L i) ⊥))
      (cond α (L.getD (layerIndex α L i) ⊥) (layerStage α U k L i))
      (layerStage α U k L (i + 1)) := by
  cases α
  · have e₁ : L.length - i = L.length - 1 - i + 1 := by omega
    have e₂ : L.length - (i + 1) = L.length - 1 - i := by omega
    change P.IsPastingIn k (L.getD (L.length - 1 - i) ⊥) (layerSuffix U k L (L.length - i))
      (layerSuffix U k L (L.length - (i + 1)))
    rw [e₁, e₂]
    exact h.isPastingIn_layerSuffix (by omega)
  · exact h.isPastingIn_layerPrefix hi

theorem IsLayering.isMoleculeIn_layerStage (α : Bool) {i : ℕ} (hi : i ≤ L.length) :
    IsMoleculeIn P (layerStage α U k L i) := by
  cases α
  · exact (h.isPastingIn_layerPrefix_layerSuffix (Nat.sub_le _ _)).2
  · cases i with
    | zero => exact h.isMoleculeIn_self.boundary k false
    | succ i => exact h.isMoleculeIn_prefixUnion (by omega)

theorem IsLayering.boundary_layerStage_not (α : Bool) {i : ℕ} (hi : i ≤ L.length) :
    P.boundary (layerStage α U k L i) k (!α) = P.boundary U k (!α) := by
  cases α
  · exact (h.isPastingIn_layerPrefix_layerSuffix (Nat.sub_le L.length i)).1.boundary_output.symm
  · cases i with
    | zero => exact boundary_eq_self (krullDim_boundary_le U k false) false
    | succ i =>
      change P.boundary (prefixUnion L i) k false = _
      rw [h.boundary_false_prefixUnion (by omega), h.boundary_false_getD_zero, Bool.not_true]

theorem IsLayering.le_krullDim_layerStage (α : Bool) {i : ℕ} (hi : i ≤ L.length)
    (hkU : (k : WithBot ℕ∞) ≤ krullDim U) :
    (k : WithBot ℕ∞) ≤ krullDim (layerStage α U k L i) := by
  rw [← h.isMoleculeIn_self.krullDim_boundary hkU (!α), ← h.boundary_layerStage_not α hi]
  exact LowerSet.krullDim_mono (boundary_le (layerStage α U k L i) k (!α))

end Stages

section Segment

def layerSegment (L : List (LowerSet P)) (q p : ℕ) : LowerSet P :=
  (Finset.range p).sup fun i => L.getD (q + i) ⊥

variable {k : ℕ} {U : LowerSet P} {L : List (LowerSet P)}

@[simp]
theorem layerSegment_zero (q : ℕ) : layerSegment L q 0 = ⊥ := by
  rw [layerSegment, Finset.range_zero, Finset.sup_empty]

theorem layerSegment_succ (q p : ℕ) :
    layerSegment L q (p + 1) = layerSegment L q p ⊔ L.getD (q + p) ⊥ := by
  rw [layerSegment, layerSegment, Finset.range_add_one, Finset.sup_insert, sup_comm]

theorem getD_le_layerSegment {q p i : ℕ} (hi : i < p) :
    L.getD (q + i) ⊥ ≤ layerSegment L q p :=
  Finset.le_sup (f := fun i => L.getD (q + i) ⊥) (Finset.mem_range.2 hi)

theorem layerSuffix_eq_layerSegment_sup {q p : ℕ} (hq : q + p ≤ L.length) :
    layerSuffix U k L q = layerSegment L q p ⊔ layerSuffix U k L (q + p) := by
  induction p with
  | zero => rw [layerSegment_zero, bot_sup_eq, Nat.add_zero]
  | succ p ih =>
    rw [ih (by omega), layerSuffix_of_lt (by omega), layerSegment_succ, sup_assoc,
      Nat.add_assoc]

variable (h : IsLayering P k U L)
include h

theorem IsLayering.layerPrefix_mono {i j : ℕ} (hij : i ≤ j) (hj : j ≤ L.length) :
    layerPrefix U k L i ≤ layerPrefix U k L j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih => exact (ih (by omega)).trans (h.isPastingIn_layerPrefix (by omega)).left_le

theorem IsLayering.isPastingIn_layerPrefix_layerSegment {q p : ℕ} (hp : 0 < p)
    (hq : q + p ≤ L.length) :
    P.IsPastingIn k (layerPrefix U k L q) (layerSegment L q p) (layerPrefix U k L (q + p)) ∧
      IsMoleculeIn P (layerSegment L q p) := by
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
  induction m with
  | zero =>
    rw [layerSegment_succ, layerSegment_zero, bot_sup_eq, Nat.add_zero]
    exact ⟨h.isPastingIn_layerPrefix (by omega), h.isMoleculeIn_getD (by omega)⟩
  | succ m ih =>
    obtain ⟨hA, hW⟩ := ih (by omega) (by omega)
    have hX := h.isPastingIn_layerPrefix (j := q + (m + 1)) (by omega)
    rw [layerSegment_succ]
    exact ⟨hA.assoc hX, (hA.isPastingIn_right_sup hX).isMoleculeIn hW
      (h.isMoleculeIn_getD (by omega))⟩

theorem IsLayering.isPastingIn_layerSegment_layerSuffix {q p : ℕ} (hp : 0 < p)
    (hq : q + p ≤ L.length) :
    P.IsPastingIn k (layerSegment L q p) (layerSuffix U k L (q + p)) (layerSuffix U k L q) := by
  have hA := (h.isPastingIn_layerPrefix_layerSegment hp hq).1
  have hX := (h.isPastingIn_layerPrefix_layerSuffix hq).1
  rw [layerSuffix_eq_layerSegment_sup (U := U) (k := k) hq]
  exact hA.isPastingIn_right_sup hX

theorem IsLayering.isSubmoleculeOf_layerSegment {q p : ℕ} (hp : 0 < p) (hq : q + p ≤ L.length) :
    P.IsSubmoleculeOf (layerSegment L q p) U := by
  obtain ⟨hA, hW⟩ := h.isPastingIn_layerPrefix_layerSegment hp hq
  obtain ⟨hX, hS⟩ := h.isPastingIn_layerPrefix_layerSuffix hq
  have hWX : P.IsPastingFactorOf (layerSegment L q p) (layerPrefix U k L (q + p)) :=
    IsPastingIn.isPastingFactorOf true hW (h.isMoleculeIn_layerStage true (by omega)) hA
  have hXU : P.IsPastingFactorOf (layerPrefix U k L (q + p)) U :=
    IsPastingIn.isPastingFactorOf false (h.isMoleculeIn_layerStage true hq) hS hX
  exact hWX.isSubmoleculeOf.trans hXU.isSubmoleculeOf

theorem IsLayering.layerPrefix_inf_layerSegment {q p : ℕ} (hp : 0 < p) (hq : q + p ≤ L.length) :
    layerPrefix U k L q ⊓ layerSegment L q p = P.boundary (L.getD q ⊥) k false := by
  rw [(h.isPastingIn_layerPrefix_layerSegment hp hq).1.inf_eq_output,
    h.boundary_layerPrefix (by omega)]

theorem IsLayering.boundary_false_layerSegment {q p : ℕ} (hp : 0 < p) (hq : q + p ≤ L.length) :
    P.boundary (layerSegment L q p) k false = P.boundary (L.getD q ⊥) k false := by
  rw [← (h.isPastingIn_layerPrefix_layerSegment hp hq).1.inf_eq_input,
    h.layerPrefix_inf_layerSegment hp hq]

end Segment

theorem isSubstitutionIn_boundary_of_unique_top {L : LowerSet P} {t : P} {k : ℕ}
    (hL : IsMoleculeIn P L) (ht : t ∈ L) (hdt : grade ℕ t = k + 1)
    (hdim : krullDim L = (k + 1 : ℕ)) (huniq : ∀ y ∈ L, grade ℕ y = k + 1 → y = t) :
    P.IsSubstitutionIn (P.boundary L k false) (P.boundary (.Iic t) k false)
      (P.boundary (.Iic t) k true) (P.boundary L k true) := by
  have hT := hL.boundary k false
  have hTself : P.boundary (P.boundary L k false) k true = P.boundary L k false :=
    boundary_eq_self (krullDim_boundary_le L k false) true
  have hinf := Iic_inf_boundary_of_unique_top hL ht hdt hdim huniq false
  have hp : P.IsPastingAtIn k true (.Iic t) (P.boundary L k false) L :=
    isPastingAtIn_Iic_of_isPastingIn hL ht hdt hdim huniq true
      (isPastingIn_boundary_false_self L k) hT
  have hS := (hL.isAtomIn_Iic ht).isRound
  have hdS : krullDim (LowerSet.Iic t) = k + 1 := by
    rw [LowerSet.krullDim_Iic, hdt]; push_cast; rfl
  have hkL : (k : WithBot ℕ∞) ≤ krullDim L := by rw [hdim]; exact_mod_cast k.le_succ
  have h := hp.isSubstitutionIn_boundary hS hdS (by rw [hL.krullDim_boundary hkL false])
  rwa [hTself, hinf] at h

theorem isRound_boundary_true_of_isRound_boundary_false {U : LowerSet P} {k : ℕ}
    (hU : IsMoleculeIn P U) (hdim : krullDim U = (k + 1 : ℕ))
    (h : P.IsRound (P.boundary U k false)) :
    P.IsRound (P.boundary U k true) := by
  obtain ⟨L, hLay⟩ := admitsLayering_pred_krullDim hU hdim (Nat.succ_pos k)
  rw [Nat.add_sub_cancel] at hLay
  have hlen : 0 < L.length := List.length_pos_iff.2 hLay.ne_nil
  have step : ∀ i, i < L.length → P.IsRound (P.boundary (L.getD i ⊥) k false) →
      P.IsRound (P.boundary (L.getD i ⊥) k true) := fun i hi hr => by
    obtain ⟨t, htL, hdt, hdL, hu⟩ := hLay.exists_top_getD hdim hi
    exact (isSubstitutionIn_boundary_of_unique_top (hLay.isMoleculeIn_getD hi) htL hdt hdL
      hu).isRound hr
  have key : ∀ i, i < L.length → P.IsRound (P.boundary (L.getD i ⊥) k true) := by
    intro i
    induction i with
    | zero => exact fun h0 => step 0 h0 (by rw [hLay.boundary_false_getD_zero]; exact h)
    | succ i ih =>
      exact fun hi => step (i + 1) hi (by
        rw [hLay.boundary_false_getD_succ hi]; exact ih (by omega))
  rw [← hLay.boundary_true_getD_last]
  exact key _ (by omega)

end Atoms.Molecule.OGP
