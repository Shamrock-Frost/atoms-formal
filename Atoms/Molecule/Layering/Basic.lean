import Mathlib.Data.List.GetD
import Mathlib.Data.Set.Card
import Atoms.Molecule.Pasting.Basic

universe u

open Order

namespace Atoms.Molecule.OGP

variable {P : OGP.{u}}

def prefixUnion (L : List (LowerSet P)) : ℕ → LowerSet P
  | 0 => L.getD 0 ⊥
  | i + 1 => prefixUnion L i ⊔ L.getD (i + 1) ⊥

theorem prefixUnion_zero (L : List (LowerSet P)) : prefixUnion L 0 = L.getD 0 ⊥ :=
  rfl

theorem mem_prefixUnion_iff {L : List (LowerSet P)} {x : P} {m : ℕ} :
    x ∈ prefixUnion L m ↔ ∃ i ≤ m, x ∈ L.getD i ⊥ := by
  induction m with
  | zero =>
    simp only [prefixUnion_zero, Nat.le_zero, exists_eq_left]
  | succ m ih =>
    rw [prefixUnion, LowerSet.mem_sup_iff, ih]
    simp only [← Nat.lt_add_one_iff, Nat.exists_lt_succ_right]

theorem getD_le_prefixUnion {L : List (LowerSet P)} {i m : ℕ} (him : i ≤ m) :
    L.getD i ⊥ ≤ prefixUnion L m :=
  fun _ hx => mem_prefixUnion_iff.2 ⟨i, him, hx⟩

theorem prefixUnion_le_prefixUnion {L : List (LowerSet P)} {i m : ℕ} (h : i ≤ m) :
    prefixUnion L i ≤ prefixUnion L m :=
  (monotone_nat_of_le_succ fun _ => le_sup_left) h

theorem getD_mem_of_lt_length {L : List (LowerSet P)} {i : ℕ} (hi : i < L.length) :
    L.getD i ⊥ ∈ L :=
  List.getD_eq_getElem L ⊥ hi ▸ List.getElem_mem hi

theorem exists_getD_eq_of_mem {L : List (LowerSet P)} {Y : LowerSet P} (hY : Y ∈ L) :
    ∃ i, i < L.length ∧ L.getD i ⊥ = Y := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hY
  exact ⟨i, hi, List.getD_eq_getElem L ⊥ hi⟩

theorem getD_map_of_lt {L : List (LowerSet P)} {f : LowerSet P → LowerSet P}
    {i : ℕ} (hi : i < L.length) : (L.map f).getD i ⊥ = f (L.getD i ⊥) := by
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map]

theorem prefixUnion_map {L : List (LowerSet P)} {f : LowerSet P → LowerSet P}
    (hf : ∀ A B, f (A ⊔ B) = f A ⊔ f B) {i : ℕ} (hi : i < L.length) :
    prefixUnion (L.map f) i = f (prefixUnion L i) := by
  induction i with
  | zero => exact getD_map_of_lt hi
  | succ i ih =>
    rw [prefixUnion, prefixUnion, ih (by omega), getD_map_of_lt hi, hf]

theorem prefixUnion_append_of_lt {LV LW : List (LowerSet P)} {i : ℕ}
    (hi : i < LV.length) : prefixUnion (LV ++ LW) i = prefixUnion LV i := by
  induction i with
  | zero => exact List.getD_append _ _ _ _ hi
  | succ i ih => rw [prefixUnion, prefixUnion, ih (by omega), List.getD_append _ _ _ _ hi]

theorem prefixUnion_append_length_add {LV LW : List (LowerSet P)} (hV : LV ≠ []) (j : ℕ) :
    prefixUnion (LV ++ LW) (LV.length + j) =
      prefixUnion LV (LV.length - 1) ⊔ prefixUnion LW j := by
  have hpos : 0 < LV.length := List.length_pos_iff.2 hV
  induction j with
  | zero =>
    have e : LV.length + 0 = (LV.length - 1) + 1 := by omega
    have hg : (LV ++ LW).getD (LV.length - 1 + 1) ⊥ = LW.getD 0 ⊥ := by
      rw [← e, List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]
    rw [e, prefixUnion.eq_2,
      prefixUnion_append_of_lt (LV := LV) (LW := LW) (i := LV.length - 1) (by omega), hg]
    rfl
  | succ j ih =>
    have he : LV.length + j + 1 - LV.length = j + 1 := by omega
    have hg : (LV ++ LW).getD (LV.length + j + 1) ⊥ = LW.getD (j + 1) ⊥ := by
      rw [List.getD_append_right _ _ _ _ (by omega), he]
    rw [← Nat.add_assoc, prefixUnion, ih, hg, prefixUnion, sup_assoc]

structure IsSuccessivePasting (P : OGP.{u}) (k : ℕ) (U : LowerSet P)
    (L : List (LowerSet P)) : Prop where
  ne_nil : L ≠ []
  isMoleculeIn : ∀ V ∈ L, IsMoleculeIn P V
  prefixUnion_eq : prefixUnion L (L.length - 1) = U
  isPastingIn : ∀ i, i + 1 < L.length →
    P.IsPastingIn k (prefixUnion L i) (L.getD (i + 1) ⊥) (prefixUnion L (i + 1))

structure IsLayering (P : OGP.{u}) (k : ℕ) (U : LowerSet P)
    (L : List (LowerSet P)) : Prop extends IsSuccessivePasting P k U L where
  existsUnique_top : ∀ V ∈ L, ∃! t : P, Maximal (· ∈ V) t ∧ k < grade ℕ t

def AdmitsLayering (P : OGP.{u}) (k : ℕ) (U : LowerSet P) : Prop :=
  ∃ L : List (LowerSet P), IsLayering P k U L

theorem IsSuccessivePasting.le {k : ℕ} {U : LowerSet P} {L : List (LowerSet P)}
    (h : IsSuccessivePasting P k U L) {i : ℕ} (hi : i < L.length) : L.getD i ⊥ ≤ U :=
  h.prefixUnion_eq ▸ getD_le_prefixUnion (by omega)

theorem IsSuccessivePasting.prefixUnion_le {k : ℕ} {U : LowerSet P}
    {L : List (LowerSet P)} (h : IsSuccessivePasting P k U L) {i : ℕ}
    (hi : i < L.length) : prefixUnion L i ≤ U :=
  h.prefixUnion_eq ▸ prefixUnion_le_prefixUnion (by omega)

variable (P) in
def topsAbove (U : LowerSet P) (k : ℕ) : Set P :=
  {t | Maximal (· ∈ U) t ∧ k < grade ℕ t}

@[simp] theorem mem_topsAbove {U : LowerSet P} {k : ℕ} {t : P} :
    t ∈ P.topsAbove U k ↔ Maximal (· ∈ U) t ∧ k < grade ℕ t :=
  Iff.rfl

theorem topsAbove_subset_of_le {U : LowerSet P} {j k : ℕ} (hjk : j ≤ k) :
    P.topsAbove U k ⊆ P.topsAbove U j := fun _ ⟨hm, hk⟩ =>
  ⟨hm, hjk.trans_lt hk⟩

theorem topsAbove_eq_empty_of_krullDim_le {U : LowerSet P} {k : ℕ} (h : krullDim U ≤ k) :
    P.topsAbove U k = ∅ :=
  Set.eq_empty_of_forall_notMem fun t ⟨hm, hk⟩ =>
    (krullDim_le_coe_iff.1 h ⟨t, hm.prop⟩).not_gt hk

theorem IsMoleculeIn.exists_subsingleton_topsAbove {U : LowerSet P} (hU : IsMoleculeIn P U) :
    ∃ j, (P.topsAbove U j).Subsingleton :=
  let ⟨n, hn⟩ := hU.exists_krullDim_eq
  ⟨n, by rw [topsAbove_eq_empty_of_krullDim_le hn.le]; exact Set.subsingleton_empty⟩

variable (P) in
def layeringDim (U : LowerSet P) [DecidablePred fun j => (P.topsAbove U j).Subsingleton]
    (hU : IsMoleculeIn P U) : ℕ :=
  Nat.find hU.exists_subsingleton_topsAbove

theorem subsingleton_topsAbove_layeringDim {U : LowerSet P}
    [DecidablePred fun j => (P.topsAbove U j).Subsingleton] (hU : IsMoleculeIn P U) :
    (P.topsAbove U (P.layeringDim U hU)).Subsingleton :=
  Nat.find_spec hU.exists_subsingleton_topsAbove

theorem layeringDim_le_iff {U : LowerSet P}
    [DecidablePred fun j => (P.topsAbove U j).Subsingleton] (hU : IsMoleculeIn P U) {j : ℕ} :
    P.layeringDim U hU ≤ j ↔ (P.topsAbove U j).Subsingleton :=
  ⟨fun hle => (subsingleton_topsAbove_layeringDim hU).anti (topsAbove_subset_of_le hle),
    Nat.find_min' hU.exists_subsingleton_topsAbove⟩

theorem lt_layeringDim_iff {U : LowerSet P}
    [DecidablePred fun j => (P.topsAbove U j).Subsingleton] (hU : IsMoleculeIn P U) {j : ℕ} :
    j < P.layeringDim U hU ↔ (P.topsAbove U j).Nontrivial := by
  rw [← not_le, layeringDim_le_iff hU, Set.not_subsingleton_iff]

theorem layeringDim_le_of_krullDim_le {U : LowerSet P}
    [DecidablePred fun j => (P.topsAbove U j).Subsingleton] (hU : IsMoleculeIn P U) {n : ℕ}
    (h : krullDim U ≤ n) : P.layeringDim U hU ≤ n :=
  (layeringDim_le_iff hU).2
    (by rw [topsAbove_eq_empty_of_krullDim_le h]; exact Set.subsingleton_empty)

section Layers

variable {k : ℕ} {U : LowerSet P} {L : List (LowerSet P)}

theorem IsSuccessivePasting.isMoleculeIn_getD
    (h : IsSuccessivePasting P k U L) {i : ℕ} (hi : i < L.length) :
    IsMoleculeIn P (L.getD i ⊥) :=
  h.isMoleculeIn _ (getD_mem_of_lt_length hi)

theorem IsSuccessivePasting.isMoleculeIn_prefixUnion (h : IsSuccessivePasting P k U L) {i : ℕ}
    (hi : i < L.length) : IsMoleculeIn P (prefixUnion L i) := by
  induction i with
  | zero => exact h.isMoleculeIn_getD hi
  | succ i ih =>
    exact (h.isPastingIn i hi).isMoleculeIn (ih (by omega)) (h.isMoleculeIn_getD hi)

theorem IsSuccessivePasting.isMoleculeIn_self
    (h : IsSuccessivePasting P k U L) : IsMoleculeIn P U := by
  have hpos : 0 < L.length := List.length_pos_iff.2 h.ne_nil
  rw [← h.prefixUnion_eq]
  exact h.isMoleculeIn_prefixUnion (by omega)

theorem IsSuccessivePasting.exists_mem_getD
    (h : IsSuccessivePasting P k U L) {x : P} (hx : x ∈ U) :
    ∃ i, i < L.length ∧ x ∈ L.getD i ⊥ := by
  have hpos : 0 < L.length := List.length_pos_iff.2 h.ne_nil
  rw [← h.prefixUnion_eq, mem_prefixUnion_iff] at hx
  obtain ⟨i, hi, hx⟩ := hx
  exact ⟨i, by omega, hx⟩

theorem IsSuccessivePasting.boundary_false_prefixUnion (h : IsSuccessivePasting P k U L) {i : ℕ}
    (hi : i < L.length) :
    P.boundary (prefixUnion L i) k false = P.boundary (L.getD 0 ⊥) k false := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [(h.isPastingIn i hi).boundary_input, ih (by omega)]

theorem IsSuccessivePasting.boundary_true_prefixUnion (h : IsSuccessivePasting P k U L) {i : ℕ}
    (hi : i < L.length) :
    P.boundary (prefixUnion L i) k true = P.boundary (L.getD i ⊥) k true := by
  cases i with
  | zero => rfl
  | succ i => exact (h.isPastingIn i hi).boundary_output

theorem IsSuccessivePasting.prefixUnion_inf_getD_succ_eq_boundary_true
    (h : IsSuccessivePasting P k U L) {i : ℕ} (hi : i + 1 < L.length) :
    prefixUnion L i ⊓ L.getD (i + 1) ⊥ = P.boundary (L.getD i ⊥) k true := by
  rw [(h.isPastingIn i hi).inf_eq_output, h.boundary_true_prefixUnion (by omega)]

theorem IsSuccessivePasting.boundary_false_getD_succ (h : IsSuccessivePasting P k U L) {i : ℕ}
    (hi : i + 1 < L.length) :
    P.boundary (L.getD (i + 1) ⊥) k false = P.boundary (L.getD i ⊥) k true := by
  rw [← (h.isPastingIn i hi).inf_eq_input, h.prefixUnion_inf_getD_succ_eq_boundary_true hi]

theorem IsSuccessivePasting.boundary_false_getD_zero (h : IsSuccessivePasting P k U L) :
    P.boundary (L.getD 0 ⊥) k false = P.boundary U k false := by
  have hlen : 0 < L.length := List.length_pos_iff.2 h.ne_nil
  rw [← h.boundary_false_prefixUnion (i := L.length - 1) (by omega), h.prefixUnion_eq]

theorem IsSuccessivePasting.boundary_true_getD_last (h : IsSuccessivePasting P k U L) :
    P.boundary (L.getD (L.length - 1) ⊥) k true = P.boundary U k true := by
  have hlen : 0 < L.length := List.length_pos_iff.2 h.ne_nil
  rw [← h.boundary_true_prefixUnion (by omega), h.prefixUnion_eq]

theorem IsSuccessivePasting.inf_le_boundary_false
    (h : IsSuccessivePasting P k U L) {i j : ℕ} (hij : i < j)
    (hj : j < L.length) : L.getD i ⊥ ⊓ L.getD j ⊥ ≤ P.boundary (L.getD j ⊥) k false := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  rw [← (h.isPastingIn m hj).inf_eq_input]
  exact inf_le_inf_right _ (getD_le_prefixUnion (by omega))

theorem IsSuccessivePasting.inf_le_boundary_true
    (h : IsSuccessivePasting P k U L) {i j : ℕ} (hij : i < j)
    (hj : j < L.length) : L.getD i ⊥ ⊓ L.getD j ⊥ ≤ P.boundary (L.getD i ⊥) k true := by
  obtain ⟨d, rfl⟩ : ∃ d, j = i + 1 + d := ⟨j - (i + 1), by omega⟩
  induction d with
  | zero =>
    rw [← h.prefixUnion_inf_getD_succ_eq_boundary_true hj]
    exact inf_le_inf_right _ (getD_le_prefixUnion le_rfl)
  | succ d ih =>
    have hj' : i + 1 + d + 1 < L.length := by omega
    intro x hx
    have hprev : x ∈ P.boundary (L.getD (i + 1 + d) ⊥) k true := by
      rw [← h.prefixUnion_inf_getD_succ_eq_boundary_true hj']
      exact ⟨getD_le_prefixUnion (by omega) hx.1, hx.2⟩
    exact ih (by omega) (by omega) ⟨hx.1, boundary_le _ k true hprev⟩

theorem IsSuccessivePasting.inf_eq (h : IsSuccessivePasting P k U L) {i j : ℕ} (hij : i < j)
    (hj : j < L.length) :
    L.getD i ⊥ ⊓ L.getD j ⊥ =
      P.boundary (L.getD i ⊥) k true ⊓ P.boundary (L.getD j ⊥) k false :=
  le_antisymm (le_inf (h.inf_le_boundary_true hij hj) (h.inf_le_boundary_false hij hj))
    (inf_le_inf (boundary_le _ k true) (boundary_le _ k false))

theorem IsSuccessivePasting.grade_le_of_mem_of_mem
    (h : IsSuccessivePasting P k U L) {i j : ℕ} (hij : i ≠ j)
    (hi : i < L.length) (hj : j < L.length) {x : P} (hxi : x ∈ L.getD i ⊥)
    (hxj : x ∈ L.getD j ⊥) : grade ℕ x ≤ k := by
  rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
  · exact grade_le_of_mem_boundary (h.inf_le_boundary_true hlt hj ⟨hxi, hxj⟩)
  · exact grade_le_of_mem_boundary (h.inf_le_boundary_true hlt hi ⟨hxj, hxi⟩)

theorem IsSuccessivePasting.eq_of_mem_of_mem
    (h : IsSuccessivePasting P k U L) {i j : ℕ} (hi : i < L.length)
    (hj : j < L.length) {x : P} (hk : k < grade ℕ x) (hxi : x ∈ L.getD i ⊥)
    (hxj : x ∈ L.getD j ⊥) : i = j := by
  by_contra hij
  have := h.grade_le_of_mem_of_mem hij hi hj hxi hxj
  omega

theorem IsSuccessivePasting.existsUnique_mem_of_maximal
    (h : IsSuccessivePasting P k U L) {t : P}
    (ht : Maximal (· ∈ U) t) (hk : k < grade ℕ t) : ∃! i : ℕ, i < L.length ∧ t ∈ L.getD i ⊥ := by
  obtain ⟨i, hi, hti⟩ := h.exists_mem_getD ht.prop
  exact ⟨i, ⟨hi, hti⟩, fun j ⟨hj, htj⟩ => h.eq_of_mem_of_mem hj hi hk htj hti⟩

theorem IsSuccessivePasting.maximal_of_maximal (h : IsSuccessivePasting P k U L) {i : ℕ}
    (hi : i < L.length) {t : P} (ht : Maximal (· ∈ L.getD i ⊥) t) (hk : k < grade ℕ t) :
    Maximal (· ∈ U) t := by
  refine ⟨h.le hi ht.prop, fun y hy hty => ?_⟩
  obtain ⟨j, hj, hyj⟩ := h.exists_mem_getD hy
  have htj : t ∈ L.getD j ⊥ := (L.getD j ⊥).lower hty hyj
  obtain rfl := h.eq_of_mem_of_mem hi hj hk ht.prop htj
  exact ht.2 hyj hty

theorem topsAbove_sub_one_of_krullDim_eq {n : ℕ} (hU : krullDim U = n) (hpos : 0 < n) :
    P.topsAbove U (n - 1) = {x ∈ U | grade ℕ x = n} := by
  ext x
  simp only [mem_topsAbove, Set.mem_ofPred_eq]
  refine ⟨fun ⟨hx, hd⟩ => ⟨hx.prop, le_antisymm (krullDim_le_coe_iff.1 hU.le ⟨x, hx.prop⟩)
    (by omega)⟩, fun ⟨hx, hd⟩ => ⟨⟨hx, fun y hy hxy => ?_⟩, by omega⟩⟩
  exact (GradeOrder.eq_of_le_of_grade_le hxy (hd ▸ krullDim_le_coe_iff.1 hU.le ⟨y, hy⟩)).ge

theorem layeringDim_eq_of_krullDim_eq_iff (hU : IsMoleculeIn P U)
    [DecidablePred fun j => (P.topsAbove U j).Subsingleton] {n : ℕ} (hn : krullDim U = n)
    (hpos : 0 < n) : P.layeringDim U hU = n ↔ {x ∈ U | grade ℕ x = n}.Nontrivial := by
  rw [← topsAbove_sub_one_of_krullDim_eq hn hpos, ← lt_layeringDim_iff hU]
  have := layeringDim_le_of_krullDim_le hU hn.le
  omega

theorem IsMoleculeIn.grade_pos_of_maximal (hU : IsMoleculeIn P U) (hpos : 0 < krullDim U)
    {t : P} (ht : Maximal (· ∈ U) t) : 0 < grade ℕ t := by
  induction hU with
  | point x hx =>
    rw [LowerSet.krullDim_Iic_of_isMin hx] at hpos
    exact absurd hpos (lt_irrefl _)
  | atom s _ _ _ =>
    obtain rfl : t = s := ht.eq_of_le (le_refl s) ht.prop
    rw [LowerSet.krullDim_Iic] at hpos
    exact_mod_cast hpos
  | paste j V W U hp _ _ hj ihV ihW =>
    obtain ⟨htVW, hV', hW'⟩ := LowerSet.maximal_mem_sup_iff.1 (hp.sup_eq.symm ▸ ht)
    have h0 : (0 : WithBot ℕ∞) ≤ j := by exact_mod_cast Nat.zero_le j
    rcases htVW with htV | htW
    · exact ihV (h0.trans_lt (hj.trans_le (min_le_left _ _))) (hV' htV)
    · exact ihW (h0.trans_lt (hj.trans_le (min_le_right _ _))) (hW' htW)

theorem layeringDim_eq_zero_iff (hU : IsMoleculeIn P U)
    [DecidablePred fun j => (P.topsAbove U j).Subsingleton] :
    P.layeringDim U hU = 0 ↔ P.IsAtomIn U := by
  obtain ⟨n, hn⟩ := hU.exists_krullDim_eq
  constructor
  · intro h0
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · obtain ⟨x, -, rfl⟩ := hU.exists_eq_Iic_of_krullDim_eq_zero hn
      exact ⟨hU, x, rfl⟩
    · have hsub : (P.topsAbove U 0).Subsingleton := (layeringDim_le_iff hU).1 h0.le
      have hpos' : 0 < krullDim U := by rw [hn]; exact_mod_cast hpos
      have htop : ∀ z, Maximal (· ∈ U) z → z ∈ P.topsAbove U 0 := fun z hz =>
        ⟨hz, hU.grade_pos_of_maximal hpos' hz⟩
      obtain ⟨x, hx⟩ := hU.nonempty
      obtain ⟨t, -, ht⟩ := hU.exists_le_maximal hx
      refine ⟨hU, t, le_antisymm (fun y hy => ?_) (LowerSet.Iic_le.2 ht.prop)⟩
      obtain ⟨z, hyz, hz⟩ := hU.exists_le_maximal hy
      rw [hsub (htop z hz) (htop t ht)] at hyz
      exact hyz
  · rintro ⟨-, t, rfl⟩
    refine Nat.le_zero.1 ((layeringDim_le_iff hU).2 fun a ha b hb => ?_)
    rw [ha.1.eq_of_le (le_refl t) ha.1.prop, hb.1.eq_of_le (le_refl t) hb.1.prop]

theorem IsLayering.existsUnique_top_getD (h : IsLayering P k U L) {i : ℕ} (hi : i < L.length) :
    ∃! t : P, Maximal (· ∈ L.getD i ⊥) t ∧ k < grade ℕ t :=
  h.existsUnique_top _ (getD_mem_of_lt_length hi)

theorem IsLayering.exists_top_getD (h : IsLayering P k U L) (hU : krullDim U = (k + 1 : ℕ)) {i : ℕ}
    (hi : i < L.length) :
    ∃ t ∈ L.getD i ⊥, grade ℕ t = k + 1 ∧ krullDim (L.getD i ⊥) = (k + 1 : ℕ) ∧
      ∀ y ∈ L.getD i ⊥, grade ℕ y = k + 1 → y = t := by
  obtain ⟨t, ⟨htM, htk⟩, hu⟩ := h.existsUnique_top_getD hi
  have hle : krullDim (L.getD i ⊥) ≤ (k + 1 : ℕ) :=
    (LowerSet.krullDim_mono (h.le hi)).trans hU.le
  have h1 : grade ℕ t ≤ k + 1 := krullDim_le_coe_iff.1 hle ⟨t, htM.prop⟩
  have htd : grade ℕ t = k + 1 := by omega
  have h2 : ((k + 1 : ℕ) : WithBot ℕ∞) ≤ krullDim (L.getD i ⊥) :=
    htd ▸ grade_le_krullDim (⟨t, htM.prop⟩ : ↥(L.getD i ⊥))
  refine ⟨t, htM.prop, htd, le_antisymm hle h2, fun y hy hyd => ?_⟩
  refine hu y ⟨⟨hy, fun z hz hyz => ?_⟩, by omega⟩
  exact (GradeOrder.eq_of_le_of_grade_le hyz (hyd ▸ krullDim_le_coe_iff.1 hle ⟨z, hz⟩)).ge

theorem IsLayering.card_topsAbove (h : IsLayering P k U L) :
    (P.topsAbove U k).encard = L.length := by
  classical
  let idx : P → ℕ := fun t => if ht : t ∈ U then (h.exists_mem_getD ht).choose else 0
  have hidx : ∀ t ∈ U, idx t < L.length ∧ t ∈ L.getD (idx t) ⊥ := fun t ht => by
    simp only [idx, dif_pos ht]
    exact (h.exists_mem_getD ht).choose_spec
  have himage : idx '' P.topsAbove U k = {i | i < L.length} := by
    ext i
    simp only [Set.mem_image, Set.mem_ofPred_eq]
    refine ⟨by rintro ⟨t, ht, rfl⟩; exact (hidx t ht.1.prop).1, fun hi => ?_⟩
    obtain ⟨t, ⟨ht, hk⟩, -⟩ := h.existsUnique_top_getD hi
    have htU := h.maximal_of_maximal hi ht hk
    exact ⟨t, ⟨htU, hk⟩,
      h.eq_of_mem_of_mem (hidx t htU.prop).1 hi hk (hidx t htU.prop).2 ht.prop⟩
  have hinj : Set.InjOn idx (P.topsAbove U k) := fun a ha b hb hab => by
    obtain ⟨hia, haL⟩ := hidx a ha.1.prop
    obtain ⟨-, hbL⟩ := hidx b hb.1.prop
    rw [hab] at hia haL
    exact (h.existsUnique_top_getD hia).unique ⟨ha.1.mono (h.le hia) haL, ha.2⟩
      ⟨hb.1.mono (h.le hia) hbL, hb.2⟩
  rw [← hinj.encard_image, himage, Set.Nat.encard_range]

theorem IsSuccessivePasting.isLayering_of_card (h : IsSuccessivePasting P k U L)
    (hdim : ∀ V ∈ L, (k : WithBot ℕ∞) < krullDim V)
    (hcard : (P.topsAbove U k).encard = L.length) :
    IsLayering P k U L := by
  classical
  let idx : P → ℕ := fun t => if ht : t ∈ U then (h.exists_mem_getD ht).choose else 0
  have hidx : ∀ t ∈ U, idx t < L.length ∧ t ∈ L.getD (idx t) ⊥ := fun t ht => by
    simp only [idx, dif_pos ht]
    exact (h.exists_mem_getD ht).choose_spec
  have hidx_eq : ∀ {i : ℕ} {t : P}, i < L.length → t ∈ L.getD i ⊥ → k < grade ℕ t →
      idx t = i := fun hi ht hk =>
    h.eq_of_mem_of_mem (hidx _ (h.le hi ht)).1 hi hk (hidx _ (h.le hi ht)).2 ht
  have hlayer : ∀ i, i < L.length → ∃ t, Maximal (· ∈ L.getD i ⊥) t ∧ k < grade ℕ t :=
      fun i hi => by
    obtain ⟨x, hx⟩ := coe_lt_krullDim_iff.1 (hdim _ (getD_mem_of_lt_length hi))
    obtain ⟨z, hxz, hz⟩ := (h.isMoleculeIn_getD hi).exists_le_maximal x.2
    exact ⟨z, hz, hx.trans_le (grade_mono hxz)⟩
  have himage : idx '' P.topsAbove U k = {i | i < L.length} := by
    ext i
    simp only [Set.mem_image, Set.mem_ofPred_eq]
    refine ⟨by rintro ⟨t, ht, rfl⟩; exact (hidx t ht.1.prop).1, fun hi => ?_⟩
    obtain ⟨t, ht, hk⟩ := hlayer i hi
    exact ⟨t, ⟨h.maximal_of_maximal hi ht hk, hk⟩, hidx_eq hi ht.prop hk⟩
  have hinj : Set.InjOn idx (P.topsAbove U k) :=
    (Set.finite_of_encard_eq_coe hcard).injOn_of_encard_image_eq
      (by rw [himage, Set.Nat.encard_range, hcard])
  refine ⟨h, fun V hV => ?_⟩
  obtain ⟨i, hi, rfl⟩ := exists_getD_eq_of_mem hV
  obtain ⟨t, ht, hk⟩ := hlayer i hi
  refine ⟨t, ⟨ht, hk⟩, fun s ⟨hs, hsk⟩ => hinj ⟨h.maximal_of_maximal hi hs hsk, hsk⟩
    ⟨h.maximal_of_maximal hi ht hk, hk⟩ ?_⟩
  rw [hidx_eq hi hs.prop hsk, hidx_eq hi ht.prop hk]

theorem isLayering_iff : IsLayering P k U L ↔ IsSuccessivePasting P k U L ∧
    (∀ V ∈ L, (k : WithBot ℕ∞) < krullDim V) ∧ (P.topsAbove U k).encard = L.length := by
  refine ⟨fun h => ⟨h.toIsSuccessivePasting, fun V hV => ?_, h.card_topsAbove⟩,
    fun ⟨h, hdim, hcard⟩ => h.isLayering_of_card hdim hcard⟩
  obtain ⟨t, ⟨ht, hk⟩, -⟩ := h.existsUnique_top V hV
  exact coe_lt_krullDim_iff.2 ⟨⟨t, ht.prop⟩, hk⟩

theorem IsLayering.one_lt_length_iff (h : IsLayering P k U L)
    [DecidablePred fun j => (P.topsAbove U j).Subsingleton] :
    1 < L.length ↔ k < P.layeringDim U h.isMoleculeIn_self := by
  rw [lt_layeringDim_iff h.isMoleculeIn_self, ← Set.one_lt_encard_iff_nontrivial, h.card_topsAbove]
  exact_mod_cast Iff.rfl

theorem IsLayering.layeringDim_le (h : IsLayering P k U L) {V : LowerSet P} (hV : V ∈ L)
    [DecidablePred fun j => (P.topsAbove V j).Subsingleton] :
    P.layeringDim V (h.isMoleculeIn V hV) ≤ k :=
  (layeringDim_le_iff (h.isMoleculeIn V hV)).2 fun _ ha _ hb =>
    (h.existsUnique_top V hV).unique ha hb

theorem IsLayering.exists_mem_topsAbove_of_lt_grade (h : IsLayering P k U L) {i : ℕ}
    (hi : i < L.length) {x : P} (hx : x ∈ L.getD i ⊥) (hxd : k + 1 < grade ℕ x) :
    ∃ z ∈ P.topsAbove U (k + 1), z ∈ L.getD i ⊥ := by
  obtain ⟨z, hxz, hz⟩ := (h.isMoleculeIn_getD hi).exists_le_maximal hx
  have hzd : k + 1 < grade ℕ z := hxd.trans_le (grade_mono hxz)
  exact ⟨z, ⟨h.maximal_of_maximal hi hz (by omega), hzd⟩, hz.prop⟩

theorem IsLayering.eq_of_lt_grade_of_lt_grade (h : IsLayering P k U L)
    [DecidablePred fun j => (P.topsAbove U j).Subsingleton]
    (hk : P.layeringDim U h.isMoleculeIn_self ≤ k + 1) {i j : ℕ} (hi : i < L.length)
    (hj : j < L.length) {x y : P} (hx : x ∈ L.getD i ⊥) (hxd : k + 1 < grade ℕ x)
    (hy : y ∈ L.getD j ⊥) (hyd : k + 1 < grade ℕ y) : i = j := by
  obtain ⟨z, hz, hzi⟩ := h.exists_mem_topsAbove_of_lt_grade hi hx hxd
  obtain ⟨w, hw, hwj⟩ := h.exists_mem_topsAbove_of_lt_grade hj hy hyd
  rw [((layeringDim_le_iff h.isMoleculeIn_self).1 hk) hz hw] at hzi
  exact h.eq_of_mem_of_mem hi hj (by have := hw.2; omega) hzi hwj

end Layers

end Atoms.Molecule.OGP
