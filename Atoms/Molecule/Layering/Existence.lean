import Atoms.Molecule.Layering.Basic

universe u

open Order

namespace Atoms.Molecule.OGP

variable {P : OGP.{u}}

theorem maximal_mem_of_isPastingIn {k : ℕ} {V W U : LowerSet P}
    (hp : P.IsPastingIn k V W U) (β : Bool) {t : P} (ht : Maximal (· ∈ cond β W V) t)
    (hk : k < grade ℕ t) : Maximal (· ∈ U) t := by
  have hs {X Y Z : LowerSet P} {γ : Bool} (ht : Maximal (· ∈ X) t)
      (hXY : X ⊓ Y = P.boundary Z k γ) : Maximal (· ∈ X ⊔ Y) t :=
    LowerSet.maximal_mem_sup_iff.2 ⟨Or.inl ht.prop, fun _ => ht, fun htY => absurd
      (grade_le_of_mem_boundary (hXY ▸ ⟨ht.prop, htY⟩ : t ∈ P.boundary Z k γ)) (not_le.2 hk)⟩
  rw [← hp.sup_eq]
  cases β
  · exact hs ht hp.inf_eq_output
  · rw [sup_comm]; exact hs ht (inf_comm V W ▸ hp.inf_eq_input)

private theorem IsMoleculeIn.exists_maximal_lt_grade {k : ℕ} {X : LowerSet P}
    (hX : IsMoleculeIn P X) (hkX : (k : WithBot ℕ∞) < krullDim X) :
    ∃ x, Maximal (· ∈ X) x ∧ k < grade ℕ x := by
  obtain ⟨⟨x₀, hx₀X⟩, hx₀⟩ := coe_lt_krullDim_iff.1 hkX
  obtain ⟨x, hx₀x, hxm⟩ := hX.exists_le_maximal hx₀X
  exact ⟨x, hxm, hx₀.trans_le (grade_mono hx₀x)⟩

theorem lt_layeringDim_of_isPastingIn {k : ℕ} {V W U : LowerSet P}
    [DecidablePred fun j => (P.topsAbove U j).Subsingleton]
    (hp : P.IsPastingIn k V W U) (hV : IsMoleculeIn P V) (hW : IsMoleculeIn P W)
    (hk : (k : WithBot ℕ∞) < min (krullDim V) (krullDim W)) :
    k < P.layeringDim U (hp.isMoleculeIn hV hW) := by
  obtain ⟨x, hxm, hxk⟩ := hV.exists_maximal_lt_grade (hk.trans_le (min_le_left _ _))
  obtain ⟨y, hym, hyk⟩ := hW.exists_maximal_lt_grade (hk.trans_le (min_le_right _ _))
  rw [lt_layeringDim_iff (hp.isMoleculeIn hV hW)]
  refine ⟨x, ⟨maximal_mem_of_isPastingIn hp false hxm hxk, hxk⟩,
    y, ⟨maximal_mem_of_isPastingIn hp true hym hyk, hyk⟩, fun h => ?_⟩
  have : x ∈ V ⊓ W := ⟨hxm.prop, h ▸ hym.prop⟩
  rw [hp.inf_eq_output] at this
  exact (grade_le_of_mem_boundary this).not_gt hxk

theorem layeringDim_le_of_isPastingIn {k : ℕ} {V W U : LowerSet P}
    (hp : P.IsPastingIn k V W U) (hV : IsMoleculeIn P V) (hW : IsMoleculeIn P W)
    (hk : (k : WithBot ℕ∞) < min (krullDim V) (krullDim W)) (β : Bool)
    [DecidablePred fun j => (P.topsAbove (cond β W V) j).Subsingleton]
    [DecidablePred fun j => (P.topsAbove U j).Subsingleton] :
    P.layeringDim (cond β W V) (Bool.cond_rec_prop β hW hV) ≤
      P.layeringDim U (hp.isMoleculeIn hV hW) := by
  have hlt := lt_layeringDim_of_isPastingIn hp hV hW hk
  rw [layeringDim_le_iff]
  refine (subsingleton_topsAbove_layeringDim (hp.isMoleculeIn hV hW)).anti fun t ⟨hm, hd⟩ => ?_
  exact ⟨maximal_mem_of_isPastingIn hp β hm (hlt.trans hd), hd⟩

theorem isPastingIn_sup_of_le_factor (β : Bool) {l : ℕ} {C W X R : LowerSet P}
    (hp : P.IsPastingIn l (cond β C W) (cond β W C) R) (hXW : X ≤ W)
    (hb : P.boundary X l (!β) = P.boundary W l (!β)) :
    P.IsPastingIn l (cond β C X) (cond β X C) (C ⊔ X) := by
  obtain ⟨-, h1, h2⟩ := (isPastingIn_cond_iff β).1 hp
  have e : C ⊓ X = P.boundary X l (!β) := le_antisymm
    (hb ▸ h1 ▸ inf_le_inf_left C hXW)
    (le_inf (hb ▸ h1 ▸ inf_le_left) (boundary_le X l (!β)))
  exact (isPastingIn_cond_iff β).2 ⟨rfl, e, e.trans (hb.trans (h1.symm.trans h2))⟩

section Layering

variable {k : ℕ} {U : LowerSet P} {L : List (LowerSet P)}

theorem IsLayering.boundary_prefixUnion_of_lt (h : IsLayering P k U L) {n : ℕ} (hn : n < k)
    (α : Bool) {i : ℕ} (hi : i < L.length) :
    P.boundary (prefixUnion L i) n α = P.boundary (L.getD 0 ⊥) n α := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [(h.isPastingIn i hi).boundary_eq_of_lt_cond false (h.isMoleculeIn_getD hi).isGlobular
      (h.isMoleculeIn_prefixUnion (by omega)).isGlobular hn α, ih (by omega)]

theorem IsLayering.boundary_prefixUnion_eq_of_lt (h : IsLayering P k U L) {n : ℕ} (hn : n < k)
    (α : Bool) {i : ℕ} (hi : i < L.length) :
    P.boundary (prefixUnion L i) n α = P.boundary U n α := by
  have hpos : 0 < L.length := List.length_pos_iff.2 h.ne_nil
  rw [h.boundary_prefixUnion_of_lt hn α hi, ← h.boundary_prefixUnion_of_lt hn α
    (i := L.length - 1) (by omega), h.prefixUnion_eq]

theorem IsLayering.boundary_getD_eq_of_lt (h : IsLayering P k U L) {n : ℕ} (hn : n < k)
    (α : Bool) {i : ℕ} (hi : i < L.length) :
    P.boundary (L.getD i ⊥) n α = P.boundary U n α := by
  cases i with
  | zero => exact h.boundary_prefixUnion_eq_of_lt (i := 0) hn α hi
  | succ i =>
    rw [← (h.isPastingIn i hi).boundary_eq_boundary_of_lt_cond true
      (h.isMoleculeIn_prefixUnion (by omega)).isGlobular
      (h.isMoleculeIn_getD hi).isGlobular hn α]
    exact h.boundary_prefixUnion_eq_of_lt hn α (by omega)

end Layering

theorem isLayering_append {k : ℕ} {V W U : LowerSet P} {LV LW : List (LowerSet P)}
    (hV : IsLayering P k V LV) (hW : IsLayering P k W LW) (hp : P.IsPastingIn k V W U) :
    IsLayering P k U (LV ++ LW) := by
  have hVpos : 0 < LV.length := List.length_pos_iff.2 hV.ne_nil
  have hWpos : 0 < LW.length := List.length_pos_iff.2 hW.ne_nil
  have hVeq : prefixUnion LV (LV.length - 1) = V := hV.prefixUnion_eq
  have hU : U = V ⊔ W := hp.sup_eq.symm
  have hp' : P.IsPastingIn k V W (V ⊔ W) := hU ▸ hp
  have hVB : ∀ j, j < LW.length →
      P.IsPastingIn k V (prefixUnion LW j) (V ⊔ prefixUnion LW j) := fun j hj =>
    isPastingIn_sup_of_le_factor true hp' (hW.prefixUnion_le hj)
      (by rw [Bool.not_true, hW.boundary_false_prefixUnion hj, ← hW.boundary_false_prefixUnion
        (i := LW.length - 1) (by omega), hW.prefixUnion_eq])
  refine ⟨⟨by simp [hV.ne_nil], fun X hX => ?_, ?_, fun i hi => ?_⟩, fun X hX => ?_⟩
  · exact (List.mem_append.1 hX).elim (hV.isMoleculeIn X) (hW.isMoleculeIn X)
  · have e : (LV ++ LW).length - 1 = LV.length + (LW.length - 1) := by
      simp only [List.length_append]; omega
    rw [e, prefixUnion_append_length_add hV.ne_nil, hVeq, hW.prefixUnion_eq, hU]
  · simp only [List.length_append] at hi
    rcases lt_or_ge (i + 1) LV.length with hlt | hge
    · rw [prefixUnion_append_of_lt (by omega), prefixUnion_append_of_lt hlt,
        List.getD_append _ _ _ _ hlt]
      exact hV.isPastingIn i hlt
    · obtain ⟨j, hj⟩ : ∃ j, i + 1 = LV.length + j := ⟨i + 1 - LV.length, by omega⟩
      rw [hj, prefixUnion_append_length_add hV.ne_nil,
        List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left, hVeq]
      cases j with
      | zero =>
        have e : i = LV.length - 1 := by omega
        rw [e, prefixUnion_append_of_lt (by omega), hVeq]
        exact hVB 0 (by omega)
      | succ j =>
        have e : i = LV.length + j := by omega
        rw [e, prefixUnion_append_length_add hV.ne_nil, hVeq]
        have hj' : j + 1 < LW.length := by omega
        obtain ⟨hBY, e1, e2⟩ := hW.isPastingIn j hj'
        have hsub : V ⊓ LW.getD (j + 1) ⊥ ≤ prefixUnion LW j ⊓ LW.getD (j + 1) ⊥ := by
          rintro x ⟨hxV, hxY⟩
          refine ⟨?_, hxY⟩
          have hxW : x ∈ V ⊓ W := ⟨hxV, hW.le (i := j + 1) hj' hxY⟩
          rw [hp.inf_eq_input, ← hW.prefixUnion_eq, hW.boundary_false_prefixUnion (by omega),
            ← hW.boundary_false_prefixUnion (i := j) (by omega)] at hxW
          exact boundary_le _ k false hxW
        have hinter : (V ⊔ prefixUnion LW j) ⊓ LW.getD (j + 1) ⊥ =
            prefixUnion LW j ⊓ LW.getD (j + 1) ⊥ := by
          rw [inf_sup_right, sup_eq_right.2 hsub]
        refine ⟨?_, ?_, ?_⟩
        · rw [← hBY, sup_assoc]
        · rw [hinter, (hVB j (by omega)).boundary_output, e1]
        · rw [hinter, e2]
  · exact (List.mem_append.1 hX).elim (hV.existsUnique_top X) (hW.existsUnique_top X)

theorem existsUnique_top_sup {k : ℕ} {A C : LowerSet P} (hCk : krullDim C ≤ k)
    (h : ∃! t : P, Maximal (· ∈ A) t ∧ k < grade ℕ t) :
    ∃! t : P, Maximal (· ∈ A ⊔ C) t ∧ k < grade ℕ t := by
  refine (existsUnique_congr fun t => ?_).2 h
  refine and_congr_left fun ht => ?_
  have htC : t ∉ C := fun hC => (krullDim_le_coe_iff.1 hCk ⟨t, hC⟩).not_gt ht
  rw [LowerSet.maximal_mem_sup_iff]
  exact ⟨fun ⟨hx, hA, _⟩ => hA (hx.resolve_right htC),
    fun hm => ⟨Or.inl hm.prop, fun _ => hm, fun hC => absurd hC htC⟩⟩

theorem IsLayering.sup (β : Bool) {k l : ℕ} {C W : LowerSet P}
    {L : List (LowerSet P)} (h : IsLayering P k W L) (hlk : l < k) (hC : IsMoleculeIn P C)
    (hCk : krullDim C ≤ k)
    (hp : P.IsPastingIn l (cond β C W) (cond β W C) (cond β C W ⊔ cond β W C)) :
    IsLayering P k (cond β C W ⊔ cond β W C) (L.map fun A => cond β C A ⊔ cond β A C) := by
  have hmap : (fun A => cond β C A ⊔ cond β A C) = (C ⊔ ·) := funext (Bool.cond_sup_cond β C)
  rw [hmap, Bool.cond_sup_cond]
  have hpos : 0 < L.length := List.length_pos_iff.2 h.ne_nil
  have hgC : P.IsGlobular C := hC.isGlobular
  have hf : ∀ A B : LowerSet P, C ⊔ (A ⊔ B) = (C ⊔ A) ⊔ (C ⊔ B) := fun _ _ =>
    sup_sup_distrib_left _ _ _
  have hpre : ∀ i, i < L.length → P.IsPastingIn l (cond β C (prefixUnion L i))
      (cond β (prefixUnion L i) C) (C ⊔ prefixUnion L i) := fun i hi =>
    isPastingIn_sup_of_le_factor β hp (h.prefixUnion_le hi)
      (h.boundary_prefixUnion_eq_of_lt hlk (!β) hi)
  have hlay : ∀ i, i < L.length → P.IsPastingIn l (cond β C (L.getD i ⊥))
      (cond β (L.getD i ⊥) C) (C ⊔ L.getD i ⊥) := fun i hi =>
    isPastingIn_sup_of_le_factor β hp (h.le hi)
      (h.boundary_getD_eq_of_lt hlk (!β) hi)
  have hbd : ∀ {A : LowerSet P}, P.IsGlobular A → P.IsPastingIn l (cond β C A) (cond β A C)
      (C ⊔ A) → ∀ γ, P.boundary (C ⊔ A) k γ = C ⊔ P.boundary A k γ := fun hgA hpA γ => by
    rw [hpA.boundary_eq_sup_of_lt_cond β hgC hgA hlk γ, boundary_eq_self hCk]
  refine ⟨⟨by simp [h.ne_nil], fun X hX => ?_, ?_, fun i hi => ?_⟩, fun X hX => ?_⟩
  · obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
    obtain ⟨i, hi, rfl⟩ := exists_getD_eq_of_mem hY
    have hY := h.isMoleculeIn_getD hi
    exact (hlay i hi).isMoleculeIn (Bool.cond_rec_prop β hC hY) (Bool.cond_rec_prop β hY hC)
  · rw [List.length_map, prefixUnion_map hf (by omega), h.prefixUnion_eq]
  · rw [List.length_map] at hi
    rw [prefixUnion_map hf (by omega), prefixUnion_map hf hi, getD_map_of_lt hi]
    obtain ⟨hAY, e1, e2⟩ := h.isPastingIn i hi
    have hinter : (C ⊔ prefixUnion L i) ⊓ (C ⊔ L.getD (i + 1) ⊥) =
        C ⊔ prefixUnion L i ⊓ L.getD (i + 1) ⊥ :=
      (sup_inf_left _ _ _).symm
    refine ⟨?_, ?_, ?_⟩
    · rw [← hAY, hf]
    · rw [hinter, e1, hbd (h.isMoleculeIn_prefixUnion (i := i) (by omega)).isGlobular
        (hpre i (by omega))]
    · rw [hinter, e2, hbd (h.isMoleculeIn_getD hi).isGlobular (hlay (i + 1) hi)]
  · obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
    rw [sup_comm]
    exact existsUnique_top_sup hCk (h.existsUnique_top Y hY)

theorem isLayering_singleton_of_existsUnique_top {k l : ℕ} {V : LowerSet P}
    (hV : IsMoleculeIn P V) (htop : ∃! t : P, Maximal (· ∈ V) t ∧ k < grade ℕ t)
    (hkl : k ≤ l) (hl : (l : WithBot ℕ∞) < krullDim V) : IsLayering P l V [V] := by
  refine ⟨⟨List.cons_ne_nil _ _, fun X hX => ?_, rfl, fun i hi => ?_⟩, fun X hX => ?_⟩
  · exact List.mem_singleton.1 hX ▸ hV
  · simp at hi
  · obtain rfl := List.mem_singleton.1 hX
    obtain ⟨z, hz, hzd⟩ := hV.exists_maximal_lt_grade hl
    exact ⟨z, ⟨hz, hzd⟩, fun s ⟨hs, hsd⟩ => htop.unique ⟨hs, by omega⟩ ⟨hz, by omega⟩⟩

theorem admitsLayering_sup_of_isPastingIn {k l : ℕ} {V W : LowerSet P} (hlk : l < k)
    (hV : IsMoleculeIn P V) (hW : IsMoleculeIn P W) (hp : P.IsPastingIn l V W (V ⊔ W))
    (hLV : (k : WithBot ℕ∞) < krullDim V → AdmitsLayering P k V)
    (hLW : (k : WithBot ℕ∞) < krullDim W → AdmitsLayering P k W)
    (hk : (k : WithBot ℕ∞) < krullDim (V ⊔ W : LowerSet P)) : AdmitsLayering P k (V ⊔ W) := by
  rw [LowerSet.krullDim_sup] at hk
  by_cases hdV : krullDim V ≤ k
  · obtain ⟨LW, hLW'⟩ := hLW ((lt_max_iff.1 hk).resolve_left hdV.not_gt)
    exact ⟨_, hLW'.sup true hlk hV hdV hp⟩
  by_cases hdW : krullDim W ≤ k
  · obtain ⟨LV, hLV'⟩ := hLV ((lt_max_iff.1 hk).resolve_right hdW.not_gt)
    exact ⟨_, hLV'.sup false hlk hW hdW hp⟩
  obtain ⟨LV, hLV'⟩ := hLV (not_le.1 hdV)
  obtain ⟨LW, hLW'⟩ := hLW (not_le.1 hdW)
  have hVt := hV.boundary k true
  have hWf := hW.boundary k false
  have hpV := isPastingIn_self_boundary_true V k
  have hpW := isPastingIn_boundary_false_self W k
  have h1 := isPastingIn_interchange_left hlk hV.isGlobular hVt.isGlobular hWf.isGlobular
    hW.isGlobular hpV hpW hp
  have h2 := isPastingIn_interchange_right hlk hV.isGlobular hVt.isGlobular hWf.isGlobular
    hW.isGlobular hpV hpW hp
  have h3 := isPastingIn_interchange hlk hV.isGlobular hVt.isGlobular hWf.isGlobular
    hW.isGlobular hpV hpW hp
  exact ⟨_, isLayering_append
    (hLV'.sup false hlk hWf (krullDim_boundary_le W k false) h1)
    (hLW'.sup true hlk hVt (krullDim_boundary_le V k true) h2) h3⟩

theorem admitsLayering_of_layeringDim_le {k : ℕ} {U : LowerSet P} (hU : IsMoleculeIn P U)
    [inst : DecidablePred fun j => (P.topsAbove U j).Subsingleton]
    (hk : P.layeringDim U hU ≤ k + 1) (hkn : (k : WithBot ℕ∞) < krullDim U) :
    AdmitsLayering P k U := by
  rw [layeringDim_le_iff] at hk
  clear inst
  classical
  induction hU generalizing k with
  | point x hx =>
    rw [LowerSet.krullDim_Iic_of_isMin hx] at hkn
    exact absurd hkn (not_lt.2 (by exact_mod_cast Nat.zero_le k))
  | atom t hround hbdry _ =>
    refine ⟨[.Iic t], isLayering_singleton_of_existsUnique_top
      (.atom t hround hbdry) ?_ le_rfl hkn⟩
    refine ⟨t, ⟨⟨le_rfl, fun y hy _ => hy⟩, ?_⟩, fun s ⟨hs, _⟩ => hs.eq_of_le le_rfl hs.prop⟩
    rw [LowerSet.krullDim_Iic] at hkn
    exact_mod_cast hkn
  | paste l V W U hpaste hV hW hl ihV ihW =>
    have hk' : P.layeringDim U (hpaste.isMoleculeIn hV hW) ≤ k + 1 :=
      (layeringDim_le_iff _).2 hk
    have hlU := lt_layeringDim_of_isPastingIn hpaste hV hW hl
    have hVU := (layeringDim_le_iff hV).1
      ((layeringDim_le_of_isPastingIn hpaste hV hW hl false).trans hk')
    have hWU := (layeringDim_le_iff hW).1
      ((layeringDim_le_of_isPastingIn hpaste hV hW hl true).trans hk')
    have hUeq : U = V ⊔ W := hpaste.sup_eq.symm
    have hp : P.IsPastingIn l V W (V ⊔ W) := hUeq ▸ hpaste
    have hlV : (l : WithBot ℕ∞) < krullDim V := hl.trans_le (min_le_left _ _)
    have hlW : (l : WithBot ℕ∞) < krullDim W := hl.trans_le (min_le_right _ _)
    rcases Nat.lt_or_ge l k with hlk | hlk
    · rw [hUeq] at hkn ⊢
      exact admitsLayering_sup_of_isPastingIn hlk hV hW hp (ihV hVU) (ihW hWU) hkn
    · obtain rfl : l = k := by omega
      obtain ⟨LV, hLV⟩ := ihV hVU hlV
      obtain ⟨LW, hLW⟩ := ihW hWU hlW
      exact ⟨_, isLayering_append hLV hLW hpaste⟩

theorem admitsLayering_pred_krullDim {U : LowerSet P} {n : ℕ} (hU : IsMoleculeIn P U)
    (hn : krullDim U = n) (hpos : 0 < n) : AdmitsLayering P (n - 1) U := by
  classical
  exact admitsLayering_of_layeringDim_le hU
    (by have := layeringDim_le_of_krullDim_le hU hn.le; omega)
    (by rw [hn]; exact_mod_cast (by omega : n - 1 < n))

theorem IsMoleculeIn.layeringDim_induction {motive : LowerSet P → Prop}
    (atom : ∀ U : LowerSet P, P.IsAtomIn U → motive U)
    (layer : ∀ (k : ℕ) (U : LowerSet P) (L : List (LowerSet P))
      [DecidablePred fun j => (P.topsAbove U j).Subsingleton] (hL : IsLayering P k U L),
      P.layeringDim U hL.isMoleculeIn_self = k + 1 → (∀ V ∈ L, motive V) → motive U)
    {U : LowerSet P} (hU : IsMoleculeIn P U) : motive U := by
  classical
  induction hd : P.layeringDim U hU using Nat.strong_induction_on generalizing U with
  | _ n ih =>
    rcases n with _ | k
    · exact atom U ((layeringDim_eq_zero_iff hU).1 hd)
    · obtain ⟨m, hm⟩ := hU.exists_krullDim_eq
      have hkn : (k : WithBot ℕ∞) < krullDim U := by
        have := layeringDim_le_of_krullDim_le hU hm.le
        rw [hm]
        exact_mod_cast (by omega : k < m)
      obtain ⟨L, hL⟩ := admitsLayering_of_layeringDim_le hU hd.le hkn
      refine layer k U L hL hd fun V hV => ?_
      exact ih (P.layeringDim V (hL.isMoleculeIn V hV))
        (by have := hL.layeringDim_le hV; omega)
        (hL.isMoleculeIn V hV) rfl

theorem IsLayering.admitsLayering_prefixUnion {k l : ℕ} {U : LowerSet P}
    {L : List (LowerSet P)} (h : IsLayering P k U L) (hkl : k < l) {i : ℕ}
    (hi : i < L.length) (hl : (l : WithBot ℕ∞) < krullDim (prefixUnion L i)) :
    AdmitsLayering P l (prefixUnion L i) := by
  induction i with
  | zero =>
    exact ⟨_, isLayering_singleton_of_existsUnique_top (h.isMoleculeIn_getD hi)
      (h.existsUnique_top_getD hi) hkl.le hl⟩
  | succ i ih =>
    have hp := h.isPastingIn i hi
    have hA := h.isMoleculeIn_prefixUnion (i := i) (by omega)
    have hY := h.isMoleculeIn_getD hi
    have hU : prefixUnion L (i + 1) = prefixUnion L i ⊔ L.getD (i + 1) ⊥ := hp.sup_eq.symm
    have hp' : P.IsPastingIn k (prefixUnion L i) (L.getD (i + 1) ⊥)
        (prefixUnion L i ⊔ L.getD (i + 1) ⊥) := hU ▸ hp
    rw [hU] at hl ⊢
    exact admitsLayering_sup_of_isPastingIn hkl hA hY hp' (fun hlA => ih (by omega) hlA)
      (fun hlY => ⟨_, isLayering_singleton_of_existsUnique_top hY
        (h.existsUnique_top_getD hi) hkl.le hlY⟩) hl

theorem admitsLayering_of_admitsLayering_of_le {k l : ℕ} {U : LowerSet P}
    (h : AdmitsLayering P k U) (hkl : k ≤ l) (hl : (l : WithBot ℕ∞) < krullDim U) :
    AdmitsLayering P l U := by
  obtain ⟨L, hL⟩ := h
  rcases hkl.lt_or_eq with hkl | rfl
  · have hpos : 0 < L.length := List.length_pos_iff.2 hL.ne_nil
    rw [← hL.prefixUnion_eq] at hl ⊢
    exact hL.admitsLayering_prefixUnion hkl (by omega) hl
  · exact ⟨L, hL⟩

end Atoms.Molecule.OGP
