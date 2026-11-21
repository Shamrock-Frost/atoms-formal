import Atoms.Molecule.Labelling.Basic
import Atoms.Molecule.Layering.Ordering
import Atoms.Molecule.Layering.Existence
import Atoms.Molecule.Layering.Interior

universe w v u u₁

open Order CategoryTheory Bicategory

namespace Atoms.Molecule.OGP

variable {P : OGP.{u}}

def orderPrefix (M : LowerSet P) (xs : List P) (j : ℕ) : LowerSet P :=
  P.boundary M 1 false ⊔ lowerClosure {x | x ∈ xs.take j}

theorem mem_orderPrefix {M : LowerSet P} {xs : List P} {j : ℕ} {y : P} :
    y ∈ orderPrefix M xs j ↔ y ∈ P.boundary M 1 false ∨ ∃ x ∈ xs.take j, y ≤ x := by
  rw [orderPrefix, LowerSet.mem_sup_iff]
  exact or_congr Iff.rfl Iff.rfl

instance decidableMemOrderPrefix [Fintype P] [DecidableLE P] (M : LowerSet P)
    [DecidablePred (· ∈ M)] (xs : List P) (j : ℕ) : DecidablePred (· ∈ orderPrefix M xs j) :=
  fun _ => decidable_of_iff _ mem_orderPrefix.symm

variable {M : LowerSet P} {xs : List P}

@[simp]
theorem orderPrefix_zero : orderPrefix M xs 0 = P.boundary M 1 false :=
  SetLike.ext fun _ => by simp [mem_orderPrefix]

theorem orderPrefix_succ {j : ℕ} (hj : j < xs.length) :
    orderPrefix M xs (j + 1) = orderPrefix M xs j ⊔ .Iic xs[j] :=
  SetLike.ext fun y => by
    rw [LowerSet.mem_sup_iff, mem_orderPrefix, mem_orderPrefix, List.take_add_one,
      List.getElem?_eq_getElem hj]
    simp only [Option.toList_some, List.mem_append, List.mem_singleton, LowerSet.mem_Iic_iff]
    constructor
    · rintro (h | ⟨x, hx | rfl, hyx⟩)
      exacts [.inl (.inl h), .inl (.inr ⟨x, hx, hyx⟩), .inr hyx]
    · rintro ((h | ⟨x, hx, hyx⟩) | h)
      exacts [.inl h, .inr ⟨x, .inl hx, hyx⟩, .inr ⟨_, .inr rfl, h⟩]

theorem orderPrefix_of_length_le {j : ℕ} (hj : xs.length ≤ j) :
    orderPrefix M xs j = orderPrefix M xs xs.length := by
  rw [orderPrefix, orderPrefix, List.take_of_length_le hj, List.take_length]

structure IsLayerOrder (M : LowerSet P) (xs : List P) : Prop where
  grade_eq : ∀ x ∈ xs, grade ℕ x = 2
  Iic_inf_orderPrefix : ∀ (j : ℕ) (hj : j < xs.length),
    .Iic xs[j] ⊓ orderPrefix M xs j = P.boundary (.Iic xs[j]) 1 false
  isSubmoleculeOf : ∀ (j : ℕ) (hj : j < xs.length),
    P.IsSubmoleculeOf (P.boundary (.Iic xs[j]) 1 false) (P.boundary (orderPrefix M xs j) 1 true)
  orderPrefix_length : orderPrefix M xs xs.length = M

namespace IsLayerOrder

variable (h : IsLayerOrder M xs)
include h

theorem mem {x : P} (hx : x ∈ xs) : x ∈ M := by
  rw [← h.orderPrefix_length, mem_orderPrefix]
  exact .inr ⟨x, by rwa [List.take_length], le_rfl⟩

variable (hM : IsMoleculeIn P M)
include hM

theorem isMoleculeIn_Iic {j : ℕ} (hj : j < xs.length) : IsMoleculeIn P (.Iic xs[j]) :=
  (hM.isAtomIn_Iic (h.mem (List.getElem_mem hj))).isMoleculeIn

theorem isPastingAtIn_and_isMoleculeIn (j : ℕ) :
    (∀ hj : j < xs.length, P.IsPastingAtIn 1 true (.Iic xs[j]) (orderPrefix M xs j)
      (orderPrefix M xs (j + 1))) ∧ IsMoleculeIn P (orderPrefix M xs j) := by
  have hpaste (j : ℕ) (hj : j < xs.length) (hT : IsMoleculeIn P (orderPrefix M xs j)) :
      P.IsPastingAtIn 1 true (.Iic xs[j]) (orderPrefix M xs j) (orderPrefix M xs (j + 1)) :=
    ⟨h.isMoleculeIn_Iic hM hj, hT, by rw [orderPrefix_succ hj, sup_comm],
      h.Iic_inf_orderPrefix j hj, (h.Iic_inf_orderPrefix j hj).symm ▸ h.isSubmoleculeOf j hj⟩
  induction j with
  | zero =>
    have hT : IsMoleculeIn P (orderPrefix M xs 0) := by
      rw [orderPrefix_zero]
      exact hM.boundary 1 false
    exact ⟨fun hj => hpaste 0 hj hT, hT⟩
  | succ j ih =>
    have hT : IsMoleculeIn P (orderPrefix M xs (j + 1)) := by
      by_cases hj : j < xs.length
      · exact (hpaste j hj ih.2).isMoleculeIn
      · rw [orderPrefix_of_length_le (by omega), ← orderPrefix_of_length_le (j := j) (by omega)]
        exact ih.2
    exact ⟨fun hj => hpaste _ hj hT, hT⟩

theorem isMoleculeIn_orderPrefix (j : ℕ) : IsMoleculeIn P (orderPrefix M xs j) :=
  (h.isPastingAtIn_and_isMoleculeIn hM j).2

theorem isPastingAtIn {j : ℕ} (hj : j < xs.length) :
    P.IsPastingAtIn 1 true (.Iic xs[j]) (orderPrefix M xs j) (orderPrefix M xs (j + 1)) :=
  (h.isPastingAtIn_and_isMoleculeIn hM j).1 hj

theorem boundary_false_orderPrefix (j : ℕ) :
    P.boundary (orderPrefix M xs j) 1 false = P.boundary M 1 false := by
  induction j with
  | zero =>
    rw [orderPrefix_zero]
    exact boundary_boundary_of_le le_rfl false false
  | succ j ih =>
    by_cases hj : j < xs.length
    · exact ((h.isPastingAtIn hM hj).boundary_not).trans ih
    · rw [orderPrefix_of_length_le (by omega), ← orderPrefix_of_length_le (j := j) (by omega)]
      exact ih

theorem boundary_zero_boundary_orderPrefix (j : ℕ) (α : Bool) :
    P.boundary (P.boundary (orderPrefix M xs j) 1 true) 0 α = P.boundary M 0 α := by
  have hT := (h.isMoleculeIn_orderPrefix hM j).isGlobular
  rw [hT.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one),
    ← hT.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one) (β := false),
    h.boundary_false_orderPrefix hM j,
    hM.isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)]

theorem krullDim_boundary_Iic {j : ℕ} (hj : j < xs.length) (α : Bool) :
    krullDim (P.boundary (.Iic xs[j]) 1 α) = 1 :=
  ((h.isMoleculeIn_Iic hM hj).krullDim_boundary (by
    rw [LowerSet.krullDim_Iic, h.grade_eq _ (List.getElem_mem hj)]
    exact_mod_cast one_le_two) α).trans Nat.cast_one

theorem one_le_krullDim_orderPrefix {j : ℕ} (hj : j < xs.length) :
    ((1 : ℕ) : WithBot ℕ∞) ≤ krullDim (orderPrefix M xs j) := by
  rw [Nat.cast_one, ← h.krullDim_boundary_Iic hM hj false]
  exact LowerSet.krullDim_mono ((h.isSubmoleculeOf j hj).le.trans (boundary_le _ 1 true))

end IsLayerOrder

theorem IsLayering.isLayerOrder {L : List (LowerSet P)} (hL : IsLayering P 1 M L)
    (hd : krullDim M = 2) (hlen : xs.length = L.length)
    (hxs : ∀ (j : ℕ) (hj : j < xs.length), xs[j] ∈ L.getD j ⊥ ∧ grade ℕ xs[j] = 2) :
    IsLayerOrder M xs := by
  have hU : krullDim M = ((1 + 1 : ℕ) : WithBot ℕ∞) := by rw [hd]; rfl
  have key : ∀ j ≤ xs.length, orderPrefix M xs j = layerPrefix M 1 L j := by
    intro j hj
    induction j with
    | zero => exact orderPrefix_zero
    | succ j ih =>
      rw [orderPrefix_succ (by omega), ih (by omega),
        hL.layerPrefix_succ hU (by omega) (hxs j (by omega)).1 (hxs j (by omega)).2]
  refine ⟨fun x hx => ?_, fun j hj => ?_, fun j hj => ?_, ?_⟩
  · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    exact (hxs j hj).2
  · rw [key j hj.le]
    exact hL.Iic_inf_layerPrefix hU (by omega) (hxs j hj).1 (hxs j hj).2
  · rw [key j hj.le]
    exact hL.isSubmoleculeOf_boundary_Iic_layerPrefix hU (by omega) (hxs j hj).1 (hxs j hj).2
  · rw [key _ le_rfl, hlen]
    exact hL.layerPrefix_length

theorem exists_isLayerOrder (hM : IsMoleculeIn P M) (hd : krullDim M = 2) :
    ∃ xs, IsLayerOrder M xs := by
  obtain ⟨L, hL⟩ := admitsLayering_pred_krullDim hM (n := 2) (by rw [hd]; rfl) two_pos
  have hU : krullDim M = ((1 + 1 : ℕ) : WithBot ℕ∞) := by rw [hd]; rfl
  have ht (j : Fin L.length) := hL.exists_top_getD hU j.2
  refine ⟨List.ofFn fun j => (ht j).choose, hL.isLayerOrder hd (List.length_ofFn) fun j hj => ?_⟩
  rw [List.getElem_ofFn]
  exact ⟨(ht ⟨j, _⟩).choose_spec.1, (ht ⟨j, _⟩).choose_spec.2.1⟩

theorem isLayerOrder_Iic {x : P} (hx : IsMoleculeIn P (.Iic x)) (h2 : grade ℕ x = 2) :
    IsLayerOrder (.Iic x) [x] := by
  have h₀ : orderPrefix (.Iic x) [x] 0 = P.boundary (.Iic x) 1 false := orderPrefix_zero
  refine ⟨by simpa using h2, fun j hj => ?_, fun j hj => ?_, ?_⟩
  · obtain rfl : j = 0 := by simpa using hj
    rw [h₀]
    exact inf_eq_right.2 (boundary_le _ 1 false)
  · obtain rfl : j = 0 := by simpa using hj
    rw [h₀, boundary_boundary_of_le le_rfl true false]
    exact .refl (hx.boundary 1 false)
  · rw [List.length_singleton, orderPrefix_succ (by simp), h₀]
    exact sup_eq_right.2 (boundary_le _ 1 false)

theorem isLayerOrder_nil (hd : krullDim M ≤ 1) : IsLayerOrder M [] :=
  ⟨fun _ hx => (List.not_mem_nil hx).elim, fun _ hj => (Nat.not_lt_zero _ hj).elim,
    fun _ hj => (Nat.not_lt_zero _ hj).elim, by
      rw [List.length_nil, orderPrefix_zero]
      exact boundary_eq_self (hd.trans_eq Nat.cast_one.symm) false⟩

theorem exists_isLayerOrder_of_krullDim_le (hM : IsMoleculeIn P M) (hd : krullDim M ≤ 2) :
    ∃ xs, IsLayerOrder M xs := by
  obtain ⟨n, hn⟩ := hM.exists_krullDim_eq
  rw [hn] at hd
  have hn2 : n ≤ 2 := by exact_mod_cast hd
  rcases Nat.lt_or_ge n 2 with h | h
  · exact ⟨[], isLayerOrder_nil (by rw [hn]; exact_mod_cast Nat.le_of_lt_succ h)⟩
  · exact exists_isLayerOrder hM (by rw [hn]; exact_mod_cast le_antisymm hn2 h)

section Path

variable [Fintype P] [DecidableLE P]

theorem pathOf_boundary_eq_comp_comp {T R : LowerSet P} [DecidablePred (· ∈ T)]
    [DecidablePred (· ∈ R)] {x : P} (hp : P.IsPastingAtIn 1 true (.Iic x) T R)
    (hx : grade ℕ x = 2) (hT : ((1 : ℕ) : WithBot ℕ∞) ≤ krullDim T) {s a b t : P}
    (hs : P.boundary (P.boundary T 1 true) 0 false = .Iic s)
    (ht : P.boundary (P.boundary T 1 true) 0 true = .Iic t)
    (hs' : P.boundary (P.boundary R 1 true) 0 false = .Iic s)
    (ht' : P.boundary (P.boundary R 1 true) 0 true = .Iic t)
    (ha : P.boundary (P.boundary (.Iic x) 1 false) 0 false = .Iic a)
    (hb : P.boundary (P.boundary (.Iic x) 1 false) 0 true = .Iic b)
    (ha' : P.boundary (P.boundary (.Iic x) 1 true) 0 false = .Iic a)
    (hb' : P.boundary (P.boundary (.Iic x) 1 true) 0 true = .Iic b)
    (p : Quiver.Path (V := EdgeQuiver P) s a) (c : Quiver.Path (V := EdgeQuiver P) b t)
    (h : pathOf (P.boundary T 1 true) (hp.isMoleculeIn_right.boundary 1 true)
        ((krullDim_boundary_le _ 1 true).trans_eq Nat.cast_one) hs ht =
      p.comp ((pathOf (P.boundary (.Iic x) 1 false) (hp.isMoleculeIn_left.boundary 1 false)
        ((krullDim_boundary_le _ 1 false).trans_eq Nat.cast_one) ha hb).comp c)) :
    p.comp ((pathOf (P.boundary (.Iic x) 1 true) (hp.isMoleculeIn_left.boundary 1 true)
        ((krullDim_boundary_le _ 1 true).trans_eq Nat.cast_one) ha' hb').comp c) =
      pathOf (P.boundary R 1 true) (hp.isMoleculeIn.boundary 1 true)
        ((krullDim_boundary_le _ 1 true).trans_eq Nat.cast_one) hs' ht' := by
  have hS := hp.isMoleculeIn_left
  have hkS : ((1 : ℕ) : WithBot ℕ∞) ≤ krullDim (LowerSet.Iic x) := by
    rw [LowerSet.krullDim_Iic, hx]
    exact_mod_cast one_le_two
  have hR := hp.coe_boundary_eq hkS hT
  rw [hp.inf_eq] at hR
  have hd₁ (U : LowerSet P) (α : Bool) : krullDim (P.boundary U 1 α) ≤ 1 :=
    (krullDim_boundary_le U 1 α).trans_eq Nat.cast_one
  have hn := nodup_edgeList (hp.isMoleculeIn_right.boundary 1 true) (hd₁ T true)
  have hE := congrArg pathEdges h
  rw [pathEdges_pathOf, pathEdges_comp, pathEdges_comp, pathEdges_pathOf] at hE
  rw [hE] at hn
  have hout {y : P} (hy : y ∈ edgeList (P.boundary T 1 true))
      (hyx : y ∉ edgeList (P.boundary (.Iic x) 1 false)) : y ∈ P.boundary R 1 true := by
    have hy' := (mem_edgeList_iff (hp.isMoleculeIn_right.boundary 1 true) (hd₁ T true)).1 hy
    have hR' : y ∈ (P.boundary R 1 true : Set P) := by
      rw [hR]
      exact .inl ⟨hy'.1, fun hi => hyx ((mem_edgeList_iff (hS.boundary 1 false)
        (hd₁ _ false)).2 ⟨hi.1, hy'.2⟩)⟩
    exact hR'
  refine eq_pathOf_of_forall_mem _ _ _ _ _ fun y hy => ?_
  rw [pathEdges_comp, pathEdges_comp, pathEdges_pathOf, List.mem_append, List.mem_append] at hy
  rcases hy with hy | hy | hy
  · refine hout (by rw [hE]; simp [hy]) fun hyx => ?_
    exact (List.nodup_append.1 hn).2.2 y hy y (List.mem_append_left _ hyx) rfl
  · have hR' : y ∈ (P.boundary R 1 true : Set P) := by
      rw [hR]
      exact .inr ((mem_edgeList_iff (hS.boundary 1 true) (hd₁ _ true)).1 hy).1
    exact hR'
  · refine hout (by rw [hE]; simp [hy]) fun hyx => ?_
    exact (List.nodup_append.1 (List.nodup_append.1 hn).2.1).2.2 y hyx y hy rfl

variable [DecidablePred (· ∈ M)] (hM : IsMoleculeIn P M) (h : IsLayerOrder M xs) {s t : P}
  (hs : P.boundary M 0 false = .Iic s) (ht : P.boundary M 0 true = .Iic t)

def stagePath (j : ℕ) : Quiver.Path (V := EdgeQuiver P) s t :=
  pathOf (P.boundary (orderPrefix M xs j) 1 true)
    ((h.isMoleculeIn_orderPrefix hM j).boundary 1 true)
    ((krullDim_boundary_le _ 1 true).trans_eq Nat.cast_one)
    ((h.boundary_zero_boundary_orderPrefix hM j false).trans hs)
    ((h.boundary_zero_boundary_orderPrefix hM j true).trans ht)

theorem pathEdges_stagePath (j : ℕ) :
    pathEdges (stagePath hM h hs ht j) = edgeList (P.boundary (orderPrefix M xs j) 1 true) :=
  pathEdges_pathOf _ _ _ _

theorem eq_stagePath_of_forall_mem {j : ℕ} (q : Quiver.Path (V := EdgeQuiver P) s t)
    (hq : ∀ e ∈ pathEdges q, e ∈ P.boundary (orderPrefix M xs j) 1 true) :
    q = stagePath hM h hs ht j :=
  eq_pathOf_of_forall_mem _ _ _ _ q hq

theorem stagePath_zero :
    stagePath hM h hs ht 0 = pathOf (P.boundary M 1 false) (hM.boundary 1 false)
      ((krullDim_boundary_le _ 1 false).trans_eq Nat.cast_one)
      ((hM.isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans hs)
      ((hM.isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans ht) := by
  refine eq_pathOf_of_forall_mem _ _ _ _ _ fun y hy => ?_
  rw [pathEdges_stagePath] at hy
  have hy' := ((mem_edgeList_iff ((h.isMoleculeIn_orderPrefix hM 0).boundary 1 true)
    ((krullDim_boundary_le _ 1 true).trans_eq Nat.cast_one)).1 hy).1
  rwa [orderPrefix_zero, boundary_boundary_of_le le_rfl true false] at hy'

theorem stagePath_length :
    stagePath hM h hs ht xs.length = pathOf (P.boundary M 1 true) (hM.boundary 1 true)
      ((krullDim_boundary_le _ 1 true).trans_eq Nat.cast_one)
      ((hM.isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans hs)
      ((hM.isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans ht) := by
  refine eq_pathOf_of_forall_mem _ _ _ _ _ fun y hy => ?_
  rw [pathEdges_stagePath] at hy
  have hy' := ((mem_edgeList_iff ((h.isMoleculeIn_orderPrefix hM _).boundary 1 true)
    ((krullDim_boundary_le _ 1 true).trans_eq Nat.cast_one)).1 hy).1
  rwa [h.orderPrefix_length] at hy'

variable {B : Type u₁} [Bicategory.{w, v} B] {hP : P.IsRDC} (ℓ : Labelling B P hP)

def Labelling.layerComp (j : ℕ) (hj : j < xs.length) :
    pathComp ℓ.toPrefunctor (stagePath hM h hs ht j) ⟶
      pathComp ℓ.toPrefunctor (stagePath hM h hs ht (j + 1)) :=
  have hx := h.isMoleculeIn_Iic hM hj
  have hT := (h.isMoleculeIn_orderPrefix hM j).boundary 1 true
  have hd₁ (U : LowerSet P) (α : Bool) : krullDim (P.boundary U 1 α) ≤ 1 :=
    (krullDim_boundary_le U 1 α).trans_eq Nat.cast_one
  have hVd := h.krullDim_boundary_Iic hM hj false
  have hVT := (h.isSubmoleculeOf j hj).le
  have glob (α β : Bool) :
      P.boundary (P.boundary (.Iic xs[j]) 1 β) 0 α = P.boundary (.Iic xs[j]) 0 α :=
    hx.isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)
  have ha := boundary_zero_eq_Iic_vertex (.Iic xs[j]) hx false
  have hb := boundary_zero_eq_Iic_vertex (.Iic xs[j]) hx true
  have hs' := (h.boundary_zero_boundary_orderPrefix hM j false).trans hs
  have ht' := (h.boundary_zero_boundary_orderPrefix hM j true).trans ht
  have e := pathOf_eq_pathBefore_comp hT (hd₁ _ true) (hx.boundary 1 false) hVd hVT hs'
    ((glob false false).trans ha) ((glob true false).trans hb) ht'
  eqToHom (congrArg (pathComp ℓ.toPrefunctor) e) ≫
    pathWhisker ℓ.toPrefunctor _ (ℓ.cell xs[j] (h.grade_eq _ (List.getElem_mem hj)) ha hb) _ ≫
    eqToHom (congrArg (pathComp ℓ.toPrefunctor) (pathOf_boundary_eq_comp_comp
      (h.isPastingAtIn hM hj) (h.grade_eq _ (List.getElem_mem hj))
      (h.one_le_krullDim_orderPrefix hM hj) hs' ht'
      ((h.boundary_zero_boundary_orderPrefix hM (j + 1) false).trans hs)
      ((h.boundary_zero_boundary_orderPrefix hM (j + 1) true).trans ht)
      ((glob false false).trans ha) ((glob true false).trans hb) ((glob false true).trans ha)
      ((glob true true).trans hb) _ _ e))

theorem Labelling.layerComp_eq {j : ℕ} (hj : j < xs.length) {x : P} (hxj : xs[j] = x)
    {a b : P} (ha : P.boundary (.Iic x) 0 false = .Iic a)
    (hb : P.boundary (.Iic x) 0 true = .Iic b) (p : Quiver.Path (V := EdgeQuiver P) s a)
    (c : Quiver.Path (V := EdgeQuiver P) b t)
    (h₁ : stagePath hM h hs ht j = p.comp ((pathOf (P.boundary (.Iic x) 1 false)
      ((hP x).boundary 1 false) ((krullDim_boundary_le _ 1 false).trans_eq Nat.cast_one)
      (((hP x).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans ha)
      (((hP x).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans
        hb)).comp c))
    (h₂ : p.comp ((pathOf (P.boundary (.Iic x) 1 true) ((hP x).boundary 1 true)
      ((krullDim_boundary_le _ 1 true).trans_eq Nat.cast_one)
      (((hP x).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans ha)
      (((hP x).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans
        hb)).comp c) = stagePath hM h hs ht (j + 1)) :
    ℓ.layerComp hM h hs ht j hj = eqToHom (congrArg (pathComp ℓ.toPrefunctor) h₁) ≫
      pathWhisker ℓ.toPrefunctor p (ℓ.cell x (hxj ▸ h.grade_eq _ (List.getElem_mem hj)) ha hb) c ≫
        eqToHom (congrArg (pathComp ℓ.toPrefunctor) h₂) := by
  subst hxj
  have hx := h.isMoleculeIn_Iic hM hj
  obtain rfl : a = vertex (.Iic xs[j]) hx false :=
    LowerSet.Iic_injective (ha.symm.trans (boundary_zero_eq_Iic_vertex _ hx false))
  obtain rfl : b = vertex (.Iic xs[j]) hx true :=
    LowerSet.Iic_injective (hb.symm.trans (boundary_zero_eq_Iic_vertex _ hx true))
  have hn : (pathEdges (stagePath hM h hs ht j)).Nodup := by
    rw [pathEdges_stagePath]
    exact nodup_edgeList ((h.isMoleculeIn_orderPrefix hM j).boundary 1 true)
      ((krullDim_boundary_le _ 1 true).trans_eq Nat.cast_one)
  have e := pathOf_eq_pathBefore_comp ((h.isMoleculeIn_orderPrefix hM j).boundary 1 true)
    ((krullDim_boundary_le _ 1 true).trans_eq Nat.cast_one) (hx.boundary 1 false)
    (h.krullDim_boundary_Iic hM hj false) (h.isSubmoleculeOf j hj).le
    ((h.boundary_zero_boundary_orderPrefix hM j false).trans hs)
    ((hx.isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans ha)
    ((hx.isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans hb)
    ((h.boundary_zero_boundary_orderPrefix hM j true).trans ht)
  rw [h₁] at hn
  obtain ⟨rfl, rfl⟩ := eq_and_eq_of_comp_comp_eq hn (length_pathOf_ne_zero _
    (h.krullDim_boundary_Iic hM hj false) _ _) (h₁.symm.trans e)
  rfl

def Labelling.compositeUpTo : (n : ℕ) → n ≤ xs.length →
    (pathComp ℓ.toPrefunctor (stagePath hM h hs ht 0) ⟶
      pathComp ℓ.toPrefunctor (stagePath hM h hs ht n))
  | 0, _ => 𝟙 _
  | n + 1, hn => Labelling.compositeUpTo n (by omega) ≫ ℓ.layerComp hM h hs ht n hn

@[simp]
theorem Labelling.compositeUpTo_zero (hn : 0 ≤ xs.length) : ℓ.compositeUpTo hM h hs ht 0 hn = 𝟙 _ :=
  rfl

theorem Labelling.compositeUpTo_succ {n : ℕ} (hn : n + 1 ≤ xs.length) :
    ℓ.compositeUpTo hM h hs ht (n + 1) hn =
      ℓ.compositeUpTo hM h hs ht n (by omega) ≫ ℓ.layerComp hM h hs ht n hn :=
  rfl

def Labelling.compositeAlong :
    pathComp ℓ.toPrefunctor (pathOf (P.boundary M 1 false) (hM.boundary 1 false)
        ((krullDim_boundary_le _ 1 false).trans_eq Nat.cast_one)
        ((hM.isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans hs)
        ((hM.isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans ht)) ⟶
      pathComp ℓ.toPrefunctor (pathOf (P.boundary M 1 true) (hM.boundary 1 true)
        ((krullDim_boundary_le _ 1 true).trans_eq Nat.cast_one)
        ((hM.isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans hs)
        ((hM.isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans ht)) :=
  eqToHom (congrArg (pathComp ℓ.toPrefunctor) (stagePath_zero hM h hs ht).symm) ≫
    ℓ.compositeUpTo hM h hs ht xs.length le_rfl ≫
      eqToHom (congrArg (pathComp ℓ.toPrefunctor) (stagePath_length hM h hs ht))

def Labelling.pathCell : PathCell B :=
  ⟨ℓ.toPrefunctor.obj s, ℓ.toPrefunctor.obj t,
    ℓ.toPrefunctor.mapPath (pathOf (P.boundary M 1 false) (hM.boundary 1 false)
      ((krullDim_boundary_le _ 1 false).trans_eq Nat.cast_one)
      ((hM.isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans hs)
      ((hM.isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans ht)),
    ℓ.toPrefunctor.mapPath (pathOf (P.boundary M 1 true) (hM.boundary 1 true)
      ((krullDim_boundary_le _ 1 true).trans_eq Nat.cast_one)
      ((hM.isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans hs)
      ((hM.isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans ht)),
    eqToHom (pathComp_mapPath ℓ.toPrefunctor _) ≫ ℓ.compositeAlong hM h hs ht ≫
      eqToHom (pathComp_mapPath ℓ.toPrefunctor _).symm⟩

@[simp]
theorem Labelling.dom_pathCell : (ℓ.pathCell hM h hs ht).dom =
    ℓ.toPrefunctor.mapPath (pathOf (P.boundary M 1 false) (hM.boundary 1 false)
      ((krullDim_boundary_le _ 1 false).trans_eq Nat.cast_one)
      ((hM.isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans hs)
      ((hM.isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans ht)) :=
  rfl

@[simp]
theorem Labelling.cod_pathCell : (ℓ.pathCell hM h hs ht).cod =
    ℓ.toPrefunctor.mapPath (pathOf (P.boundary M 1 true) (hM.boundary 1 true)
      ((krullDim_boundary_le _ 1 true).trans_eq Nat.cast_one)
      ((hM.isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans hs)
      ((hM.isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans ht)) :=
  rfl

theorem Labelling.hom_pathCell_heq : (ℓ.pathCell hM h hs ht).hom ≍ ℓ.compositeAlong hM h hs ht :=
  (eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)

private theorem eqToHom_comp_eqToHom_chain {C : Type*} [Category C] {X X₁ X₂ Y Y₁ Y₂ : C}
    (f : X ⟶ Y) (a : X = X₁) (b : X₁ = X₂) (c : X₂ = X) (d : Y = Y₁) (e : Y₁ = Y₂) (g : Y₂ = Y) :
    eqToHom a ≫ eqToHom b ≫ eqToHom c ≫ f ≫ eqToHom d ≫ eqToHom e ≫ eqToHom g = f := by
  subst a b d e
  simp

omit [DecidablePred (· ∈ M)] in
theorem Labelling.compositeAlong_Iic {x : P} (hx : grade ℕ x = 2)
    (hs : P.boundary (.Iic x) 0 false = .Iic s) (ht : P.boundary (.Iic x) 0 true = .Iic t) :
    ℓ.compositeAlong (hP x) (isLayerOrder_Iic (hP x) hx) hs ht = ℓ.cell x hx hs ht := by
  have h := isLayerOrder_Iic (hP x) hx
  have h₁ : stagePath (hP x) h hs ht 0 = Quiver.Path.nil.comp ((pathOf
      (P.boundary (.Iic x) 1 false) ((hP x).boundary 1 false)
      ((krullDim_boundary_le _ 1 false).trans_eq Nat.cast_one)
      (((hP x).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans hs)
      (((hP x).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans
        ht)).comp Quiver.Path.nil) :=
    (stagePath_zero (hP x) h hs ht).trans (Quiver.Path.nil_comp _).symm
  have h₂ : Quiver.Path.nil.comp ((pathOf (P.boundary (.Iic x) 1 true) ((hP x).boundary 1 true)
      ((krullDim_boundary_le _ 1 true).trans_eq Nat.cast_one)
      (((hP x).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans hs)
      (((hP x).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans
        ht)).comp Quiver.Path.nil) = stagePath (hP x) h hs ht (0 + 1) :=
    (Quiver.Path.nil_comp _).trans (stagePath_length (hP x) h hs ht).symm
  have e : ℓ.compositeUpTo (hP x) h hs ht [x].length le_rfl =
      ℓ.layerComp (hP x) h hs ht 0 (by simp) ≫
        eqToHom (congrArg (pathComp ℓ.toPrefunctor) (rfl : stagePath (hP x) h hs ht (0 + 1) =
          stagePath (hP x) h hs ht [x].length)) := by
    rw [eqToHom_refl, Category.comp_id]
    exact Category.id_comp _
  rw [Labelling.compositeAlong, e,
    ℓ.layerComp_eq (hP x) h hs ht (j := 0) (by simp) (x := x) rfl hs ht _ _ h₁ h₂,
    pathWhisker_nil_nil]
  dsimp only [Quiver.Path.comp_nil, List.length_singleton, Nat.reduceAdd]
  simp only [Category.assoc, eqToHom_refl, Category.id_comp]
  exact eqToHom_comp_eqToHom_chain _ _ _ _ _ _ _

theorem Labelling.compositeAlong_nil (hd : krullDim M ≤ 1) :
    ℓ.compositeAlong hM (isLayerOrder_nil hd) hs ht = eqToHom (congrArg (pathComp ℓ.toPrefunctor)
      (pathOf_congr ((boundary_eq_self (hd.trans_eq Nat.cast_one.symm) false).trans
        (boundary_eq_self (hd.trans_eq Nat.cast_one.symm) true).symm))) := by
  rw [Labelling.compositeAlong]
  simp only [List.length_nil, Labelling.compositeUpTo_zero, Category.id_comp, eqToHom_trans]

variable {pre post : List P} {x y : P}

omit [Fintype P] [DecidableLE P] [DecidablePred (· ∈ M)] in
theorem orderPrefix_swap {j : ℕ} (hj : j ≠ pre.length + 1) :
    orderPrefix M (pre ++ y :: x :: post) j = orderPrefix M (pre ++ x :: y :: post) j := by
  refine SetLike.ext fun z => ?_
  rw [mem_orderPrefix, mem_orderPrefix, List.take_append, List.take_append]
  refine or_congr Iff.rfl (exists_congr fun w => and_congr_left fun _ => ?_)
  rcases hk : j - pre.length with _ | _ | n
  · simp
  · omega
  · simp only [List.take_succ_cons, List.mem_append, List.mem_cons]
    tauto

omit [Fintype P] [DecidableLE P] [DecidablePred (· ∈ M)] in
private theorem IsLayerOrder.not_mem_boundary_Iic_swap
    (h : IsLayerOrder M (pre ++ x :: y :: post))
    (hM : IsMoleculeIn P M) {e : P} (hex : e ∈ P.boundary (.Iic x) 1 false)
    (hey : e ∈ P.boundary (.Iic y) 1 false) (he : grade ℕ e = 1) : False := by
  have hk : pre.length < (pre ++ x :: y :: post).length := by simp
  have hk' : pre.length + 1 < (pre ++ x :: y :: post).length := by simp
  have hxk : (pre ++ x :: y :: post)[pre.length] = x := by simp
  have hyk : (pre ++ x :: y :: post)[pre.length + 1] = y := by simp
  have hp := h.isPastingAtIn hM hk
  have hy := (h.isSubmoleculeOf _ hk').le
  have hxd := h.krullDim_boundary_Iic hM hk false
  have hT := h.one_le_krullDim_orderPrefix hM hk
  rw [hxk] at hp hxd
  rw [hyk] at hy
  have hxM : x ∈ M := h.mem (by simp)
  have hx2 : grade ℕ x = 2 := h.grade_eq x (by simp)
  have hkS : ((1 : ℕ) : WithBot ℕ∞) ≤ krullDim (LowerSet.Iic x) := by
    rw [LowerSet.krullDim_Iic, hx2]
    exact_mod_cast one_le_two
  have hR := hp.coe_boundary_eq hkS hT
  rw [hp.inf_eq] at hR
  have heR : e ∈ (P.boundary (orderPrefix M (pre ++ x :: y :: post) (pre.length + 1)) 1 true :
      Set P) := hy hey
  rw [hR] at heR
  rcases heR with ⟨-, hei⟩ | hex'
  · refine hei ((mem_interior_iff_of_isMoleculeIn (hp.isMoleculeIn_left.boundary 1 false) hex).2
      (.inl ?_))
    rw [he, hxd]
    rfl
  · have hU : krullDim (LowerSet.Iic x) = (1 : ℕ) + 1 := by
      rw [LowerSet.krullDim_Iic, hx2]
      rfl
    have hb : e ∈ P.bdry (.Iic x) false ⊓ P.bdry (.Iic x) true := by
      rw [bdry_eq_boundary hU, bdry_eq_boundary hU]
      exact ⟨hex, hex'⟩
    rw [bdry_Iic_inf_bdry_Iic_of_grade_eq_two (hM.isAtomIn_Iic hxM) hx2,
      mem_boundaryFull] at hb
    obtain ⟨α, hα⟩ := hb
    have h0 : grade ℕ e ≤ 0 := krullDim_le_coe_iff.1 (krullDim_boundary_le _ 0 α) ⟨e, hα⟩
    omega

end Path

section Swap

variable {pre post : List P} {x y : P}

private theorem getElem_swap {j : ℕ} (hj : j < (pre ++ y :: x :: post).length)
    (hjk : j ≠ pre.length) (hjk' : j ≠ pre.length + 1) :
    (pre ++ y :: x :: post)[j] = (pre ++ x :: y :: post)[j]'(by simpa using hj) := by
  rw [List.getElem_append, List.getElem_append]
  split_ifs with h₁
  · rfl
  · obtain ⟨n, hn⟩ : ∃ n, j - pre.length = n + 2 := ⟨j - pre.length - 2, by omega⟩
    simp only [hn, List.getElem_cons_succ]

theorem IsLayerOrder.swap [Finite P] (h : IsLayerOrder M (pre ++ x :: y :: post))
    (hM : IsMoleculeIn P M)
    (hy : P.boundary (.Iic y) 1 false ≤
      P.boundary (orderPrefix M (pre ++ x :: y :: post) pre.length) 1 true) :
    IsLayerOrder M (pre ++ y :: x :: post) := by
  classical
  have := Fintype.ofFinite P
  have hk : pre.length < (pre ++ x :: y :: post).length := by simp
  have hk' : pre.length + 1 < (pre ++ x :: y :: post).length := by simp
  have hxk : (pre ++ x :: y :: post)[pre.length] = x := by simp
  have hyk : (pre ++ x :: y :: post)[pre.length + 1] = y := by simp
  have hxk' : (pre ++ y :: x :: post)[pre.length + 1]'(by simp) = x := by simp
  have hyk' : (pre ++ y :: x :: post)[pre.length]'(by simp) = y := by simp
  have hlen : (pre ++ y :: x :: post).length = (pre ++ x :: y :: post).length := by simp
  have hT := h.isMoleculeIn_orderPrefix hM pre.length
  have hxM := h.isMoleculeIn_Iic hM hk
  have hyM := h.isMoleculeIn_Iic hM hk'
  have hxd := h.krullDim_boundary_Iic hM hk false
  have hyd := h.krullDim_boundary_Iic hM hk' false
  have hx₄ := (h.isSubmoleculeOf _ hk).le
  have hx₁ := h.Iic_inf_orderPrefix _ hk
  have hy₁ := h.Iic_inf_orderPrefix _ hk'
  have hsucc := orderPrefix_succ (M := M) hk
  rw [hxk] at hxM hxd hx₁ hx₄ hsucc
  rw [hyk] at hyM hyd hy₁
  have hR : orderPrefix M (pre ++ y :: x :: post) (pre.length + 1) =
      orderPrefix M (pre ++ x :: y :: post) pre.length ⊔ .Iic y := by
    rw [orderPrefix_succ (by simp), hyk', orderPrefix_swap (by omega)]
  have hy₂ : .Iic y ⊓ orderPrefix M (pre ++ x :: y :: post) pre.length =
      P.boundary (.Iic y) 1 false := by
    refine le_antisymm ((inf_le_inf_left _ ?_).trans hy₁.le)
      (le_inf (boundary_le _ 1 false) (hy.trans (boundary_le _ 1 true)))
    rw [hsucc]
    exact le_sup_left
  have hy₃ : P.IsSubmoleculeOf (P.boundary (.Iic y) 1 false)
      (P.boundary (orderPrefix M (pre ++ x :: y :: post) pre.length) 1 true) :=
    isSubmoleculeOf_of_le (hT.boundary 1 true) ((krullDim_boundary_le _ 1 true).trans_eq
      Nat.cast_one) (hyM.boundary 1 false) hyd hy
  have hpy : P.IsPastingAtIn 1 true (.Iic y) (orderPrefix M (pre ++ x :: y :: post) pre.length)
      (orderPrefix M (pre ++ y :: x :: post) (pre.length + 1)) :=
    ⟨hyM, hT, by rw [hR, sup_comm], hy₂, hy₂ ▸ hy₃⟩
  have hx₂ : .Iic x ⊓ orderPrefix M (pre ++ y :: x :: post) (pre.length + 1) =
      P.boundary (.Iic x) 1 false := by
    rw [hR, inf_sup_left, hx₁, sup_eq_left]
    rintro z ⟨hzx, hzy⟩
    have hz : z ∈ LowerSet.Iic y ⊓ orderPrefix M (pre ++ x :: y :: post) (pre.length + 1) := by
      rw [hsucc]
      exact ⟨hzy, .inr hzx⟩
    rw [hy₁] at hz
    rw [← hx₁]
    exact ⟨hzx, boundary_le _ 1 true (hy hz)⟩
  have hx₃ : P.boundary (.Iic x) 1 false ≤
      P.boundary (orderPrefix M (pre ++ y :: x :: post) (pre.length + 1)) 1 true := by
    obtain ⟨s, -, hs⟩ := exists_boundary_zero_eq_Iic (hT.boundary 1 true) false
    obtain ⟨t, -, ht⟩ := exists_boundary_zero_eq_Iic (hT.boundary 1 true) true
    obtain ⟨a, -, ha⟩ := exists_boundary_zero_eq_Iic hxM false
    obtain ⟨b, -, hb⟩ := exists_boundary_zero_eq_Iic hxM true
    obtain ⟨c, -, hc⟩ := exists_boundary_zero_eq_Iic hyM false
    obtain ⟨d, -, hd⟩ := exists_boundary_zero_eq_Iic hyM true
    have gT (α : Bool) := hT.isGlobular.boundary_boundary_eq_of_le zero_le_one
      (.inl zero_lt_one) (α := α) (β := true)
    have gR (α : Bool) := hpy.isMoleculeIn.isGlobular.boundary_boundary_eq_of_le zero_le_one
      (.inl zero_lt_one) (α := α) (β := true)
    have gR' (α : Bool) := hpy.isMoleculeIn.isGlobular.boundary_boundary_eq_of_le zero_le_one
      (.inl zero_lt_one) (α := α) (β := false)
    have gT' (α : Bool) := hT.isGlobular.boundary_boundary_eq_of_le zero_le_one
      (.inl zero_lt_one) (α := α) (β := false)
    have gx (α β : Bool) := hxM.isGlobular.boundary_boundary_eq_of_le zero_le_one
      (.inl zero_lt_one) (α := α) (β := β)
    have gy (α β : Bool) := hyM.isGlobular.boundary_boundary_eq_of_le zero_le_one
      (.inl zero_lt_one) (α := α) (β := β)
    have hRs (α : Bool) : P.boundary (P.boundary (orderPrefix M (pre ++ y :: x :: post)
        (pre.length + 1)) 1 true) 0 α = P.boundary (P.boundary (orderPrefix M
          (pre ++ x :: y :: post) pre.length) 1 true) 0 α := by
      have hbn : P.boundary (orderPrefix M (pre ++ y :: x :: post) (pre.length + 1)) 1 false =
          P.boundary (orderPrefix M (pre ++ x :: y :: post) pre.length) 1 false :=
        hpy.boundary_not
      rw [gR, ← gR', hbn, gT', gT]
    have hd₁ (U : LowerSet P) (α : Bool) : krullDim (P.boundary U 1 α) ≤ 1 :=
      (krullDim_boundary_le U 1 α).trans_eq Nat.cast_one
    have hmem {r : Quiver.Path (V := EdgeQuiver P) s t}
        (hr : r = pathOf _ (hpy.isMoleculeIn.boundary 1 true) (hd₁ _ true)
          ((hRs false).trans hs) ((hRs true).trans ht))
        (hx : ∀ e ∈ edgeList (P.boundary (.Iic x) 1 false), e ∈ pathEdges r) :
        P.boundary (.Iic x) 1 false ≤ P.boundary (orderPrefix M (pre ++ y :: x :: post)
          (pre.length + 1)) 1 true := by
      refine le_of_forall_mem_edgeList (hxM.boundary 1 false) hxd.le
        (edgeList_ne_nil (hxM.boundary 1 false) hxd) fun e he => ?_
      have := hx e he
      rw [hr, pathEdges_pathOf] at this
      exact ((mem_edgeList_iff (hpy.isMoleculeIn.boundary 1 true) (hd₁ _ true)).1 this).1
    rcases exists_pathOf_eq_comp_comp_or (hT.boundary 1 true) (hd₁ _ true)
        (hxM.boundary 1 false) hxd hx₄ (hyM.boundary 1 false) hyd hy
        (fun e he he' he1 => h.not_mem_boundary_Iic_swap hM he he' he1) hs ht
        ((gx false false).trans ha) ((gx true false).trans hb) ((gy false false).trans hc)
        ((gy true false).trans hd) with ⟨p, m, r, e⟩ | ⟨p, m, r, e⟩
    · refine hmem (pathOf_boundary_eq_comp_comp hpy (h.grade_eq y (by simp))
        (h.one_le_krullDim_orderPrefix hM hk) hs ht ((hRs false).trans hs) ((hRs true).trans ht)
        ((gy false false).trans hc) ((gy true false).trans hd) ((gy false true).trans hc)
        ((gy true true).trans hd) (p.comp ((pathOf _ (hxM.boundary 1 false) hxd.le
          ((gx false false).trans ha) ((gx true false).trans hb)).comp m)) r
        (e.trans (by simp only [Quiver.Path.comp_assoc]))) fun e he => ?_
      simp [he]
    · refine hmem (pathOf_boundary_eq_comp_comp hpy (h.grade_eq y (by simp))
        (h.one_le_krullDim_orderPrefix hM hk) hs ht ((hRs false).trans hs) ((hRs true).trans ht)
        ((gy false false).trans hc) ((gy true false).trans hd) ((gy false true).trans hc)
        ((gy true true).trans hd) p (m.comp ((pathOf _ (hxM.boundary 1 false) hxd.le
          ((gx false false).trans ha) ((gx true false).trans hb)).comp r)) e) fun e he => ?_
      simp [he]
  refine ⟨fun z hz => h.grade_eq z (by simp only [List.mem_append, List.mem_cons] at hz ⊢; tauto),
    fun j hj => ?_, fun j hj => ?_, ?_⟩
  · by_cases hjk : j = pre.length
    · subst hjk
      rw [hyk', orderPrefix_swap (by omega)]
      exact hy₂
    by_cases hjk' : j = pre.length + 1
    · subst hjk'
      rw [hxk']
      exact hx₂
    rw [getElem_swap hj hjk hjk', orderPrefix_swap hjk']
    exact h.Iic_inf_orderPrefix j _
  · by_cases hjk : j = pre.length
    · subst hjk
      rw [hyk', orderPrefix_swap (by omega)]
      exact hy₃
    by_cases hjk' : j = pre.length + 1
    · subst hjk'
      rw [hxk']
      exact isSubmoleculeOf_of_le (hpy.isMoleculeIn.boundary 1 true)
        ((krullDim_boundary_le _ 1 true).trans_eq Nat.cast_one) (hxM.boundary 1 false) hxd hx₃
    rw [getElem_swap hj hjk hjk', orderPrefix_swap hjk']
    exact h.isSubmoleculeOf j _
  · rw [hlen, orderPrefix_swap (by simp)]
    exact h.orderPrefix_length

variable [Fintype P] [DecidableLE P] [DecidablePred (· ∈ M)] {s t : P}
  (hs : P.boundary M 0 false = .Iic s) (ht : P.boundary M 0 true = .Iic t)

theorem IsLayerOrder.exists_stagePath_eq (hM : IsMoleculeIn P M) (h : IsLayerOrder M xs)
    {j : ℕ} (hj : j < xs.length) {a b : P} (ha : P.boundary (.Iic xs[j]) 0 false = .Iic a)
    (hb : P.boundary (.Iic xs[j]) 0 true = .Iic b) :
    ∃ (p : Quiver.Path (V := EdgeQuiver P) s a) (c : Quiver.Path (V := EdgeQuiver P) b t),
      stagePath hM h hs ht j = p.comp ((pathOf (P.boundary (.Iic xs[j]) 1 false)
        ((h.isMoleculeIn_Iic hM hj).boundary 1 false) (h.krullDim_boundary_Iic hM hj false).le
        (((h.isMoleculeIn_Iic hM hj).isGlobular.boundary_boundary_eq_of_le zero_le_one
          (.inl zero_lt_one)).trans ha)
        (((h.isMoleculeIn_Iic hM hj).isGlobular.boundary_boundary_eq_of_le zero_le_one
          (.inl zero_lt_one)).trans hb)).comp c) :=
  ⟨_, _, pathOf_eq_pathBefore_comp ((h.isMoleculeIn_orderPrefix hM j).boundary 1 true)
    ((krullDim_boundary_le _ 1 true).trans_eq Nat.cast_one)
    ((h.isMoleculeIn_Iic hM hj).boundary 1 false) (h.krullDim_boundary_Iic hM hj false)
    (h.isSubmoleculeOf j hj).le _ _ _ _⟩

theorem IsLayerOrder.comp_comp_eq_stagePath (hM : IsMoleculeIn P M)
    (h : IsLayerOrder M xs) {j : ℕ} (hj : j < xs.length) {x : P} (hxj : xs[j] = x)
    (hx : IsMoleculeIn P (.Iic x)) {a b : P} (ha : P.boundary (.Iic x) 0 false = .Iic a)
    (hb : P.boundary (.Iic x) 0 true = .Iic b) (p : Quiver.Path (V := EdgeQuiver P) s a)
    (c : Quiver.Path (V := EdgeQuiver P) b t)
    (e : stagePath hM h hs ht j = p.comp ((pathOf (P.boundary (.Iic x) 1 false)
      (hx.boundary 1 false) ((krullDim_boundary_le _ 1 false).trans_eq Nat.cast_one)
      ((hx.isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans ha)
      ((hx.isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans hb)).comp
        c)) :
    p.comp ((pathOf (P.boundary (.Iic x) 1 true) (hx.boundary 1 true)
      ((krullDim_boundary_le _ 1 true).trans_eq Nat.cast_one)
      ((hx.isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans ha)
      ((hx.isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans hb)).comp
        c) = stagePath hM h hs ht (j + 1) := by
  subst hxj
  exact pathOf_boundary_eq_comp_comp (h.isPastingAtIn hM hj) (h.grade_eq _ (List.getElem_mem hj))
    (h.one_le_krullDim_orderPrefix hM hj) _ _ _ _ _ _ _ _ p c e

theorem stagePath_eq_of_boundary_eq (hM : IsMoleculeIn P M) (h : IsLayerOrder M xs)
    {M' : LowerSet P} [DecidablePred (· ∈ M')] (hM' : IsMoleculeIn P M') {ys : List P}
    (h' : IsLayerOrder M' ys) (hs' : P.boundary M' 0 false = .Iic s)
    (ht' : P.boundary M' 0 true = .Iic t) {j k : ℕ}
    (e : P.boundary (orderPrefix M xs j) 1 true = P.boundary (orderPrefix M' ys k) 1 true) :
    stagePath hM h hs ht j = stagePath hM' h' hs' ht' k := by
  refine eq_pathOf_of_forall_mem _ _ _ _ _ fun y hy => ?_
  rw [pathEdges_stagePath] at hy
  have hy' := ((mem_edgeList_iff ((h.isMoleculeIn_orderPrefix hM j).boundary 1 true)
    ((krullDim_boundary_le _ 1 true).trans_eq Nat.cast_one)).1 hy).1
  rwa [e] at hy'

variable {B : Type u₁} [Bicategory.{w, v} B] {hP : P.IsRDC} (ℓ : Labelling B P hP)

theorem Labelling.layerComp_eq_of_stagePath_eq (hM : IsMoleculeIn P M) (h : IsLayerOrder M xs)
    {M' : LowerSet P} [DecidablePred (· ∈ M')] (hM' : IsMoleculeIn P M') {ys : List P}
    (h' : IsLayerOrder M' ys) (hs' : P.boundary M' 0 false = .Iic s)
    (ht' : P.boundary M' 0 true = .Iic t) {j k : ℕ} (hj : j < xs.length) (hk : k < ys.length)
    (hx : xs[j] = ys[k]) (e₀ : stagePath hM h hs ht j = stagePath hM' h' hs' ht' k)
    (e₁ : stagePath hM h hs ht (j + 1) = stagePath hM' h' hs' ht' (k + 1)) :
    ℓ.layerComp hM h hs ht j hj = eqToHom (congrArg (pathComp ℓ.toPrefunctor) e₀) ≫
      ℓ.layerComp hM' h' hs' ht' k hk ≫ eqToHom (congrArg (pathComp ℓ.toPrefunctor) e₁.symm) := by
  have hx' := hP ys[k]
  have ha := boundary_zero_eq_Iic_vertex _ hx' false
  have hb := boundary_zero_eq_Iic_vertex _ hx' true
  obtain ⟨p, c, e⟩ := h'.exists_stagePath_eq hs' ht' hM' hk ha hb
  have e' := h'.comp_comp_eq_stagePath hs' ht' hM' hk rfl hx' ha hb p c e
  rw [ℓ.layerComp_eq hM h hs ht hj hx ha hb p c (e₀.trans e) (e'.trans e₁.symm),
    ℓ.layerComp_eq hM' h' hs' ht' hk rfl ha hb p c e e']
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]

theorem Labelling.compositeAlong_swap (hM : IsMoleculeIn P M)
    (h : IsLayerOrder M (pre ++ x :: y :: post))
    (hy : P.boundary (.Iic y) 1 false ≤
      P.boundary (orderPrefix M (pre ++ x :: y :: post) pre.length) 1 true) :
    ℓ.compositeAlong hM h hs ht = ℓ.compositeAlong hM (h.swap hM hy) hs ht := by
  have h' := h.swap hM hy
  have hlen : (pre ++ y :: x :: post).length = (pre ++ x :: y :: post).length := by simp
  have hS (j : ℕ) (hj : j ≠ pre.length + 1) :
      stagePath hM h' hs ht j = stagePath hM h hs ht j :=
    stagePath_eq_of_boundary_eq hs ht hM h' hM h hs ht (by rw [orderPrefix_swap hj])
  have hL (j : ℕ) (hj : j < (pre ++ x :: y :: post).length)
      (hj' : j < (pre ++ y :: x :: post).length) (hjk : j ≠ pre.length)
      (hjk' : j ≠ pre.length + 1) :
      ℓ.layerComp hM h' hs ht j hj' = eqToHom (congrArg (pathComp ℓ.toPrefunctor) (hS j hjk')) ≫
        ℓ.layerComp hM h hs ht j hj ≫
          eqToHom (congrArg (pathComp ℓ.toPrefunctor) (hS (j + 1) (by omega)).symm) :=
    ℓ.layerComp_eq_of_stagePath_eq hs ht hM h' hM h hs ht hj' hj (getElem_swap hj' hjk hjk')
      (hS j hjk') (hS (j + 1) (by omega))
  have hk : pre.length < (pre ++ x :: y :: post).length := by simp
  have hk' : pre.length + 1 < (pre ++ x :: y :: post).length := by simp
  have hkk : pre.length < (pre ++ y :: x :: post).length := by simp
  have hkk' : pre.length + 1 < (pre ++ y :: x :: post).length := by simp
  have hxM := hP x
  have hyM := hP y
  have hax := boundary_zero_eq_Iic_vertex _ hxM false
  have hbx := boundary_zero_eq_Iic_vertex _ hxM true
  have hay := boundary_zero_eq_Iic_vertex _ hyM false
  have hby := boundary_zero_eq_Iic_vertex _ hyM true
  have gx (α β : Bool) := hxM.isGlobular.boundary_boundary_eq_of_le zero_le_one
    (.inl zero_lt_one) (α := α) (β := β)
  have gy (α β : Bool) := hyM.isGlobular.boundary_boundary_eq_of_le zero_le_one
    (.inl zero_lt_one) (α := α) (β := β)
  have hxd := h.krullDim_boundary_Iic hM hk false
  have hyd := h.krullDim_boundary_Iic hM hk' false
  have hxQ := (h.isSubmoleculeOf _ hk).le
  have hxk : (pre ++ x :: y :: post)[pre.length] = x := by simp
  have hyk : (pre ++ x :: y :: post)[pre.length + 1] = y := by simp
  rw [hxk] at hxd hxQ
  rw [hyk] at hyd
  have h2 : ℓ.layerComp hM h' hs ht pre.length hkk ≫ ℓ.layerComp hM h' hs ht (pre.length + 1) hkk' =
      eqToHom (congrArg (pathComp ℓ.toPrefunctor) (hS _ (by omega))) ≫
        ℓ.layerComp hM h hs ht pre.length hk ≫ ℓ.layerComp hM h hs ht (pre.length + 1) hk' ≫
          eqToHom (congrArg (pathComp ℓ.toPrefunctor)
            (hS (pre.length + 1 + 1) (by omega)).symm) := by
    rcases exists_pathOf_eq_comp_comp_or ((h.isMoleculeIn_orderPrefix hM _).boundary 1 true)
        ((krullDim_boundary_le _ 1 true).trans_eq Nat.cast_one) (hxM.boundary 1 false) hxd hxQ
        (hyM.boundary 1 false) hyd hy
        (fun e he he' he1 => h.not_mem_boundary_Iic_swap hM he he' he1)
        ((h.boundary_zero_boundary_orderPrefix hM _ false).trans hs)
        ((h.boundary_zero_boundary_orderPrefix hM _ true).trans ht) ((gx false false).trans hax)
        ((gx true false).trans hbx) ((gy false false).trans hay) ((gy true false).trans hby) with
      ⟨p, m, r, e⟩ | ⟨p, m, r, e⟩
    · have e₁ := h.comp_comp_eq_stagePath hs ht hM hk hxk hxM hax hbx p _ e
      have e₁' := e₁.symm.trans ((congrArg p.comp (Quiver.Path.comp_assoc _ m _).symm).trans
        (Quiver.Path.comp_assoc p _ _).symm)
      have e₂ := h.comp_comp_eq_stagePath hs ht hM hk' hyk hyM hay hby _ r e₁'
      have e₃₀ := (hS _ (by omega)).trans (e.trans ((congrArg p.comp
        (Quiver.Path.comp_assoc _ m _).symm).trans (Quiver.Path.comp_assoc p _ _).symm))
      have e₃ := h'.comp_comp_eq_stagePath hs ht hM hkk (by simp) hyM hay hby _ r e₃₀
      have e₃' := e₃.symm.trans ((Quiver.Path.comp_assoc p _ _).trans
        (congrArg p.comp (Quiver.Path.comp_assoc _ m _)))
      have e₄ := h'.comp_comp_eq_stagePath hs ht hM hkk' (by simp) hxM hax hbx p _ e₃'
      rw [ℓ.layerComp_eq hM h hs ht hk hxk hax hbx p _ e e₁,
        ℓ.layerComp_eq hM h hs ht hk' hyk hay hby _ r e₁' e₂,
        ℓ.layerComp_eq hM h' hs ht hkk (by simp) hay hby _ r e₃₀ e₃,
        ℓ.layerComp_eq hM h' hs ht hkk' (by simp) hax hbx p _ e₃' e₄]
      simp only [Category.assoc, eqToHom_trans_assoc]
      rw [pathWhisker_exchange_assoc]
      simp only [eqToHom_trans_assoc, eqToHom_trans]
    · have e₀ := e.trans ((congrArg p.comp (Quiver.Path.comp_assoc _ m _).symm).trans
        (Quiver.Path.comp_assoc p _ _).symm)
      have e₁ := h.comp_comp_eq_stagePath hs ht hM hk hxk hxM hax hbx _ r e₀
      have e₁' := e₁.symm.trans ((Quiver.Path.comp_assoc p _ _).trans
        (congrArg p.comp (Quiver.Path.comp_assoc _ m _)))
      have e₂ := h.comp_comp_eq_stagePath hs ht hM hk' hyk hyM hay hby p _ e₁'
      have e₃₀ := (hS _ (by omega)).trans e
      have e₃ := h'.comp_comp_eq_stagePath hs ht hM hkk (by simp) hyM hay hby p _ e₃₀
      have e₃' := e₃.symm.trans ((congrArg p.comp (Quiver.Path.comp_assoc _ m _).symm).trans
        (Quiver.Path.comp_assoc p _ _).symm)
      have e₄ := h'.comp_comp_eq_stagePath hs ht hM hkk' (by simp) hxM hax hbx _ r e₃'
      rw [ℓ.layerComp_eq hM h hs ht hk hxk hax hbx _ r e₀ e₁,
        ℓ.layerComp_eq hM h hs ht hk' hyk hay hby p _ e₁' e₂,
        ℓ.layerComp_eq hM h' hs ht hkk (by simp) hay hby p _ e₃₀ e₃,
        ℓ.layerComp_eq hM h' hs ht hkk' (by simp) hax hbx _ r e₃' e₄]
      simp only [Category.assoc, eqToHom_trans_assoc]
      rw [pathWhisker_exchange_assoc]
      simp only [eqToHom_trans_assoc, eqToHom_trans]
  have claim (n : ℕ) (hn : n ≤ (pre ++ x :: y :: post).length)
      (hn' : n ≤ (pre ++ y :: x :: post).length) (hnk : n ≠ pre.length + 1) :
      ℓ.compositeUpTo hM h' hs ht n hn' =
        eqToHom (congrArg (pathComp ℓ.toPrefunctor) (hS 0 (by omega))) ≫
          ℓ.compositeUpTo hM h hs ht n hn ≫
            eqToHom (congrArg (pathComp ℓ.toPrefunctor) (hS n hnk).symm) := by
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases n with _ | n
      · simp
      by_cases hnk' : n = pre.length + 1
      · subst hnk'
        rw [ℓ.compositeUpTo_succ, ℓ.compositeUpTo_succ, ih pre.length (by omega) (by omega)
          (by omega) (by omega), ℓ.compositeUpTo_succ, ℓ.compositeUpTo_succ]
        simp only [Category.assoc]
        rw [h2]
        simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      · rw [ℓ.compositeUpTo_succ, ih n (by omega) (by omega) (by omega) hnk',
          hL n (by omega) (by omega) (by omega) hnk', ℓ.compositeUpTo_succ]
        simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  have hC (n₁ n₂ : ℕ) (e : n₁ = n₂) (hn₁ : n₁ ≤ (pre ++ x :: y :: post).length)
      (hn₂ : n₂ ≤ (pre ++ x :: y :: post).length) {Z : ℓ.toPrefunctor.obj s ⟶ ℓ.toPrefunctor.obj t}
      (p₁ : pathComp ℓ.toPrefunctor (stagePath hM h hs ht n₁) = Z)
      (p₂ : pathComp ℓ.toPrefunctor (stagePath hM h hs ht n₂) = Z) :
      ℓ.compositeUpTo hM h hs ht n₁ hn₁ ≫ eqToHom p₁ = ℓ.compositeUpTo hM h hs ht n₂ hn₂ ≫
        eqToHom p₂ := by
    subst e
    rfl
  rw [Labelling.compositeAlong, Labelling.compositeAlong,
    claim _ (by omega) le_rfl (by simp)]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  congr 1
  exact hC _ _ hlen.symm _ _ _ _

end Swap

end Atoms.Molecule.OGP
