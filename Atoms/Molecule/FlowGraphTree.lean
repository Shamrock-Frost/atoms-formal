import Atoms.Molecule.FlowGraph
import Atoms.Molecule.Layering.Ordering

universe u

open CategoryTheory Order Set

namespace Atoms.Molecule.OGP

variable {P : OGP.{u}}

theorem IsMoleculeIn.exists_sink_reflTransGen_maximalFlowGraph {U : LowerSet P} {n : ℕ}
    (hU : IsMoleculeIn P U) (hd : krullDim U = (n + 1 : ℕ)) {x : P}
    (hx : x ∈ P.topsAbove U n) :
    ∃ r ∈ P.topsAbove U n, Relation.ReflTransGen (P.maximalFlowGraph U n).Adj x r ∧
      ∀ y, ¬ (P.maximalFlowGraph U n).Adj r y := by
  let R := (P.maximalFlowGraph U n).Adj
  let S := {r | r ∈ P.topsAbove U n ∧ Relation.ReflTransGen R x r}
  have hfin : S.Finite := hU.finite.subset fun _ h => h.1.1.prop
  have hne : S.Nonempty := ⟨x, hx, .refl⟩
  obtain ⟨r, hr, hsink⟩ :=
    (hU.isAcyclic_maximalFlowGraph_of_krullDim_eq hd).exists_forall_not_adj_right hfin hne
  refine ⟨r, hr.1, hr.2, fun y hry => ?_⟩
  have hy : y ∈ S := ⟨hry.2.1, hr.2.tail hry⟩
  exact hsink y hy hry

theorem IsMoleculeIn.exists_root_maximalFlowGraph_of_connected {U : LowerSet P} {n : ℕ}
    (hU : IsMoleculeIn P U) (hd : krullDim U = (n + 1 : ℕ))
    (ho : ∀ x ∈ U, grade ℕ x = n + 1 → (P.faces true x).Subsingleton)
    (hc : ∀ x ∈ P.topsAbove U n, ∀ y ∈ P.topsAbove U n,
      Relation.EqvGen (P.maximalFlowGraph U n).Adj x y) :
    ∃ r ∈ P.topsAbove U n, (∀ y, ¬ (P.maximalFlowGraph U n).Adj r y) ∧
      ∀ x ∈ P.topsAbove U n,
        Relation.ReflTransGen (P.maximalFlowGraph U n).Adj x r := by
  have hgrade {x : P} (hx : x ∈ P.topsAbove U n) : grade ℕ x = n + 1 := by
    have heq := P.topsAbove_sub_one_of_krullDim_eq hd (Nat.succ_pos n)
    rw [Nat.add_sub_cancel] at heq
    exact (heq ▸ hx).2
  have hsucc (x : P) : {y | (P.maximalFlowGraph U n).Adj x y}.Subsingleton := by
    by_cases hx : x ∈ P.topsAbove U n
    · exact hU.subsingleton_maximalFlowGraph_successors hd (hgrade hx)
        (ho x hx.1.prop (hgrade hx))
    · exact fun _ hy _ _ => (hx hy.1).elim
  have hshort {a b r : P}
      (har : Relation.ReflTransGen (P.maximalFlowGraph U n).Adj a r)
      (hab : (P.maximalFlowGraph U n).Adj a b)
      (hr : ∀ c, ¬ (P.maximalFlowGraph U n).Adj r c) :
      Relation.ReflTransGen (P.maximalFlowGraph U n).Adj b r := by
    rcases har.cases_head with rfl | ⟨c, hac, hcr⟩
    · exact (hr b hab).elim
    · exact hsucc a hac hab ▸ hcr
  obtain ⟨⟨x, hxU⟩, hxgrade⟩ := exists_grade_eq_of_krullDim_eq hd
  change grade ℕ x = n + 1 at hxgrade
  have hx : x ∈ P.topsAbove U n :=
    ⟨maximal_mem_of_krullDim_le hxU (by rw [hd, hxgrade]), by omega⟩
  obtain ⟨r, hr, hxr, hsink⟩ := hU.exists_sink_reflTransGen_maximalFlowGraph hd hx
  refine ⟨r, hr, hsink, fun y hy => ?_⟩
  have hprop : ∀ a b, Relation.EqvGen (P.maximalFlowGraph U n).Adj a b →
      (Relation.ReflTransGen (P.maximalFlowGraph U n).Adj a r ↔
        Relation.ReflTransGen (P.maximalFlowGraph U n).Adj b r) := by
    intro a b hab
    induction hab with
    | rel a b hab =>
      exact ⟨fun har => hshort har hab hsink,
        fun hbr => (Relation.ReflTransGen.single hab).trans hbr⟩
    | refl => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih ih' => exact ih.trans ih'
  exact (hprop x y (hc x hx y hy)).1 hxr

private theorem IsMoleculeIn.exists_facesIn_eq_of_connected {U : LowerSet P} {n : ℕ}
    (hU : IsMoleculeIn P U) (hr : P.IsRound U) (hd : krullDim U = (n + 1 : ℕ))
    (ho : ∀ x ∈ U, grade ℕ x = n + 1 → ∃! o, o ∈ P.faces true x)
    (hc : ∀ x ∈ P.topsAbove U n, ∀ y ∈ P.topsAbove U n,
      Relation.EqvGen (P.maximalFlowGraph U n).Adj x y) :
    ∃ r ∈ P.topsAbove U n, (∀ y, ¬ (P.maximalFlowGraph U n).Adj r y) ∧
      (∀ x ∈ P.topsAbove U n,
        Relation.ReflTransGen (P.maximalFlowGraph U n).Adj x r) ∧
      P.facesIn U n true = P.faces true r := by
  obtain ⟨r, hrtop, hsink, hreach⟩ := hU.exists_root_maximalFlowGraph_of_connected hd
    (fun x hx hxgrade _ ha _ hb => (ho x hx hxgrade).unique ha hb) hc
  have hgrade {x : P} (hx : x ∈ P.topsAbove U n) : grade ℕ x = n + 1 := by
    have heq := P.topsAbove_sub_one_of_krullDim_eq hd (Nat.succ_pos n)
    rw [Nat.add_sub_cancel] at heq
    exact (heq ▸ hx).2
  refine ⟨r, hrtop, hsink, hreach, Set.Subset.antisymm (fun o hof => ?_)
    (fun o hor => mem_facesIn_of_forall_not_maximalFlowGraph_adj hd hrtop.1.prop
      (hgrade hrtop) hor hsink)⟩
  have hnm : ¬ Maximal (· ∈ U) o := fun h => by
    have := hr.grade_eq_of_maximal hd h
    have := hof.2.1
    omega
  rw [maximal_mem_iff_forall_cofaces_inter_eq_empty hof.1] at hnm
  obtain ⟨α, hα⟩ := not_forall.1 hnm
  obtain ⟨x, hox, hxU⟩ := Set.nonempty_iff_ne_empty.2 hα
  cases α
  · exact (Set.disjoint_left.1 hof.2.2 hox hxU).elim
  have hxgrade : grade ℕ x = n + 1 := by
    have := Nat.covBy_iff_add_one_eq.1 (hox.1.grade ℕ)
    have := hof.2.1
    omega
  have hxtop : x ∈ P.topsAbove U n :=
    ⟨maximal_mem_of_krullDim_le hxU (by rw [hd, hxgrade]), by omega⟩
  have hxsink (y : P) : ¬ (P.maximalFlowGraph U n).Adj x y := by
    intro hxy
    obtain ⟨z, hzx, hzy⟩ :=
      (flowGraph_adj_iff_exists_mem_faces hxgrade (hgrade hxy.2.1)).1 hxy.2.2
    have he := (ho x hxU hxgrade).unique hzx hox
    exact Set.disjoint_left.1 hof.2.2 (he ▸ hzy) hxy.2.1.1.prop
  rcases (hreach x hxtop).cases_head with he | ⟨y, hxy, -⟩
  · exact he ▸ hox
  · exact (hxsink y hxy).elim

theorem IsMoleculeIn.subsingleton_graph_successors {U : LowerSet P} {n : ℕ}
    (hU : IsMoleculeIn P U) (hd : krullDim U ≤ (n + 1 : ℕ))
    (ho : ∀ x ∈ U, grade ℕ x = n + 1 → (P.faces true x).Subsingleton) (x : P) :
    {y | (P.graph U (n + 1)).Adj x y}.Subsingleton := by
  intro y hy z hz
  rcases hy with ⟨hxgrade, hxU, hxy⟩ | ⟨hygrade, hyU, hxy⟩ <;>
    rcases hz with ⟨hxgrade', hxU', hxz⟩ | ⟨hzgrade, hzU, hxz⟩
  · exact ho x hxU hxgrade hxy hxz
  · have := Nat.covBy_iff_add_one_eq.1 (hxz.1.grade ℕ)
    omega
  · have := Nat.covBy_iff_add_one_eq.1 (hxy.1.grade ℕ)
    omega
  · exact hU.subsingleton_cofaces_inter (x := x) (by
      have := Nat.covBy_iff_add_one_eq.1 (hxy.1.grade ℕ)
      exact hd.trans (by exact_mod_cast (by omega : n + 1 ≤ grade ℕ x + 1))) false
      ⟨hxy, hyU⟩ ⟨hxz, hzU⟩

theorem IsMoleculeIn.reflTransGen_graph_of_facesIn_eq_singleton {U : LowerSet P} {n : ℕ}
    (hU : IsMoleculeIn P U) (hd : krullDim U = (n + 1 : ℕ)) {o : P}
    (ho : P.facesIn U n true = {o}) {x : P} (hx : x ∈ U)
    (hxgrade : grade ℕ x = n ∨ grade ℕ x = n + 1) :
    Relation.ReflTransGen (P.graph U (n + 1)).Adj x o := by
  have hnode {y : P} (hy : y ∈ U) (hygrade : grade ℕ y = n + 1) :
      Relation.ReflTransGen (P.graph U (n + 1)).Adj y o := by
    obtain ⟨z, hz, hyz⟩ := hU.exists_reflTransGen_graph_mem_facesIn hd.le hy hygrade
    have he : z = o := Set.mem_singleton_iff.1 (ho ▸ hz)
    exact he ▸ hyz
  rcases hxgrade with hxgrade | hxgrade
  · by_cases hxo : x = o
    · subst x; exact .refl
    have hxf : x ∉ P.facesIn U n true := by simpa only [ho, Set.mem_singleton_iff] using hxo
    have hnot : ¬ Disjoint (P.cofaces false x) (U : Set P) :=
      fun hdisj => hxf ⟨hx, hxgrade, hdisj⟩
    obtain ⟨y, hxy, hyU⟩ := Set.not_disjoint_iff.1 hnot
    have hygrade : grade ℕ y = n + 1 := by
      have := Nat.covBy_iff_add_one_eq.1 (hxy.1.grade ℕ)
      omega
    have hstep : (P.graph U (n + 1)).Adj x y := Or.inr ⟨hygrade, hyU, hxy⟩
    exact (Relation.ReflTransGen.single hstep).trans (hnode hyU hygrade)
  · exact hnode hx hxgrade

theorem IsMoleculeIn.eqvGen_maximalFlowGraph_of_common_face {U : LowerSet P} {n : ℕ}
    (hU : IsMoleculeIn P U) (hd : krullDim U = (n + 1 : ℕ)) {x y z : P}
    (hx : x ∈ U) (hy : y ∈ U) (hxn : grade ℕ x = n + 1)
    (hyn : grade ℕ y = n + 1) (hzn : grade ℕ z = n) (hzx : z ≤ x) (hzy : z ≤ y) :
    Relation.EqvGen (P.maximalFlowGraph U n).Adj x y := by
  have hcx := GradeOrder.covBy_of_le_of_grade_eq_add_one hzx (by omega)
  have hcy := GradeOrder.covBy_of_le_of_grade_eq_add_one hzy (by omega)
  have htop {t : P} (ht : t ∈ U) (htn : grade ℕ t = n + 1) :
      t ∈ P.topsAbove U n :=
    ⟨maximal_mem_of_krullDim_le ht (by rw [hd, htn]), by omega⟩
  cases hα : P.orient hcx <;> cases hβ : P.orient hcy
  · have he := hU.subsingleton_cofaces_inter (x := z) (by rw [hd, hzn]) false
      ⟨⟨hcx, hα⟩, hx⟩ ⟨⟨hcy, hβ⟩, hy⟩
    subst y
    exact .refl x
  · exact Relation.EqvGen.symm _ _ (.rel _ _ ⟨htop hy hyn, htop hx hxn,
      (flowGraph_adj_iff_exists_mem_faces hyn hxn).2 ⟨z, ⟨hcy, hβ⟩, ⟨hcx, hα⟩⟩⟩)
  · exact .rel _ _ ⟨htop hx hxn, htop hy hyn,
      (flowGraph_adj_iff_exists_mem_faces hxn hyn).2 ⟨z, ⟨hcx, hα⟩, ⟨hcy, hβ⟩⟩⟩
  · have he := hU.subsingleton_cofaces_inter (x := z) (by rw [hd, hzn]) true
      ⟨⟨hcx, hα⟩, hx⟩ ⟨⟨hcy, hβ⟩, hy⟩
    subst y
    exact .refl x

private theorem IsMoleculeIn.exists_coface_of_isRound {U : LowerSet P} {n : ℕ}
    (hU : IsMoleculeIn P U) (hr : P.IsRound U) (hd : krullDim U = (n + 1 : ℕ))
    {z : P} (hz : z ∈ U) (hzn : grade ℕ z = n) :
    ∃ t ∈ U, grade ℕ t = n + 1 ∧ z ⋖ t := by
  obtain ⟨t, hzt, ht⟩ := hU.exists_le_maximal hz
  have htn := hr.grade_eq_of_maximal hd ht
  exact ⟨t, ht.prop, htn, GradeOrder.covBy_of_le_of_grade_eq_add_one hzt (by omega)⟩

private theorem IsMoleculeIn.exists_coface_of_mem_facesIn {U : LowerSet P} {n : ℕ}
    (hU : IsMoleculeIn P U) (hr : P.IsRound U) (hd : krullDim U = (n + 1 : ℕ))
    {z : P} {α : Bool} (hz : z ∈ P.facesIn U n α) :
    ∃ t ∈ U, z ∈ P.faces α t := by
  obtain ⟨t, ht, -, hzt⟩ := hU.exists_coface_of_isRound hr hd hz.1 hz.2.1
  refine ⟨t, ht, hzt, ?_⟩
  by_contra hne
  exact Set.disjoint_left.1 hz.2.2 ⟨hzt, Bool.eq_not_iff.2 hne⟩ ht

private theorem mixed_cofaces_of_boundary_rewrite {U B C : LowerSet P} {n : ℕ}
    (hU : IsMoleculeIn P U) {t z : P} (ht : t ∈ U) (htn : grade ℕ t = n + 2)
    (hzn : grade ℕ z = n)
    (hB : IsMoleculeIn P B) (hBd : krullDim B ≤ (n + 1 : ℕ))
    (hBU : B ≤ U) (hin : P.boundary (.Iic t) (n + 1) false ≤ B)
    (heq : (C : Set P) = ((B : Set P) \
      P.interior (P.boundary (.Iic t) (n + 1) false)) ∪
        P.boundary (.Iic t) (n + 1) true)
    (f g : P → Bool) (b : Bool)
    (hlabel : ∀ w ∈ U, grade ℕ w = n + 1 → ∀ s ∈ U,
      grade ℕ s = n + 2 → w ≤ s → g w = f s)
    (hmix : ∀ α, ∃ w ∈ B, z ∈ P.faces α w ∧ g w = (α ^^ b)) :
    ∀ α, ∃ w ∈ C, z ∈ P.faces α w ∧ g w = (α ^^ b) := by
  have hmem (s : P) : s ∈ C ↔
      (s ∈ B ∧ s ∉ P.interior (P.boundary (.Iic t) (n + 1) false)) ∨
        s ∈ P.boundary (.Iic t) (n + 1) true := by
    change s ∈ (C : Set P) ↔ _
    rw [heq]
    rfl
  intro α
  obtain ⟨w, hw, hzw, hgw⟩ := hmix α
  obtain ⟨v, hv, hzv, hgv⟩ := hmix (!α)
  have hwgrade : grade ℕ w = n + 1 := by
    have := Nat.covBy_iff_add_one_eq.1 (hzw.1.grade ℕ)
    omega
  have hvgrade : grade ℕ v = n + 1 := by
    have := Nat.covBy_iff_add_one_eq.1 (hzv.1.grade ℕ)
    omega
  by_cases hwC : w ∈ C
  · exact ⟨w, hwC, hzw, hgw⟩
  have hwIn : w ∈ P.boundary (.Iic t) (n + 1) false := by
    by_contra hn
    exact hwC ((hmem w).2 (Or.inl ⟨hw, fun h => hn h.1⟩))
  have hft : f t = (α ^^ b) := (hlabel w (hBU hw) hwgrade t ht htn
    (boundary_le _ _ _ hwIn)).symm.trans hgw
  have hvNotIn : v ∉ P.boundary (.Iic t) (n + 1) false := by
    intro hvIn
    have := (hlabel v (hBU hv) hvgrade t ht htn
      (boundary_le _ _ _ hvIn)).trans hft
    rw [hgv] at this
    cases α <;> cases b <;> simp at this
  have hzIn : z ∈ P.facesIn ↑(P.boundary (.Iic t) (n + 1) false) n α := by
    refine ⟨(P.boundary (.Iic t) (n + 1) false).lower hzw.1.le hwIn,
      hzn, Set.disjoint_left.2 fun s hzs hs => ?_⟩
    have hse : s = v := hB.subsingleton_cofaces_inter (x := z)
      (by rw [hzn]; exact hBd) (!α) ⟨hzs, hin hs⟩ ⟨hzv, hv⟩
    exact hvNotIn (hse ▸ hs)
  have hglob := (hU.isAtomIn_Iic ht).isRound.isGlobular
  have hboundary : P.boundary (P.boundary (.Iic t) (n + 1) false) n α =
      P.boundary (P.boundary (.Iic t) (n + 1) true) n α := by
    rw [hglob n (n + 1) (by omega) α false, hglob n (n + 1) (by omega) α true]
  have hzOut := (facesIn_eq_of_boundary_eq hboundary) ▸ hzIn
  have hAtom := (hU.isAtomIn_Iic ht).isMoleculeIn
  have hdOut : krullDim (P.boundary (.Iic t) (n + 1) true) = (n + 1 : ℕ) :=
    hAtom.krullDim_boundary (by rw [LowerSet.krullDim_Iic, htn]; exact_mod_cast (by omega :
      n + 1 ≤ n + 2)) true
  obtain ⟨s, hs, hzs⟩ := (hAtom.boundary (n + 1) true).exists_coface_of_mem_facesIn
    ((hU.isAtomIn_Iic ht).isRound.boundary (n + 1) true) hdOut hzOut
  have hsgrade : grade ℕ s = n + 1 := by
    have := Nat.covBy_iff_add_one_eq.1 (hzs.1.grade ℕ)
    omega
  have hst : s ≤ t := boundary_le _ _ _ hs
  exact ⟨s, (hmem s).2 (Or.inr hs), hzs, (hlabel s (U.lower hst ht) hsgrade t ht htn hst).trans hft⟩

private theorem eq_labels_of_input_flow_adj {U : LowerSet P} {n : ℕ}
    (hU : IsMoleculeIn P U) (hr : P.IsRound U) (hd : krullDim U = (n + 2 : ℕ))
    (f g : P → Bool)
    (hlabel : ∀ w ∈ U, grade ℕ w = n + 1 → ∀ s ∈ U,
      grade ℕ s = n + 2 → w ≤ s → g w = f s)
    {x y : P} (hx : grade ℕ x = n + 1) (hy : grade ℕ y = n + 1)
    (hxy : (P.maximalFlowGraph (P.boundary U (n + 1) false) n).Adj x y) :
    g x = g y := by
  by_contra hne
  obtain ⟨z, hzx, hzy⟩ := (flowGraph_adj_iff_exists_mem_faces hx hy).1 hxy.2.2
  have hzn : grade ℕ z = n := by
    have := Nat.covBy_iff_add_one_eq.1 (hzx.1.grade ℕ)
    omega
  let b := g y
  have hmix : ∀ α, ∃ w ∈ P.boundary U (n + 1) false,
      z ∈ P.faces α w ∧ g w = (α ^^ b) := by
    intro α
    cases α
    · exact ⟨y, hxy.2.1.1.prop, hzy, by simp only [Bool.false_xor, b]⟩
    · refine ⟨x, hxy.1.1.prop, hzx, ?_⟩
      cases hgx : g x <;> cases hgy : g y <;> simp_all only [b, Bool.true_xor,
        Bool.not_true, Bool.not_false, not_true_eq_false]
  obtain ⟨L, hL⟩ := admitsLayering_pred_krullDim hU hd (by omega)
  change P.IsLayering (n + 1) U L at hL
  let B (i : ℕ) := P.boundary (layerPrefix U (n + 1) L i) (n + 1) true
  have hB0 : B 0 = P.boundary U (n + 1) false :=
    boundary_eq_self (krullDim_boundary_le U (n + 1) false) true
  have hkeep (i : ℕ) (hi : i ≤ L.length) :
      ∀ α, ∃ w ∈ B i, z ∈ P.faces α w ∧ g w = (α ^^ b) := by
    induction i with
    | zero => simpa only [hB0] using hmix
    | succ i ih =>
      have hil : i < L.length := by omega
      obtain ⟨t, ht, htn, -, -⟩ := hL.exists_top_getD hd hil
      have hBM : IsMoleculeIn P (B i) := by
        cases i with
        | zero => simpa only [hB0] using hU.boundary (n + 1) false
        | succ j => exact (hL.isMoleculeIn_prefixUnion (by omega)).boundary (n + 1) true
      have hBU : B i ≤ U := (boundary_le _ _ _).trans
        (hL.isPastingIn_layerPrefix_layerSuffix (by omega)).1.left_le
      apply mixed_cofaces_of_boundary_rewrite hU (hL.le hil ht) htn hzn hBM
        (krullDim_boundary_le _ _ _) hBU
        (hL.isSubmoleculeOf_boundary_Iic_layerPrefix hd hil ht htn).le
        (hL.boundary_layerPrefix_succ hd hil ht htn) f g b hlabel (ih (by omega))
  obtain ⟨w, hw, hzw, -⟩ := hkeep L.length le_rfl false
  have hzInput : z ∈ P.boundary U (n + 1) false :=
    (P.boundary U (n + 1) false).lower hzx.1.le hxy.1.1.prop
  have hzOutput : z ∈ P.boundary U (n + 1) true := by
    change w ∈ P.boundary (layerPrefix U (n + 1) L L.length) (n + 1) true at hw
    rw [hL.layerPrefix_length] at hw
    exact (P.boundary U (n + 1) true).lower hzw.1.le hw
  have hzFull : z ∈ P.boundaryFull U n := by
    rw [← hr.inf_boundary_succ n (by rw [hd]; exact_mod_cast (by omega : n + 1 < n + 2))]
    exact ⟨hzInput, hzOutput⟩
  have hg := hr.isGlobular
  have hb (α : Bool) : P.boundary U n α =
      P.boundary (P.boundary U (n + 1) false) n α :=
    (hg n (n + 1) (by omega) α false).symm
  rcases hzFull with hz | hz
  · have hf := mem_facesIn_of_mem_boundary (hb false ▸ hz) hzn
    exact Set.disjoint_left.1 hf.2.2 hzx hxy.1.1.prop
  · have hf := mem_facesIn_of_mem_boundary (hb true ▸ hz) hzn
    exact Set.disjoint_left.1 hf.2.2 hzy hxy.2.1.1.prop

private theorem IsMoleculeIn.eq_labels_of_input_constant {U : LowerSet P} {n : ℕ}
    (hU : IsMoleculeIn P U) (hd : krullDim U = (n + 1 : ℕ)) (f g : P → Bool) (b : Bool)
    (hlabel : ∀ w ∈ U, grade ℕ w = n → ∀ s ∈ U,
      grade ℕ s = n + 1 → w ≤ s → g w = f s)
    (hinput : ∀ w ∈ P.facesIn U n false, g w = b)
    {x : P} (hx : x ∈ U) (hxn : grade ℕ x = n + 1) : f x = b := by
  obtain ⟨w, hw, hwx⟩ := hU.exists_mem_facesIn_reflTransGen_graph hd.le hx hxn
  have hne : n ≠ n + 1 := by omega
  have hprop : ∀ a b, (P.graph U (n + 1)).Adj a b →
      (cond (decide (grade ℕ a = n + 1)) (f a) (g a)) =
        (cond (decide (grade ℕ b = n + 1)) (f b) (g b)) := by
    intro a b hab
    rcases hab with ⟨ha, haU, hab⟩ | ⟨hb, hbU, hab⟩
    · have hbn : grade ℕ b = n := by
        have := Nat.covBy_iff_add_one_eq.1 (hab.1.grade ℕ)
        omega
      simpa only [ha, hbn, hne, decide_true,
        decide_false, Bool.cond_true, Bool.cond_false] using
        (hlabel b (U.lower hab.1.le haU) hbn a haU ha hab.1.le).symm
    · have han : grade ℕ a = n := by
        have := Nat.covBy_iff_add_one_eq.1 (hab.1.grade ℕ)
        omega
      simpa only [hb, han, hne, decide_true,
        decide_false, Bool.cond_true, Bool.cond_false] using
        hlabel a (U.lower hab.1.le hbU) han b hbU hb hab.1.le
  have hpath : ∀ a b, Relation.ReflTransGen (P.graph U (n + 1)).Adj a b →
      (cond (decide (grade ℕ a = n + 1)) (f a) (g a)) =
        (cond (decide (grade ℕ b = n + 1)) (f b) (g b)) := by
    intro a b hab
    induction hab with
    | refl => rfl
    | tail _ hbc ih => exact ih.trans (hprop _ _ hbc)
  have he := hpath w x hwx
  simp only [hw.2.1, hxn, hne, decide_false, decide_true,
    Bool.cond_false, Bool.cond_true] at he
  exact he.symm.trans (hinput w hw)

private theorem IsMoleculeIn.exists_top_coface_eqvGen_iff {U : LowerSet P} {n : ℕ}
    (hU : IsMoleculeIn P U) (hd : krullDim U = (n + 1 : ℕ)) (x : P) {w s : P}
    (hwn : grade ℕ w = n) (hs : s ∈ U) (hsn : grade ℕ s = n + 1) (hws : w ≤ s) :
    (∃ t ∈ U, grade ℕ t = n + 1 ∧ w ≤ t ∧
      Relation.EqvGen (P.maximalFlowGraph U n).Adj x t) ↔
        Relation.EqvGen (P.maximalFlowGraph U n).Adj x s := by
  constructor
  · rintro ⟨t, ht, htn, hwt, hxt⟩
    exact .trans _ _ _ hxt
      (hU.eqvGen_maximalFlowGraph_of_common_face hd ht hs htn hsn hwn hwt hws)
  · exact fun h => ⟨s, hs, hsn, hws, h⟩

private theorem IsMoleculeIn.eqvGen_of_input_labels_constant {U : LowerSet P} {n : ℕ}
    (hU : IsMoleculeIn P U) (hd : krullDim U = (n + 1 : ℕ))
    {x y : P} (hx : x ∈ P.topsAbove U n) (hy : y ∈ P.topsAbove U n)
    (hc : ∀ f g : P → Bool,
      (∀ w ∈ U, grade ℕ w = n → ∀ s ∈ U,
        grade ℕ s = n + 1 → w ≤ s → g w = f s) →
      ∃ b, ∀ w ∈ P.facesIn U n false, g w = b) :
    Relation.EqvGen (P.maximalFlowGraph U n).Adj x y := by
  classical
  let f (s : P) := decide (Relation.EqvGen (P.maximalFlowGraph U n).Adj x s)
  let g (w : P) := decide (∃ s ∈ U, grade ℕ s = n + 1 ∧ w ≤ s ∧
    Relation.EqvGen (P.maximalFlowGraph U n).Adj x s)
  have hlabel : ∀ w ∈ U, grade ℕ w = n → ∀ s ∈ U,
      grade ℕ s = n + 1 → w ≤ s → g w = f s := by
    intro w _ hwgrade s hs hsgrade hws
    simp only [g, f, hU.exists_top_coface_eqvGen_iff hd x hwgrade hs hsgrade hws]
  obtain ⟨b, hinput⟩ := hc f g hlabel
  have hgrade {s : P} (hs : s ∈ P.topsAbove U n) : grade ℕ s = n + 1 := by
    have heq := P.topsAbove_sub_one_of_krullDim_eq hd (Nat.succ_pos n)
    rw [Nat.add_sub_cancel] at heq
    exact (heq ▸ hs).2
  have he := (hU.eq_labels_of_input_constant hd f g b hlabel hinput hx.1.prop (hgrade hx)).trans
    (hU.eq_labels_of_input_constant hd f g b hlabel hinput hy.1.prop (hgrade hy)).symm
  have hxtrue : f x = true := by simp only [f, Relation.EqvGen.refl, decide_true]
  have hytrue : f y = true := he.symm.trans hxtrue
  simpa only [f, decide_eq_true_eq] using hytrue

theorem IsMoleculeIn.eqvGen_maximalFlowGraph_of_isRound {U : LowerSet P} {n : ℕ}
    (hU : IsMoleculeIn P U) (hr : P.IsRound U) (hd : krullDim U = (n + 1 : ℕ))
    {x y : P} (hx : x ∈ P.topsAbove U n) (hy : y ∈ P.topsAbove U n) :
    Relation.EqvGen (P.maximalFlowGraph U n).Adj x y := by
  classical
  induction n generalizing U x y with
  | zero =>
    apply hU.eqvGen_of_input_labels_constant hd hx hy
    intro f g hlabel
    obtain ⟨v, hv, hb⟩ := (hU.boundary 0 false).exists_eq_Iic_of_krullDim_eq_zero
      (hU.krullDim_boundary (by rw [hd]; exact_mod_cast (by omega : 0 ≤ 1)) false)
    have hinput : ∀ w ∈ P.facesIn U 0 false, g w = g v := by
      intro w hw
      have hwv : w ∈ LowerSet.Iic v := by
        rw [← hb]
        exact mem_boundary_of_mem_facesIn hw le_rfl
      exact congrArg g (hv.eq_of_le hwv)
    exact ⟨g v, hinput⟩
  | succ n ih =>
    apply hU.eqvGen_of_input_labels_constant hd hx hy
    intro f g hlabel
    let V := P.boundary U (n + 1) false
    have hV := hU.boundary (n + 1) false
    have hVd : krullDim V = (n + 1 : ℕ) :=
      hU.krullDim_boundary (by rw [hd]; exact_mod_cast (by omega : n + 1 ≤ n + 2)) false
    have hgrade {s : P} (hs : s ∈ P.topsAbove V n) : grade ℕ s = n + 1 :=
      (hr.boundary (n + 1) false).grade_eq_of_maximal hVd hs.1
    have hrel : ∀ a b, (P.maximalFlowGraph V n).Adj a b → g a = g b := by
      intro a b hab
      exact eq_labels_of_input_flow_adj hU hr hd f g hlabel
        (hgrade hab.1) (hgrade hab.2.1) hab
    have heqv : ∀ a b, Relation.EqvGen (P.maximalFlowGraph V n).Adj a b → g a = g b := by
      intro a b hab
      induction hab with
      | rel a b hab => exact hrel a b hab
      | refl => rfl
      | symm _ _ _ ih' => exact ih'.symm
      | trans _ _ _ _ _ ih' ih'' => exact ih'.trans ih''
    have htop {s : P} (hs : s ∈ P.facesIn U (n + 1) false) : s ∈ P.topsAbove V n :=
      ⟨maximal_mem_of_krullDim_le (mem_boundary_of_mem_facesIn hs le_rfl)
        (by rw [hVd, hs.2.1]), by have := hs.2.1; omega⟩
    have hxgrade : grade ℕ x = n + 2 := hr.grade_eq_of_maximal hd hx.1
    obtain ⟨w, hw, -⟩ := hU.exists_mem_facesIn_reflTransGen_graph hd.le hx.1.prop hxgrade
    have hinput : ∀ s ∈ P.facesIn U (n + 1) false, g s = g w := by
      intro s hs
      exact heqv s w (ih hV (hr.boundary (n + 1) false) hVd (htop hs) (htop hw))
    exact ⟨g w, hinput⟩

theorem IsMoleculeIn.exists_root_maximalFlowGraph_and_facesIn_eq {U : LowerSet P} {n : ℕ}
    (hU : IsMoleculeIn P U) (hr : P.IsRound U) (hd : krullDim U = (n + 1 : ℕ))
    (ho : ∀ x ∈ U, grade ℕ x = n + 1 → ∃! o, o ∈ P.faces true x) :
    ∃ r ∈ P.topsAbove U n, (∀ y, ¬ (P.maximalFlowGraph U n).Adj r y) ∧
      (∀ x ∈ P.topsAbove U n,
        Relation.ReflTransGen (P.maximalFlowGraph U n).Adj x r) ∧
      (∀ x, {y | (P.maximalFlowGraph U n).Adj x y}.Subsingleton) ∧
      P.facesIn U n true = P.faces true r := by
  obtain ⟨r, hrtop, hsink, hreach, heq⟩ := hU.exists_facesIn_eq_of_connected hr hd ho
    (fun _ hx _ hy => hU.eqvGen_maximalFlowGraph_of_isRound hr hd hx hy)
  refine ⟨r, hrtop, hsink, hreach, fun x => ?_, heq⟩
  by_cases hx : x ∈ P.topsAbove U n
  · have hxgrade : grade ℕ x = n + 1 := hr.grade_eq_of_maximal hd hx.1
    exact hU.subsingleton_maximalFlowGraph_successors hd hxgrade
      (fun _ ha _ hb => (ho x hx.1.prop hxgrade).unique ha hb)
  · exact fun _ hxy _ _ => (hx hxy.1).elim

theorem IsMoleculeIn.exists_facesIn_eq {U : LowerSet P} {n : ℕ}
    (hU : IsMoleculeIn P U) (hr : P.IsRound U) (hd : krullDim U = (n + 1 : ℕ))
    (ho : ∀ x ∈ U, grade ℕ x = n + 1 → ∃! o, o ∈ P.faces true x) :
    ∃ r ∈ U, grade ℕ r = n + 1 ∧ P.facesIn U n true = P.faces true r := by
  obtain ⟨r, hrU, -, -, -, heq⟩ := hU.exists_root_maximalFlowGraph_and_facesIn_eq hr hd ho
  exact ⟨r, hrU.1.prop, hr.grade_eq_of_maximal hd hrU.1, heq⟩

theorem IsMoleculeIn.exists_root_graph {U : LowerSet P} {n : ℕ}
    (hU : IsMoleculeIn P U) (hr : P.IsRound U) (hd : krullDim U = (n + 1 : ℕ))
    (ho : ∀ x ∈ U, grade ℕ x = n + 1 → ∃! o, o ∈ P.faces true x) :
    ∃ r ∈ U, grade ℕ r = n + 1 ∧ ∃ o,
      P.faces true r = {o} ∧ P.facesIn U n true = {o} ∧
      (∀ y, ¬ (P.graph U (n + 1)).Adj o y) ∧
      (∀ x, {y | (P.graph U (n + 1)).Adj x y}.Subsingleton) ∧
      ∀ x ∈ U, grade ℕ x = n ∨ grade ℕ x = n + 1 →
        Relation.ReflTransGen (P.graph U (n + 1)).Adj x o := by
  obtain ⟨r, hrU, hrgrade, heq⟩ := hU.exists_facesIn_eq hr hd ho
  obtain ⟨o, hor, hou⟩ := ho r hrU hrgrade
  have hro : P.faces true r = {o} := Set.eq_singleton_iff_unique_mem.2 ⟨hor, hou⟩
  have hUo : P.facesIn U n true = {o} := heq.trans hro
  have hograde : grade ℕ o = n := by
    have := Nat.covBy_iff_add_one_eq.1 (hor.1.grade ℕ)
    omega
  refine ⟨r, hrU, hrgrade, o, hro, hUo, fun y hoy => ?_,
    hU.subsingleton_graph_successors hd.le
      (fun x hx hxgrade _ ha _ hb => (ho x hx hxgrade).unique ha hb),
    fun x hx hxgrade => hU.reflTransGen_graph_of_facesIn_eq_singleton hd hUo hx hxgrade⟩
  rcases hoy with ⟨hograde', -, -⟩ | ⟨-, hyU, hoy⟩
  · omega
  · have hof : o ∈ P.facesIn U n true := by
      rw [hUo]
      exact Set.mem_singleton o
    exact Set.disjoint_left.1 hof.2.2 hoy hyU

theorem IsMoleculeIn.exists_root_maximalFlowGraph_and_graph {U : LowerSet P} {n : ℕ}
    (hU : IsMoleculeIn P U) (hr : P.IsRound U) (hd : krullDim U = (n + 1 : ℕ))
    (ho : ∀ x ∈ U, grade ℕ x = n + 1 → ∃! o, o ∈ P.faces true x) :
    ∃ r ∈ P.topsAbove U n, ∃ o,
      P.faces true r = {o} ∧ P.facesIn U n true = {o} ∧
      (∀ y, ¬ (P.maximalFlowGraph U n).Adj r y) ∧
      (∀ x ∈ P.topsAbove U n,
        Relation.ReflTransGen (P.maximalFlowGraph U n).Adj x r) ∧
      (∀ x, {y | (P.maximalFlowGraph U n).Adj x y}.Subsingleton) ∧
      (∀ y, ¬ (P.graph U (n + 1)).Adj o y) ∧
      (∀ x, {y | (P.graph U (n + 1)).Adj x y}.Subsingleton) ∧
      ∀ x ∈ U, grade ℕ x = n ∨ grade ℕ x = n + 1 →
        Relation.ReflTransGen (P.graph U (n + 1)).Adj x o := by
  obtain ⟨r, hrtop, hsink, hreach, hsucc, heq⟩ :=
    hU.exists_root_maximalFlowGraph_and_facesIn_eq hr hd ho
  obtain ⟨-, -, -, o, -, hUo, hgsink, hgsucc, hgreach⟩ := hU.exists_root_graph hr hd ho
  exact ⟨r, hrtop, o, heq.symm.trans hUo, hUo, hsink, hreach, hsucc, hgsink, hgsucc, hgreach⟩

end Atoms.Molecule.OGP
