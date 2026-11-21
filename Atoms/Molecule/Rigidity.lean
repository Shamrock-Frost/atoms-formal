import Atoms.Molecule.Submolecule
import Atoms.Molecule.Transport
import Mathlib.Combinatorics.Digraph.Basic

universe u

open CategoryTheory Order Set

namespace Atoms.Molecule.OGP

variable {P : OGP.{u}} {U V : LowerSet P} {n : ℕ} {x y : P}

variable (P) in
def graph (U : LowerSet P) (n : ℕ) : Digraph P where
  Adj x y := grade ℕ x = n ∧ x ∈ U ∧ y ∈ P.faces true x ∨
    grade ℕ y = n ∧ y ∈ U ∧ x ∈ P.faces false y

@[simp] theorem graph_adj :
    (P.graph U n).Adj x y ↔ grade ℕ x = n ∧ x ∈ U ∧ y ∈ P.faces true x ∨
      grade ℕ y = n ∧ y ∈ U ∧ x ∈ P.faces false y :=
  Iff.rfl

variable (P) in
private def step (U : LowerSet P) (n : ℕ) (α : Bool) (a b : P) : Prop :=
  grade ℕ a = n ∧ a ∈ U ∧ b ∈ P.faces (!α) a ∨ grade ℕ b = n ∧ b ∈ U ∧ a ∈ P.faces α b

private theorem mem_of_step_left {α : Bool} (h : P.step U n α x y) : x ∈ U :=
  h.elim (fun h => h.2.1) fun h => U.lower h.2.2.1.le h.2.1

private theorem mem_of_step_right {α : Bool} (h : P.step U n α x y) : y ∈ U :=
  h.elim (fun h => U.lower h.2.2.1.le h.2.1) fun h => h.2.1

private theorem step_of_mem {α : Bool} (h : P.step U n α x y) (hx : x ∈ V) (hy : y ∈ V) :
    P.step V n α x y :=
  h.imp (fun h => ⟨h.1, hx, h.2.2⟩) fun h => ⟨h.1, hy, h.2.2⟩

private theorem wellFounded_step_Iic {t : P} (ht : grade ℕ t ≤ n) (α : Bool) :
    WellFounded (P.step (.Iic t) n α) := by
  classical
  refine Subrelation.wf (fun {a b} hab => ?_)
    (InvImage.wf (fun z => if z = t then 1 else if z ∈ P.faces (!α) t then 2 else 0)
      wellFounded_lt)
  rcases hab with ⟨ha, hat, hb⟩ | ⟨hb, hbt, ha⟩
  · obtain rfl : a = t := GradeOrder.eq_of_le_of_grade_le hat (ha ▸ ht)
    simp [InvImage, hb.1.ne, hb]
  · obtain rfl : b = t := GradeOrder.eq_of_le_of_grade_le hbt (hb ▸ ht)
    simp [InvImage, ha.1.ne, Set.disjoint_left.1 (P.disjoint_faces b α) ha]

private theorem wellFounded_step_sup {X Y : LowerSet P} {k : ℕ} {α : Bool} (hkn : k < n)
    (hI : X ⊓ Y = P.boundary Y k α) (hX : WellFounded (P.step X n α))
    (hY : WellFounded (P.step Y n α)) : WellFounded (P.step (X ⊔ Y) n α) := by
  have hin (a b : P) (hab : P.step (X ⊔ Y) n α a b) (hb : b ∈ X) : a ∈ X := by
    by_contra ha
    have haY := (LowerSet.mem_sup_iff.1 (mem_of_step_left hab)).resolve_left ha
    rcases hab with ⟨han, -, hba⟩ | ⟨-, -, hab⟩
    · have hbI : b ∈ P.boundary Y k α := by
        rw [← hI]
        exact ⟨hb, Y.lower hba.1.le haY⟩
      have hbk := grade_le_of_mem_boundary hbI
      have hba' := Nat.covBy_iff_add_one_eq.1 (hba.1.grade ℕ)
      exact disjoint_left.1 (mem_facesIn_of_mem_boundary hbI (by omega)).2.2 hba haY
    · exact ha (X.lower hab.1.le hb)
  have hAccX (z : P) (hz : z ∈ X) : Acc (P.step (X ⊔ Y) n α) z := by
    induction z using hX.induction with
    | _ z ih => exact ⟨z, fun a ha => ih a (step_of_mem ha (hin a z ha hz) hz) (hin a z ha hz)⟩
  refine ⟨fun z => ?_⟩
  induction z using hY.induction with
  | _ z ih =>
    refine ⟨z, fun a ha => ?_⟩
    by_cases haX : a ∈ X
    · exact hAccX a haX
    have hzY := (LowerSet.mem_sup_iff.1 (mem_of_step_right ha)).resolve_left
      fun hz => haX (hin a z ha hz)
    exact ih a (step_of_mem ha ((LowerSet.mem_sup_iff.1 (mem_of_step_left ha)).resolve_left haX)
      hzY)

private theorem IsMoleculeIn.wellFounded_step (h : IsMoleculeIn P U) (hU : krullDim U ≤ n)
    (α : Bool) : WellFounded (P.step U n α) := by
  induction h with
  | point t _ => exact wellFounded_step_Iic (by rwa [LowerSet.krullDim_Iic, Nat.cast_le] at hU) α
  | atom t _ _ _ => exact wellFounded_step_Iic (by rwa [LowerSet.krullDim_Iic, Nat.cast_le] at hU) α
  | paste k V W U hp _ _ hk ihV ihW =>
    have hVU := LowerSet.krullDim_mono hp.left_le
    have hWU := LowerSet.krullDim_mono hp.right_le
    have hkn : k < n := by
      have := (hk.trans_le (min_le_right _ _)).trans_le (hWU.trans hU)
      exact_mod_cast this
    rw [← hp.sup_eq]
    cases α
    · exact wellFounded_step_sup hkn hp.inf_eq_input (ihV (hVU.trans hU)) (ihW (hWU.trans hU))
    · rw [sup_comm]
      refine wellFounded_step_sup hkn ?_ (ihW (hWU.trans hU)) (ihV (hVU.trans hU))
      rw [inf_comm]
      exact hp.inf_eq_output

theorem IsMoleculeIn.wellFounded_graph (h : IsMoleculeIn P U) (hU : krullDim U ≤ n) :
    WellFounded (P.graph U n).Adj :=
  h.wellFounded_step hU false

theorem IsMoleculeIn.subsingleton_cofaces_inter (h : IsMoleculeIn P U)
    (hx : krullDim U ≤ (grade ℕ x + 1 : ℕ)) (α : Bool) : (P.cofaces α x ∩ U).Subsingleton := by
  have hIic (t : P) (ht : krullDim (LowerSet.Iic t) ≤ (grade ℕ x + 1 : ℕ)) :
      (P.cofaces α x ∩ (LowerSet.Iic t : Set P)).Subsingleton := by
    rw [LowerSet.krullDim_Iic, Nat.cast_le] at ht
    have key (c : P) (hc : c ∈ P.cofaces α x ∩ (LowerSet.Iic t : Set P)) : c = t := by
      have := Nat.covBy_iff_add_one_eq.1 (hc.1.1.grade ℕ)
      exact GradeOrder.eq_of_le_of_grade_le hc.2 (by omega)
    exact fun c₁ h₁ c₂ h₂ => (key c₁ h₁).trans (key c₂ h₂).symm
  induction h with
  | point t _ => exact hIic t hx
  | atom t _ _ _ => exact hIic t hx
  | paste k V W U hp _ _ hk ihV ihW =>
    have hVU := LowerSet.krullDim_mono hp.left_le
    have hWU := LowerSet.krullDim_mono hp.right_le
    have hmixed (a b : P) (ha : a ∈ P.cofaces α x ∩ V) (hb : b ∈ P.cofaces α x ∩ W) : False := by
      have hxI : x ∈ V ⊓ W := ⟨V.lower ha.1.1.le ha.2, W.lower hb.1.1.le hb.2⟩
      have hxk : grade ℕ x ≤ k := grade_le_of_mem_boundary (hp.inf_eq_output ▸ hxI)
      have hkx : k < grade ℕ x + 1 := by
        have := (hk.trans_le (min_le_left _ _)).trans_le (hVU.trans hx)
        exact_mod_cast this
      cases α
      · exact disjoint_left.1 (mem_facesIn_of_mem_boundary (hp.inf_eq_output ▸ hxI)
          (by omega)).2.2 ha.1 ha.2
      · exact disjoint_left.1 (mem_facesIn_of_mem_boundary (hp.inf_eq_input ▸ hxI)
          (by omega)).2.2 hb.1 hb.2
    have hmem (z : P) (hz : z ∈ U) : z ∈ V ∨ z ∈ W := by
      rw [← hp.sup_eq] at hz
      exact LowerSet.mem_sup_iff.1 hz
    rintro c₁ ⟨hc₁, h₁⟩ c₂ ⟨hc₂, h₂⟩
    rcases hmem c₁ h₁ with h₁ | h₁ <;> rcases hmem c₂ h₂ with h₂ | h₂
    · exact ihV (hVU.trans hx) ⟨hc₁, h₁⟩ ⟨hc₂, h₂⟩
    · exact (hmixed c₁ c₂ ⟨hc₁, h₁⟩ ⟨hc₂, h₂⟩).elim
    · exact (hmixed c₂ c₁ ⟨hc₂, h₂⟩ ⟨hc₁, h₁⟩).elim
    · exact ihW (hWU.trans hx) ⟨hc₁, h₁⟩ ⟨hc₂, h₂⟩

theorem maximal_mem_iff_forall_cofaces_inter_eq_empty (hx : x ∈ U) :
    Maximal (· ∈ U) x ↔ ∀ α, P.cofaces α x ∩ U = ∅ := by
  simp only [maximal_mem_iff_forall_mem_facesIn, ← disjoint_iff_inter_eq_empty]
  refine ⟨fun h α => ?_, fun h α => ⟨hx, rfl, h (!α)⟩⟩
  simpa using (h (!α)).2.2

private theorem mem_facesIn_grade_iff (hx : x ∈ U) (α : Bool) :
    x ∈ P.facesIn U (grade ℕ x) α ↔ P.cofaces (!α) x ∩ U = ∅ := by
  rw [← disjoint_iff_inter_eq_empty]
  exact ⟨fun h => h.2.2, fun h => ⟨hx, rfl, h⟩⟩

private theorem IsMoleculeIn.exists_cofaces_inter_eq_singleton_iff (h : IsMoleculeIn P U)
    (hx : krullDim U ≤ (grade ℕ x + 1 : ℕ)) (α : Bool) :
    (∃ c, P.cofaces α x ∩ U = {c}) ↔ (P.cofaces α x ∩ U).Nonempty := by
  rw [exists_eq_singleton_iff_nonempty_subsingleton,
    and_iff_left (h.subsingleton_cofaces_inter hx α)]

theorem IsMoleculeIn.mem_facesIn_diff_iff (h : IsMoleculeIn P U) (hxU : x ∈ U)
    (hx : krullDim U ≤ (grade ℕ x + 1 : ℕ)) (α : Bool) :
    x ∈ P.facesIn U (grade ℕ x) α \ P.facesIn U (grade ℕ x) (!α) ↔
      (∃ c, P.cofaces α x ∩ U = {c}) ∧ P.cofaces (!α) x ∩ U = ∅ := by
  rw [mem_sdiff, mem_facesIn_grade_iff hxU, mem_facesIn_grade_iff hxU, Bool.not_not,
    h.exists_cofaces_inter_eq_singleton_iff hx, nonempty_iff_ne_empty, and_comm]

theorem IsMoleculeIn.notMem_facesIn_union_iff (h : IsMoleculeIn P U) (hxU : x ∈ U)
    (hx : krullDim U ≤ (grade ℕ x + 1 : ℕ)) :
    x ∉ P.facesIn U (grade ℕ x) false ∪ P.facesIn U (grade ℕ x) true ↔
      ∀ α, ∃ c, P.cofaces α x ∩ U = {c} := by
  simp only [mem_union, not_or, mem_facesIn_grade_iff hxU,
    h.exists_cofaces_inter_eq_singleton_iff hx, nonempty_iff_ne_empty,
    Bool.forall_bool, Bool.not_false, Bool.not_true, and_comm]

private theorem IsMoleculeIn.exists_mem_facesIn_reflTransGen_step (h : IsMoleculeIn P U)
    (hU : krullDim U ≤ (n + 1 : ℕ)) (α : Bool) (hx : x ∈ U) (hxn : grade ℕ x = n + 1) :
    ∃ y ∈ P.facesIn U n α, Relation.ReflTransGen (P.step U (n + 1) α) y x := by
  induction x using (h.wellFounded_step hU α).transGen.induction with
  | _ x ih =>
  obtain ⟨y, hy⟩ := h.nonempty_faces hx (by omega) α
  have hyU : y ∈ U := U.lower hy.1.le hx
  have hyn : grade ℕ y = n := by have := Nat.covBy_iff_add_one_eq.1 (hy.1.grade ℕ); omega
  have e₁ : P.step U (n + 1) α y x := Or.inr ⟨hxn, hx, hy⟩
  by_cases hyf : Disjoint (P.cofaces (!α) y) (U : Set P)
  · exact ⟨y, ⟨hyU, hyn, hyf⟩, .single e₁⟩
  obtain ⟨c, hc, hcU⟩ := not_disjoint_iff.1 hyf
  have hcn : grade ℕ c = n + 1 := by have := Nat.covBy_iff_add_one_eq.1 (hc.1.grade ℕ); omega
  have e₂ : P.step U (n + 1) α c y := Or.inl ⟨hcn, hcU, hc⟩
  obtain ⟨z, hz, hzc⟩ := ih c (.tail (.single e₂) e₁) hcU hcn
  exact ⟨z, hz, (hzc.tail e₂).tail e₁⟩

theorem IsMoleculeIn.exists_mem_facesIn_reflTransGen_graph (h : IsMoleculeIn P U)
    (hU : krullDim U ≤ (n + 1 : ℕ)) (hx : x ∈ U) (hxn : grade ℕ x = n + 1) :
    ∃ y ∈ P.facesIn U n false, Relation.ReflTransGen (P.graph U (n + 1)).Adj y x :=
  h.exists_mem_facesIn_reflTransGen_step hU false hx hxn

theorem IsMoleculeIn.exists_reflTransGen_graph_mem_facesIn (h : IsMoleculeIn P U)
    (hU : krullDim U ≤ (n + 1 : ℕ)) (hx : x ∈ U) (hxn : grade ℕ x = n + 1) :
    ∃ y ∈ P.facesIn U n true, Relation.ReflTransGen (P.graph U (n + 1)).Adj x y := by
  obtain ⟨y, hy, hyx⟩ := h.exists_mem_facesIn_reflTransGen_step hU true hx hxn
  refine ⟨y, hy, Relation.reflTransGen_swap.1 ?_⟩
  exact hyx.lift id fun a b (hab : P.step U (n + 1) true a b) =>
    (Or.symm hab : (P.graph U (n + 1)).Adj b a)

section Rigidity

variable {Q : OGP.{u}} (f g : P ⟶ Q)

private theorem eq_of_le_of_eq_of_isMoleculeIn [IsInclusion f] [IsInclusion g] {d : ℕ}
    (ih : ∀ m < d, ∀ V : LowerSet P, IsMoleculeIn P V → krullDim V = m → map f V = map g V →
      EqOn f g V)
    (h : IsMoleculeIn P U) (hd : krullDim U = d) {z : P} (hz : z ∈ U) (hfz : f z = g z)
    (hyz : y ≤ z) : f y = g y := by
  rcases hyz.eq_or_lt with rfl | hlt
  · exact hfz
  have hzd : grade ℕ z ≤ d := krullDim_le_coe_iff.1 hd.le ⟨z, hz⟩
  obtain ⟨m, hm⟩ : ∃ m, grade ℕ z = m + 1 :=
    ⟨grade ℕ z - 1, by have := grade_strictMono (𝕆 := ℕ) hlt; omega⟩
  obtain ⟨α, hα⟩ : ∃ α, y ∈ P.bdry (.Iic z) α := by
    have hy : y ∈ (P.bdry (.Iic z) false ⊔ P.bdry (.Iic z) true : LowerSet P) := by
      rw [← SetLike.mem_coe, coe_bdry_Iic_sup]
      exact hlt
    exact (LowerSet.mem_sup_iff.1 hy).elim (⟨false, ·⟩) (⟨true, ·⟩)
  have hb := (h.isAtomIn_Iic hz).isMoleculeIn.bdry
    (by rw [LowerSet.krullDim_Iic, hm]; exact_mod_cast m.succ_pos) α
  refine ih m (by omega) _ hb (krullDim_bdry_Iic hm hb.nonempty) ?_ hα
  rw [map_bdry, map_bdry, map_Iic, map_Iic, hfz]

private theorem eq_of_graph_adj_of_isMoleculeIn [IsInclusion f] {m : ℕ} (h : IsMoleculeIn P U)
    (hd : krullDim U = (m + 1 : ℕ)) (hfg : map f U = map g U)
    (hcl : ∀ z ∈ U, f z = g z → ∀ y ≤ z, f y = g y) {a b : P}
    (hab : (P.graph U (m + 1)).Adj a b) (hfa : f a = g a) : f b = g b := by
  rcases graph_adj.1 hab with ⟨-, haU, hb⟩ | ⟨hbn, hbU, ha⟩
  · exact hcl a haU hfa b hb.1.le
  have han := Nat.covBy_iff_add_one_eq.1 (ha.1.grade ℕ)
  refine (isMoleculeIn_map f h).subsingleton_cofaces_inter (x := f a) ?_ false
    ⟨((isMorphism f).bijOn_faces b false).mapsTo ha, mem_map.2 ⟨b, hbU, rfl⟩⟩ ⟨?_, ?_⟩
  · rw [krullDim_map, hd, (isMorphism f).grade_eq]
    exact_mod_cast (by omega : m + 1 ≤ grade ℕ a + 1)
  · rw [hfa]
    exact ((isMorphism g).bijOn_faces b false).mapsTo ha
  · rw [SetLike.mem_coe, hfg]
    exact mem_map.2 ⟨b, hbU, rfl⟩

theorem IsMoleculeIn.eqOn_of_map_eq [IsInclusion f] [IsInclusion g] (h : IsMoleculeIn P U)
    (hfg : map f U = map g U) :
    EqOn f g U := by
  suffices key : ∀ d : ℕ, ∀ U : LowerSet P, IsMoleculeIn P U → krullDim U = d →
      map f U = map g U → EqOn f g U by
    obtain ⟨d, hd⟩ := h.exists_krullDim_eq
    exact key d U h hd hfg
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro U h hd hfg
  have hcl (z : P) (hz : z ∈ U) (hfz : f z = g z) (y : P) (hyz : y ≤ z) : f y = g y :=
    eq_of_le_of_eq_of_isMoleculeIn f g ih h hd hz hfz hyz
  cases d with
  | zero =>
    obtain ⟨x, hx, rfl⟩ := h.exists_eq_Iic_of_krullDim_eq_zero (by exact_mod_cast hd)
    rw [map_Iic, map_Iic, LowerSet.Iic_inj] at hfg
    exact fun y hy => hcl x le_rfl hfg y hy
  | succ m =>
    have hbd (α : Bool) : EqOn f g (P.boundary U m α) :=
      ih m (by omega) _ (h.boundary m α)
        (h.krullDim_boundary (by rw [hd]; exact_mod_cast m.le_succ) α)
        (by rw [map_boundary, map_boundary, hfg])
    have hnode (x : P) (hx : x ∈ U) (hxn : grade ℕ x = m + 1) : f x = g x := by
      obtain ⟨y, hy, hyx⟩ := h.exists_mem_facesIn_reflTransGen_graph hd.le hx hxn
      clear hx hxn
      induction hyx with
      | refl => exact hbd false (mem_boundary_of_mem_facesIn hy le_rfl)
      | tail _ e ih' => exact eq_of_graph_adj_of_isMoleculeIn f g h hd hfg hcl e ih'
    intro x hx
    have hU (y : P) (hy : y ∈ (U : Set P)) : grade ℕ y ≤ m + 1 :=
      krullDim_le_coe_iff.1 hd.le ⟨y, hy⟩
    obtain ⟨z, hxz, hz⟩ := GradeOrder.exists_le_maximal hU hx
    rcases (hU z hz.prop).lt_or_eq with hlt | heq
    · exact hbd false ((P.boundary U m false).lower hxz
        (mem_boundary_of_maximal_of_grade_le hz (by omega) false))
    · exact hcl z hz.prop (hnode z hz.prop heq) x hxz

end Rigidity

theorem IsMolecule.subsingleton_iso {Q : OGP.{u}} (hP : P.IsMolecule) : Subsingleton (P ≅ Q) :=
  ⟨fun e e' => Iso.ext (by
    ext x
    exact IsMoleculeIn.eqOn_of_map_eq e.hom e'.hom hP
      (by rw [map_top_of_isIso, map_top_of_isIso]) (LowerSet.mem_top (a := x)))⟩

end Atoms.Molecule.OGP
