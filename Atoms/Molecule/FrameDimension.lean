import Mathlib.Order.GameAdd
import Atoms.Molecule.HassePath
import Atoms.Molecule.Layering.Interior

universe u v

open Order Set Topology

namespace Atoms.Molecule.OGP

variable {P : OGP.{u}}

variable (P) in
def frame (U : LowerSet P) : LowerSet P where
  carrier := {z | ∃ x y, Maximal (· ∈ U) x ∧ Maximal (· ∈ U) y ∧ x ≠ y ∧ z ≤ x ∧ z ≤ y}
  lower' := fun _ _ hba ⟨x, y, hx, hy, hxy, hax, hay⟩ =>
    ⟨x, y, hx, hy, hxy, hba.trans hax, hba.trans hay⟩

@[simp] theorem mem_frame {U : LowerSet P} {z : P} :
    z ∈ P.frame U ↔ ∃ x y, Maximal (· ∈ U) x ∧ Maximal (· ∈ U) y ∧ x ≠ y ∧ z ≤ x ∧ z ≤ y :=
  Iff.rfl

theorem frame_le (U : LowerSet P) : P.frame U ≤ U :=
  fun _ ⟨_, _, hx, _, _, hzx, _⟩ => U.lower hzx hx.prop

private theorem lt_of_mem_frame {U : LowerSet P} {x y z : P} (hx : Maximal (· ∈ U) x)
    (hy : Maximal (· ∈ U) y) (hxy : x ≠ y) (hzx : z ≤ x) (hzy : z ≤ y) : z < x :=
  lt_of_le_of_ne hzx fun h => hxy (hx.eq_of_le hy.prop (h ▸ hzy))

private theorem krullDim_lt_of_forall_grade_lt {s : LowerSet P} {n : ℕ}
    (h : ∀ z ∈ s, grade ℕ z < n) : krullDim s < n := by
  rcases isEmpty_or_nonempty s with hs | ⟨z, hz⟩
  · rw [krullDim_eq_bot]
    exact WithBot.bot_lt_coe _
  · have hn := h z hz
    have hle : krullDim s ≤ (n - 1 : ℕ) :=
      krullDim_le_coe_iff.2 fun a => (Nat.le_sub_one_of_lt (h a a.2) : grade ℕ (a : P) ≤ n - 1)
    exact hle.trans_lt (by exact_mod_cast (by omega : n - 1 < n))

theorem IsMoleculeIn.krullDim_frame_lt {U : LowerSet P} (hU : IsMoleculeIn P U) :
    krullDim (P.frame U) < krullDim U := by
  obtain ⟨n, hn⟩ := hU.exists_krullDim_eq
  rw [hn]
  refine krullDim_lt_of_forall_grade_lt fun z ⟨x, y, hx, hy, hxy, hzx, hzy⟩ => ?_
  exact (grade_strictMono (lt_of_mem_frame hx hy hxy hzx hzy)).trans_le
    (krullDim_le_coe_iff.1 hn.le ⟨x, hx.prop⟩)

theorem IsMoleculeIn.krullDim_frame_eq_bot_iff {U : LowerSet P} (hU : IsMoleculeIn P U) :
    krullDim (P.frame U) = ⊥ ↔ P.IsAtomIn U := by
  rw [krullDim_eq_bot_iff, isEmpty_subtype]
  refine ⟨fun h => ⟨hU, ?_⟩, fun ⟨_, t, ht⟩ z ⟨x, y, hx, hy, hxy, _⟩ => ?_⟩
  · obtain ⟨x₀, hx₀⟩ := hU.nonempty
    obtain ⟨x, -, hx⟩ := hU.exists_le_maximal hx₀
    let V : LowerSet P := lowerClosure {y | Maximal (· ∈ U) y ∧ y ≠ x}
    have hcover : (U : Set P) ⊆ (LowerSet.Iic x : Set P) ∪ (V : Set P) := fun w hw => by
      obtain ⟨y, hwy, hy⟩ := hU.exists_le_maximal hw
      by_cases hyx : y = x
      · exact Or.inl (hyx ▸ hwy)
      · exact Or.inr (mem_lowerClosure.2 ⟨y, ⟨hy, hyx⟩, hwy⟩)
    have hdisj : (U : Set P) ∩ ((LowerSet.Iic x : Set P) ∩ (V : Set P)) = ∅ :=
      Set.eq_empty_of_forall_notMem fun w ⟨_, hwx, hwV⟩ => by
        obtain ⟨y, ⟨hy, hyx⟩, hwy⟩ := mem_lowerClosure.1 hwV
        exact h w ⟨x, y, hx, hy, Ne.symm hyx, hwx, hwy⟩
    rcases isPreconnected_iff_subset_of_disjoint_closed.1 hU.isConnected.isPreconnected _ _
      (IsUpperSet.isClosed_iff_isLower.2 (LowerSet.Iic x).lower)
      (IsUpperSet.isClosed_iff_isLower.2 V.lower) hcover hdisj with hle | hle
    · exact ⟨x, SetLike.coe_injective (le_antisymm hle (LowerSet.Iic_le.2 hx.prop))⟩
    · obtain ⟨y, ⟨hy, hyx⟩, hxy⟩ := mem_lowerClosure.1 (hle hx.prop)
      exact absurd (hx.eq_of_le hy.prop hxy).symm hyx
  · subst ht
    have hmax {w : P} (hw : Maximal (· ∈ LowerSet.Iic t) w) : w = t :=
      hw.eq_of_le (LowerSet.mem_Iic_iff.2 le_rfl) hw.prop
    exact hxy ((hmax hx).trans (hmax hy).symm)

theorem IsMoleculeIn.krullDim_frame_lt_layeringDim {U : LowerSet P} (hU : IsMoleculeIn P U)
    [DecidablePred fun j => (P.topsAbove U j).Subsingleton] :
    krullDim (P.frame U) < (P.layeringDim U hU : WithBot ℕ∞) := by
  refine krullDim_lt_of_forall_grade_lt fun z ⟨x, y, hx, hy, hxy, hzx, hzy⟩ => ?_
  refine (lt_layeringDim_iff hU).2 ⟨x, ⟨hx, ?_⟩, y, ⟨hy, ?_⟩, hxy⟩
  · exact grade_strictMono (lt_of_mem_frame hx hy hxy hzx hzy)
  · exact grade_strictMono (lt_of_mem_frame hy hx (Ne.symm hxy) hzy hzx)

theorem IsLayering.krullDim_frame_le {k : ℕ} {U : LowerSet P} {L : List (LowerSet P)}
    (hL : P.IsLayering k U L) : krullDim (P.frame U) ≤ k := by
  refine krullDim_le_coe_iff.2 fun ⟨z, x, y, hx, hy, hxy, hzx, hzy⟩ => ?_
  have hzx' := grade_strictMono (𝕆 := ℕ) (lt_of_mem_frame hx hy hxy hzx hzy)
  have hzy' := grade_strictMono (𝕆 := ℕ) (lt_of_mem_frame hy hx (Ne.symm hxy) hzy hzx)
  by_cases hkx : k < grade ℕ x
  · by_cases hky : k < grade ℕ y
    · obtain ⟨i, hi, hxi⟩ := hL.exists_mem_getD hx.prop
      obtain ⟨j, hj, hyj⟩ := hL.exists_mem_getD hy.prop
      have hij : i ≠ j := by
        rintro rfl
        exact hxy ((hL.existsUnique_top_getD hi).unique
          ⟨hx.mono (fun _ h => hL.le hi h) hxi, hkx⟩ ⟨hy.mono (fun _ h => hL.le hi h) hyj, hky⟩)
      exact hL.grade_le_of_mem_of_mem hij hi hj ((L.getD i ⊥).lower hzx hxi)
        ((L.getD j ⊥).lower hzy hyj)
    · change grade ℕ z ≤ k
      omega
  · change grade ℕ z ≤ k
    omega

theorem IsMoleculeIn.boundary_Iic_le_boundary {U : LowerSet P} (hU : IsMoleculeIn P U) {x : P}
    (hx : Maximal (· ∈ U) x) {k : ℕ} (hk : krullDim (P.frame U) < k) (α : Bool) :
    P.boundary (.Iic x) k α ≤ P.boundary U k α := by
  by_cases hkx : grade ℕ x ≤ k
  · rw [boundary_eq_self (by rw [LowerSet.krullDim_Iic]; exact_mod_cast hkx)]
    exact LowerSet.Iic_le.2 (mem_boundary_of_maximal_of_grade_le hx hkx α)
  have hT := hU.isAtomIn_Iic hx.prop
  have hdim : krullDim (P.boundary (.Iic x) k α) = k :=
    hT.isMoleculeIn.krullDim_boundary
      (by rw [LowerSet.krullDim_Iic]; exact_mod_cast (not_le.1 hkx).le) α
  intro w hw
  obtain ⟨m, hwm, hm⟩ := (hT.isMoleculeIn.boundary k α).exists_le_maximal hw
  have hmk : grade ℕ m = k := (hT.isRound.boundary k α).grade_eq_of_maximal hdim hm
  have hmx : m ∈ P.facesIn (Set.Iic x) k α := mem_facesIn_of_mem_boundary hm.prop hmk
  refine mem_boundary_of_mem_facesIn ⟨U.lower hmx.1 hx.prop, hmk, ?_⟩ hwm
  refine Set.disjoint_left.2 fun c hc hcU => ?_
  obtain ⟨x', hcx', hx'⟩ := hU.exists_le_maximal hcU
  by_cases hxx' : x = x'
  · subst hxx'
    exact Set.disjoint_left.1 hmx.2.2 hc hcx'
  · have hmF : m ∈ P.frame U := ⟨x, x', hx, hx', hxx', hmx.1, hc.1.le.trans hcx'⟩
    have := grade_le_krullDim (⟨m, hmF⟩ : ↥(P.frame U))
    exact absurd (this.trans_lt hk) (by
      change ¬ ((grade ℕ m : ℕ) : WithBot ℕ∞) < (k : WithBot ℕ∞)
      rw [hmk]
      exact lt_irrefl _)

private theorem grade_eq_of_mem_topsAbove {S t : P} (hS : IsMoleculeIn P (.Iic S)) {k : ℕ}
    (α : Bool) (hSk : k + 1 ≤ grade ℕ S)
    (ht : t ∈ P.topsAbove (P.boundary (.Iic S) (k + 1) α) k) :
    grade ℕ t = k + 1 ∧ t ∈ P.facesIn (Set.Iic S) (k + 1) α := by
  have hdim : krullDim (P.boundary (.Iic S) (k + 1) α) = (k + 1 : ℕ) :=
    hS.krullDim_boundary (by rw [LowerSet.krullDim_Iic]; exact_mod_cast hSk) α
  have hT := hS.isAtomIn_Iic (le_refl S)
  have hg := (hT.isRound.boundary (k + 1) α).grade_eq_of_maximal hdim ht.1
  exact ⟨hg, mem_facesIn_of_mem_boundary ht.1.prop hg⟩

private theorem mem_topsAbove_of_grade_eq {S t : P} (hS : IsMoleculeIn P (.Iic S)) {k : ℕ}
    (α : Bool) (hSk : k + 1 ≤ grade ℕ S) (ht : t ∈ P.boundary (.Iic S) (k + 1) α)
    (hg : grade ℕ t = k + 1) : t ∈ P.topsAbove (P.boundary (.Iic S) (k + 1) α) k := by
  have hdim : krullDim (P.boundary (.Iic S) (k + 1) α) = (k + 1 : ℕ) :=
    hS.krullDim_boundary (by rw [LowerSet.krullDim_Iic]; exact_mod_cast hSk) α
  exact ⟨maximal_mem_of_krullDim_le ht (by rw [hdim, hg]), by omega⟩

private theorem wellFounded_cond_adj {G : Digraph P} (hG : G.IsAcyclic) {s : Set P}
    (hs : s.Finite) (β : Bool) :
    WellFounded (fun a b : s => G.Adj (cond β a b) (cond β b a)) := by
  have : Finite s := hs.to_subtype
  let T : s → s → Prop := fun a b => Relation.TransGen G.Adj (cond β a b) (cond β b a)
  have : IsTrans s T := ⟨fun a b c hab hbc => by
    cases β
    · exact Relation.TransGen.trans hbc hab
    · exact Relation.TransGen.trans hab hbc⟩
  have : Std.Irrefl T := ⟨fun a h => by
    cases β
    · exact hG _ h
    · exact hG _ h⟩
  exact Subrelation.wf (fun h => Relation.TransGen.single h)
    (Finite.wellFounded_of_trans_of_irrefl T)

private theorem exists_Iic_inf_le_boundary {M : LowerSet P} {k : ℕ} (hM : IsMoleculeIn P M)
    (hd : krullDim M = (k + 1 : ℕ)) {a b : P} (ha : a ∈ M) (hb : b ∈ M) (hga : grade ℕ a = k + 1)
    (hgb : grade ℕ b = k + 1) (hab : a ≠ b) :
    ∃ γ, LowerSet.Iic a ⊓ LowerSet.Iic b ≤
      P.boundary (.Iic a) k γ ⊓ P.boundary (.Iic b) k (!γ) := by
  obtain ⟨L, hL⟩ := admitsLayering_pred_krullDim hM hd (Nat.succ_pos k)
  have hamax : Maximal (· ∈ M) a := maximal_mem_of_krullDim_le ha (by rw [hd, hga])
  have hbmax : Maximal (· ∈ M) b := maximal_mem_of_krullDim_le hb (by rw [hd, hgb])
  obtain ⟨i, hi, hai⟩ := hL.exists_mem_getD ha
  obtain ⟨j, hj, hbj⟩ := hL.exists_mem_getD hb
  have hij : i ≠ j := by
    rintro rfl
    exact hab ((hL.existsUnique_top_getD hi).unique
      ⟨hamax.mono (fun _ h => hL.le hi h) hai, by omega⟩
      ⟨hbmax.mono (fun _ h => hL.le hi h) hbj, by omega⟩)
  rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
  · exact ⟨true, hL.Iic_inf_le_of_lt hlt hj hai hbj⟩
  · exact ⟨false, by
      rw [inf_comm]
      exact (hL.Iic_inf_le_of_lt hlt hi hbj hai).trans (inf_comm _ _).le⟩

private theorem exists_mem_boundary_of_mem_boundary_succ {x z : P} (hx : IsMoleculeIn P (.Iic x))
    {k : ℕ} (hk : k + 1 ≤ grade ℕ x) (hzx : z < x) (α : Bool)
    (h1 : z ∈ P.boundary (.Iic x) (k + 1) α) (h2 : z ∈ P.boundary (.Iic x) (k + 1) (!α)) :
    ∃ β, z ∈ P.boundary (.Iic x) k β := by
  rcases hk.lt_or_eq with hlt | heq
  · have hT := hx.isAtomIn_Iic (le_refl x)
    have hkd : ((k + 1 : ℕ) : WithBot ℕ∞) < krullDim (LowerSet.Iic x) := by
      rw [LowerSet.krullDim_Iic]; exact_mod_cast hlt
    have hmem : z ∈ P.boundary (.Iic x) (k + 1) false ⊓ P.boundary (.Iic x) (k + 1) true := by
      cases α
      · exact ⟨h1, h2⟩
      · exact ⟨h2, h1⟩
    rw [hT.isRound.inf_boundary_succ k hkd] at hmem
    exact mem_boundaryFull.1 hmem
  · obtain ⟨β, hβ⟩ := exists_mem_boundary_Iic_of_lt hzx
    exact ⟨β, by rwa [← heq, Nat.add_sub_cancel] at hβ⟩

private theorem mem_boundary_or_exists_adj {S t z : P} (hS : IsMoleculeIn P (.Iic S)) {k : ℕ}
    (α β : Bool) (hSk : k + 1 ≤ grade ℕ S)
    (ht : t ∈ P.topsAbove (P.boundary (.Iic S) (k + 1) α) k)
    (hz : z ∈ P.boundary (.Iic t) k (!β)) :
    z ∈ P.boundary (.Iic S) k (!β) ∨ ∃ t' ∈ P.topsAbove (P.boundary (.Iic S) (k + 1) α) k,
      z ≤ t' ∧
        (P.maximalFlowGraph (P.boundary (.Iic S) (k + 1) α) k).Adj (cond β t' t) (cond β t t') := by
  obtain ⟨htg, htf⟩ := grade_eq_of_mem_topsAbove hS α hSk ht
  have hTt := hS.isAtomIn_Iic (show t ≤ S from htf.1)
  have hdim : krullDim (P.boundary (.Iic t) k (!β)) = k :=
    hTt.1.krullDim_boundary (by rw [LowerSet.krullDim_Iic, htg]; exact_mod_cast k.le_succ) _
  obtain ⟨w, hzw, hw⟩ := (hTt.1.boundary k (!β)).exists_le_maximal hz
  have hwg : grade ℕ w = k := (hTt.isRound.boundary k (!β)).grade_eq_of_maximal hdim hw
  have hwf : w ∈ P.facesIn (Set.Iic t) k (!β) := mem_facesIn_of_mem_boundary hw.prop hwg
  have hwt : w ⋖ t := GradeOrder.covBy_of_le_of_grade_eq_add_one hwf.1 (by omega)
  have hor : P.orient hwt = !β := by
    by_contra hne
    have hβ : P.orient hwt = β := by
      revert hne
      generalize P.orient hwt = o
      cases o <;> cases β <;> decide
    have hdis := hwf.2.2
    rw [Bool.not_not] at hdis
    exact Set.disjoint_left.1 hdis ⟨hwt, hβ⟩ (Set.mem_Iic.2 le_rfl)
  by_cases hcof : ∃ m ∈ P.cofaces β w, m ∈ P.boundary (.Iic S) (k + 1) α
  · obtain ⟨m, ⟨hwm, hmor⟩, hmM⟩ := hcof
    have hmg : grade ℕ m = k + 1 := by
      have := Nat.covBy_iff_add_one_eq.1 (hwm.grade ℕ)
      omega
    have hmt := mem_topsAbove_of_grade_eq hS α hSk hmM hmg
    have hwm' : w ∈ P.facesIn (Set.Iic m) k β := by
      exact (mem_facesIn_Iic_iff_mem_faces hmg β).2 ⟨hwm, hmor⟩
    refine Or.inr ⟨m, hmt, hzw.trans hwm.le, ?_⟩
    cases β
    · exact ⟨ht, hmt, ht.2, hmt.2, w, hwf, hwm'⟩
    · exact ⟨hmt, ht, hmt.2, ht.2, w, hwm', hwf⟩
  · refine Or.inl ?_
    have hwM : w ∈ P.facesIn (P.boundary (.Iic S) (k + 1) α) k (!β) := by
      refine ⟨(P.boundary (.Iic S) (k + 1) α).lower hwt.le ht.1.prop, hwg, ?_⟩
      rw [Bool.not_not]
      exact Set.disjoint_left.2 fun c hc hcM => hcof ⟨c, hc, hcM⟩
    have hw' := mem_boundary_of_mem_facesIn hwM (le_refl w)
    rw [hS.isGlobular.boundary_boundary_eq_of_le k.le_succ (Or.inl k.lt_succ_self)] at hw'
    exact (P.boundary (.Iic S) k (!β)).lower hzw hw'

private theorem mem_boundary_not_or_mem_boundary_not {U : LowerSet P} (hU : IsMoleculeIn P U)
    {x y : P} (hx : Maximal (· ∈ U) x) (hy : Maximal (· ∈ U) y) (hxy : x ≠ y) {k : ℕ}
    (hk : krullDim (P.frame U) ≤ k) (hkx : k < grade ℕ x) (hky : k < grade ℕ y) (α β : Bool)
    {z : P} (hzx : z ∈ P.boundary (.Iic x) k β) (hzy : z ∈ P.boundary (.Iic y) k β) :
    z ∈ P.boundary (.Iic x) k (!β) ∨ z ∈ P.boundary (.Iic y) k (!β) := by
  have hIx : IsMoleculeIn P (.Iic x) := (hU.isAtomIn_Iic hx.prop).1
  have hIy : IsMoleculeIn P (.Iic y) := (hU.isAtomIn_Iic hy.prop).1
  have hk1 : krullDim (P.frame U) < ((k + 1 : ℕ) : WithBot ℕ∞) :=
    hk.trans_lt (by exact_mod_cast k.lt_succ_self)
  have hdimU : ((k + 1 : ℕ) : WithBot ℕ∞) ≤ krullDim U :=
    (by exact_mod_cast hkx : ((k + 1 : ℕ) : WithBot ℕ∞) ≤ grade ℕ x).trans
      (grade_le_krullDim (⟨x, hx.prop⟩ : ↥U))
  have hMol : IsMoleculeIn P (P.boundary U (k + 1) α) := hU.boundary _ _
  have hMdim : krullDim (P.boundary U (k + 1) α) = (k + 1 : ℕ) := hU.krullDim_boundary hdimU α
  have hdim (S : P) (hS : IsMoleculeIn P (.Iic S)) (hSk : k < grade ℕ S) :
      krullDim (P.boundary (.Iic S) (k + 1) α) = (k + 1 : ℕ) :=
    hS.krullDim_boundary (by rw [LowerSet.krullDim_Iic]; exact_mod_cast hSk) α
  have hfin (S : P) (hS : IsMoleculeIn P (.Iic S)) :
      (P.topsAbove (P.boundary (.Iic S) (k + 1) α) k).Finite :=
    (hS.boundary (k + 1) α).finite.subset fun _ ht => ht.1.prop
  have wx := wellFounded_cond_adj
    ((hIx.boundary (k + 1) α).isAcyclic_maximalFlowGraph_of_krullDim_eq (hdim x hIx hkx))
    (hfin x hIx) β
  have wy := wellFounded_cond_adj
    ((hIy.boundary (k + 1) α).isAcyclic_maximalFlowGraph_of_krullDim_eq (hdim y hIy hky))
    (hfin y hIy) β
  have hbU (S : P) (hS : Maximal (· ∈ U) S) {t : P}
      (ht : t ∈ P.boundary (.Iic S) (k + 1) α) : t ∈ P.boundary U (k + 1) α :=
    hU.boundary_Iic_le_boundary hS hk1 α ht
  have key : ∀ p : ↥(P.topsAbove (P.boundary (.Iic x) (k + 1) α) k) ×
      ↥(P.topsAbove (P.boundary (.Iic y) (k + 1) α) k), z ≤ p.1 → z ≤ p.2 →
      z ∈ P.boundary (.Iic x) k (!β) ∨ z ∈ P.boundary (.Iic y) k (!β) := by
    intro p
    refine (wx.prod_gameAdd wy).induction (C := fun p => z ≤ p.1 → z ≤ p.2 →
      z ∈ P.boundary (.Iic x) k (!β) ∨ z ∈ P.boundary (.Iic y) k (!β)) p ?_
    rintro ⟨a, b⟩ ih hza hzb
    obtain ⟨hga, -⟩ := grade_eq_of_mem_topsAbove hIx α hkx a.2
    obtain ⟨hgb, -⟩ := grade_eq_of_mem_topsAbove hIy α hky b.2
    have hax : (a : P) ≤ x := LowerSet.mem_Iic_iff.1 (boundary_le _ _ _ a.2.1.prop)
    have hby : (b : P) ≤ y := LowerSet.mem_Iic_iff.1 (boundary_le _ _ _ b.2.1.prop)
    have hne : (a : P) ≠ b := fun h => by
      have hf : (a : P) ∈ P.frame U := ⟨x, y, hx, hy, hxy, hax, h ▸ hby⟩
      have := (grade_le_krullDim (⟨a, hf⟩ : ↥(P.frame U))).trans hk
      have h' : grade ℕ (a : P) ≤ k := by exact_mod_cast this
      omega
    obtain ⟨γ, hγ⟩ := exists_Iic_inf_le_boundary hMol hMdim
      (hbU x hx a.2.1.prop) (hbU y hy b.2.1.prop) hga hgb hne
    obtain ⟨hγa, hγb⟩ := hγ ⟨hza, hzb⟩
    by_cases hγβ : γ = β
    · subst hγβ
      rcases mem_boundary_or_exists_adj hIy α γ hky b.2 hγb with h | ⟨t, ht, hzt, hadj⟩
      · exact Or.inr h
      · exact ih ⟨a, ⟨t, ht⟩⟩ (Prod.GameAdd.snd hadj) hza hzt
    · have hγ' : γ = !β := by revert hγβ; cases γ <;> cases β <;> decide
      subst hγ'
      rcases mem_boundary_or_exists_adj hIx α β hkx a.2 hγa with h | ⟨t, ht, hzt, hadj⟩
      · exact Or.inl h
      · exact ih ⟨⟨t, ht⟩, b⟩ (Prod.GameAdd.fst hadj) hzt hzb
  have hstart (S : P) (hS : IsMoleculeIn P (.Iic S)) (hSk : k < grade ℕ S)
      (hz : z ∈ P.boundary (.Iic S) k β) :
      ∃ t ∈ P.topsAbove (P.boundary (.Iic S) (k + 1) α) k, z ≤ t := by
    have hzb : z ∈ P.boundary (.Iic S) (k + 1) α :=
      hS.isGlobular.boundary_le_boundary k.lt_succ_self β α hz
    obtain ⟨t, hzt, ht⟩ := (hS.boundary (k + 1) α).exists_le_maximal hzb
    have hg := ((hS.isAtomIn_Iic (le_refl S)).isRound.boundary (k + 1) α).grade_eq_of_maximal
      (hdim S hS hSk) ht
    exact ⟨t, ⟨ht, by omega⟩, hzt⟩
  obtain ⟨a, ha, hza⟩ := hstart x hIx hkx hzx
  obtain ⟨b, hb, hzb⟩ := hstart y hIy hky hzy
  exact key (⟨a, ha⟩, ⟨b, hb⟩) hza hzb

private theorem exists_mem_boundary_inf {U : LowerSet P} (hU : IsMoleculeIn P U) {x y : P}
    (hx : Maximal (· ∈ U) x) (hy : Maximal (· ∈ U) y) (hxy : x ≠ y) (k : ℕ)
    (hk : krullDim (P.frame U) ≤ k) {z : P} (hz : z ∈ LowerSet.Iic x ⊓ LowerSet.Iic y) :
    ∃ β, z ∈ P.boundary (.Iic x) k β ∧ z ∈ P.boundary (.Iic y) k (!β) := by
  have hxsub := hU.Iic_isSubmoleculeOf hx.prop
  have hysub := hU.Iic_isSubmoleculeOf hy.prop
  by_cases hmin : min (grade ℕ x) (grade ℕ y) ≤ k
  · have hself (S : P) (hS : grade ℕ S ≤ k) (β : Bool) :
        P.boundary (.Iic S) k β = LowerSet.Iic S :=
      boundary_eq_self (by rw [LowerSet.krullDim_Iic]; exact_mod_cast hS) β
    rcases min_le_iff.1 hmin with hgx | hgy
    · have hzU : z ∈ P.boundary U k true :=
        (P.boundary U k true).lower hz.1 (mem_boundary_of_maximal_of_grade_le hx hgx true)
      refine ⟨false, by rw [hself x hgx]; exact hz.1, ?_⟩
      exact hysub.inf_boundary_le k true ⟨hz.2, hzU⟩
    · have hzU : z ∈ P.boundary U k false :=
        (P.boundary U k false).lower hz.2 (mem_boundary_of_maximal_of_grade_le hy hgy false)
      refine ⟨false, hxsub.inf_boundary_le k false ⟨hz.1, hzU⟩, ?_⟩
      rw [Bool.not_false, hself y hgy]
      exact hz.2
  · have hkx : k < grade ℕ x := by have := lt_min_iff.1 (not_le.1 hmin); omega
    have hky : k < grade ℕ y := by have := lt_min_iff.1 (not_le.1 hmin); omega
    have hk1 : krullDim (P.frame U) < ((k + 1 : ℕ) : WithBot ℕ∞) :=
      hk.trans_lt (by exact_mod_cast k.lt_succ_self)
    obtain ⟨α, hzxα, hzyα⟩ := exists_mem_boundary_inf hU hx hy hxy (k + 1)
      (hk1.le) hz
    have hzx' : z ∈ P.boundary (.Iic x) (k + 1) (!α) :=
      hxsub.inf_boundary_le (k + 1) (!α)
        ⟨hz.1, hU.boundary_Iic_le_boundary hy hk1 (!α) hzyα⟩
    have hzy' : z ∈ P.boundary (.Iic y) (k + 1) α :=
      hysub.inf_boundary_le (k + 1) α ⟨hz.2, hU.boundary_Iic_le_boundary hx hk1 α hzxα⟩
    have hIx : IsMoleculeIn P (.Iic x) := (hU.isAtomIn_Iic hx.prop).1
    have hIy : IsMoleculeIn P (.Iic y) := (hU.isAtomIn_Iic hy.prop).1
    obtain ⟨βx, hβx⟩ := exists_mem_boundary_of_mem_boundary_succ hIx hkx
      (lt_of_mem_frame hx hy hxy hz.1 hz.2) α hzxα hzx'
    obtain ⟨βy, hβy⟩ := exists_mem_boundary_of_mem_boundary_succ hIy hky
      (lt_of_mem_frame hy hx hxy.symm hz.2 hz.1) α hzy' hzyα
    by_cases hb : βy = !βx
    · exact ⟨βx, hβx, hb ▸ hβy⟩
    · have hβ : βy = βx := by revert hb; cases βy <;> cases βx <;> decide
      rcases mem_boundary_not_or_mem_boundary_not hU hx hy hxy hk hkx hky α βx hβx
        (hβ ▸ hβy) with h | h
      · exact ⟨!βx, h, by rw [Bool.not_not]; exact hβ ▸ hβy⟩
      · exact ⟨βx, hβx, h⟩
termination_by min (grade ℕ x) (grade ℕ y) - k
decreasing_by omega

theorem IsMoleculeIn.Iic_inf_Iic_eq {U : LowerSet P} (hU : IsMoleculeIn P U) {x y : P}
    (hx : Maximal (· ∈ U) x) (hy : Maximal (· ∈ U) y) (hxy : x ≠ y) {k : ℕ}
    (hk : krullDim (P.frame U) ≤ k) :
    LowerSet.Iic x ⊓ LowerSet.Iic y =
      (P.boundary (.Iic x) k false ⊓ P.boundary (.Iic y) k true) ⊔
        (P.boundary (.Iic x) k true ⊓ P.boundary (.Iic y) k false) := by
  refine le_antisymm (fun z hz => ?_) (sup_le (inf_le_inf (boundary_le _ k false)
    (boundary_le _ k true)) (inf_le_inf (boundary_le _ k true) (boundary_le _ k false)))
  obtain ⟨β, h1, h2⟩ := exists_mem_boundary_inf hU hx hy hxy k hk hz
  cases β
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩

variable (P) in
structure IsFrameAcyclic (U : LowerSet P) : Prop where
  isMoleculeIn : IsMoleculeIn P U
  isAcyclic : ∀ V, P.IsSubmoleculeOf V U → ∀ r : ℕ, krullDim (P.frame V) = r →
    (P.maximalFlowGraph V r).IsAcyclic

theorem maximalFlowGraph_eq_restrict (U : LowerSet P) (k : ℕ) :
    P.maximalFlowGraph U k = (P.flowGraph k).restrict (P.topsAbove U k) :=
  rfl

theorem IsFrameAcyclic.of_isSubmoleculeOf {U V : LowerSet P} (hU : P.IsFrameAcyclic U)
    (hVU : P.IsSubmoleculeOf V U) : P.IsFrameAcyclic V :=
  ⟨hVU.isMoleculeIn, fun W hWV r hr => hU.isAcyclic W (hWV.trans hVU) r hr⟩

theorem IsMoleculeIn.isFrameAcyclic {U : LowerSet P} (hU : IsMoleculeIn P U)
    (h : ∀ k, ((P.flowGraph k).restrict U).IsAcyclic) : P.IsFrameAcyclic U := by
  refine ⟨hU, fun V hVU r _ => (h r).mono ?_⟩
  rw [maximalFlowGraph_eq_restrict]
  exact Digraph.restrict_mono fun _ ht => hVU.le ht.1.prop

theorem IsMoleculeIn.isFrameAcyclic_of_isAcyclic {U : LowerSet P} (hU : IsMoleculeIn P U)
    (h : (P.hasseDiagram.restrict U).IsAcyclic) : P.IsFrameAcyclic U :=
  hU.isFrameAcyclic fun _ => isAcyclic_flowGraph_restrict
    (isAcyclic_extendedFlowGraph_restrict (fun _ hx => (hU.isAtomIn_Iic hx).1) h _)

theorem IsAcyclic.isFrameAcyclic_of_isMorphism {Q : OGP.{v}} (hQ : Q.IsAcyclic)
    (hP : P.IsMolecule) {f : P → Q} (hf : IsMorphism f) : P.IsFrameAcyclic ⊤ :=
  hP.isFrameAcyclic_of_isAcyclic (by
    rw [LowerSet.coe_top, Digraph.restrict_univ]
    exact hf.isAcyclic hQ)

end Atoms.Molecule.OGP
