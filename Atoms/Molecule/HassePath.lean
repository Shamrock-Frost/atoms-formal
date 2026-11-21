import Atoms.Molecule.FlowGraph
import Atoms.Molecule.RegularComplex.Basic

universe u

open Order Set

namespace Atoms.Molecule.OGP

variable {P : OGP.{u}}

private theorem adj_hasseDiagram_restrict_of_covBy {s : Set P} {y m : P} (hy : y ∈ s) (hm : m ∈ s)
    (h : y ⋖ m) (α : Bool) (hα : P.orient h = α) :
    (P.hasseDiagram.restrict s).Adj (cond α m y) (cond α y m) := by
  subst hα
  cases hh : P.orient h
  · exact ⟨hy, hm, Or.inl ⟨h, hh⟩⟩
  · exact ⟨hm, hy, Or.inr ⟨h, hh⟩⟩

theorem reflTransGen_hasseDiagram_of_mem_facesIn {x y : P} (hx : IsMoleculeIn P (.Iic x)) {k : ℕ}
    (α : Bool) (hy : y ∈ P.facesIn (Set.Iic x) k α) :
    Relation.ReflTransGen (P.hasseDiagram.restrict (Set.Iic x)).Adj (cond α x y) (cond α y x) := by
  have hT := hx.isAtomIn_Iic (le_refl x)
  obtain ⟨d, hd⟩ : ∃ d, grade ℕ x = k + d := ⟨grade ℕ x - k, by
    have := grade_mono (𝕆 := ℕ) hy.1; have := hy.2.1; omega⟩
  induction d generalizing k y with
  | zero =>
    have hyk := hy.2.1
    obtain rfl : y = x := GradeOrder.eq_of_le_of_grade_le hy.1 (by omega)
    cases α <;> exact .refl
  | succ d ih =>
    have hyb : y ∈ P.boundary (.Iic x) (k + 1) α :=
      hx.isGlobular.boundary_le_boundary (Nat.lt_succ_self k) α α
        (mem_boundary_of_mem_facesIn hy le_rfl)
    have hdim : krullDim (P.boundary (.Iic x) (k + 1) α) = (k + 1 : ℕ) :=
      hx.krullDim_boundary (by rw [LowerSet.krullDim_Iic, hd]; exact_mod_cast (by omega)) α
    obtain ⟨m, hym, hm⟩ := (hx.boundary (k + 1) α).exists_le_maximal hyb
    have hmk : grade ℕ m = k + 1 := (hT.isRound.boundary (k + 1) α).grade_eq_of_maximal hdim hm
    have hmf : m ∈ P.facesIn (Set.Iic x) (k + 1) α := mem_facesIn_of_mem_boundary hm.prop hmk
    have hcov : y ⋖ m :=
      GradeOrder.covBy_of_le_of_grade_eq_add_one hym (by rw [hmk, hy.2.1])
    have hor : P.orient hcov = α := by
      by_contra hne
      have : P.orient hcov = !α := by
        cases hh : P.orient hcov <;> cases α <;> first | rfl | exact absurd hh hne
      exact Set.disjoint_left.1 hy.2.2 ⟨hcov, this⟩ hmf.1
    have hedge := adj_hasseDiagram_restrict_of_covBy hy.1 hmf.1 hcov α hor
    have hrest := ih hmf (by omega)
    cases α
    · exact (Relation.ReflTransGen.single hedge).trans hrest
    · exact hrest.trans (.single hedge)

theorem exists_mem_cofaces_mem_interior {U : LowerSet P} {x : P} (hx : x ∈ P.interior U)
    (hxm : ¬ Maximal (· ∈ U) x) (α : Bool) : ∃ y ∈ P.cofaces α x, y ∈ P.interior U := by
  obtain ⟨y₀, hxy₀, hy₀⟩ := (not_maximal_iff_exists_gt hx.1).1 hxm
  have hk : (grade ℕ x : WithBot ℕ∞) < krullDim U :=
    (Nat.cast_lt.2 (grade_strictMono hxy₀)).trans_le (grade_le_krullDim (⟨y₀, hy₀⟩ : ↥U))
  have hcof : ∃ y ∈ P.cofaces α x, y ∈ U := by
    by_contra hno
    push Not at hno
    have hface : x ∈ P.facesIn U (grade ℕ x) (!α) :=
      ⟨hx.1, rfl, Set.disjoint_left.2 fun c hc hcU => hno c (by simpa using hc) hcU⟩
    exact hx.2 (boundary_le_properBoundary hk (!α) (mem_boundary_of_mem_facesIn hface le_rfl))
  obtain ⟨y, hy, hyU⟩ := hcof
  refine ⟨y, hy, hyU, fun hyb => hx.2 ?_⟩
  exact (P.properBoundary U).lower hy.1.le hyb

theorem reflTransGen_hasseDiagram_of_mem_interior {x y : P} (hx : IsMoleculeIn P (.Iic x)) {k : ℕ}
    (α : Bool) (hy : y ∈ P.interior (P.boundary (.Iic x) k α)) :
    Relation.ReflTransGen (P.hasseDiagram.restrict (Set.Iic x)).Adj (cond α x y) (cond α y x) := by
  have hT := hx.isAtomIn_Iic (le_refl x)
  by_cases hkx : grade ℕ x ≤ k
  · rw [boundary_eq_self (by rw [LowerSet.krullDim_Iic]; exact_mod_cast hkx), hx.interior_Iic] at hy
    obtain rfl : y = x := hy
    cases α <;> exact .refl
  have hkx' : k < grade ℕ x := not_le.1 hkx
  have hdim : krullDim (P.boundary (.Iic x) k α) = k :=
    hx.krullDim_boundary (by rw [LowerSet.krullDim_Iic]; exact_mod_cast hkx'.le) α
  have hyk : grade ℕ y ≤ k := grade_le_of_mem_boundary hy.1
  obtain ⟨d, hd⟩ : ∃ d, k = grade ℕ y + d := ⟨k - grade ℕ y, by omega⟩
  induction d generalizing y with
  | zero =>
    exact reflTransGen_hasseDiagram_of_mem_facesIn hx α
      (mem_facesIn_of_mem_boundary hy.1 (by omega))
  | succ d ih =>
    have hnm : ¬ Maximal (· ∈ P.boundary (.Iic x) k α) y := fun hm =>
      absurd ((hT.isRound.boundary k α).grade_eq_of_maximal hdim hm) (by omega)
    obtain ⟨y', hy', hy'I⟩ := exists_mem_cofaces_mem_interior hy hnm α
    obtain ⟨hcov, hor⟩ := hy'
    have hyx : y ≤ x := LowerSet.mem_Iic_iff.1 (boundary_le _ _ _ hy.1)
    have hy'x : y' ≤ x := LowerSet.mem_Iic_iff.1 (boundary_le _ _ _ hy'I.1)
    have hedge := adj_hasseDiagram_restrict_of_covBy (s := Set.Iic x) hyx hy'x hcov α hor
    have hg : grade ℕ y' = grade ℕ y + 1 := (Nat.covBy_iff_add_one_eq.1 (hcov.grade ℕ)).symm
    have hrest := ih hy'I (grade_le_of_mem_boundary hy'I.1) (by omega)
    cases α
    · exact (Relation.ReflTransGen.single hedge).trans hrest
    · exact hrest.trans (.single hedge)

theorem transGen_extendedFlowGraph_restrict {U : LowerSet P} {k : ℕ} {x y : P}
    (h : Relation.TransGen ((P.flowGraph k).restrict U).Adj x y) :
    Relation.TransGen ((P.extendedFlowGraph k).restrict U).Adj x y := by
  have step {x y : P} (hxy : ((P.flowGraph k).restrict U).Adj x y) :
      Relation.TransGen ((P.extendedFlowGraph k).restrict U).Adj x y := by
    obtain ⟨hxU, hyU, hx, hy, z, hzx, hzy⟩ := hxy
    have hz : grade ℕ z ≤ k := hzx.2.1.le
    have hzU : z ∈ U := U.lower hzx.1 hxU
    exact .tail (.single ⟨hxU, hzU, Or.inr ⟨hx, hz, mem_interior_boundary_of_mem_facesIn hzx⟩⟩)
      ⟨hzU, hyU, Or.inl ⟨hz, hy, mem_interior_boundary_of_mem_facesIn hzy⟩⟩
  induction h with
  | single hxy => exact step hxy
  | tail _ hyz ih => exact ih.trans (step hyz)

theorem transGen_hasseDiagram_of_transGen_extendedFlowGraph {U : LowerSet P}
    (hU : ∀ x ∈ U, IsMoleculeIn P (.Iic x)) {k : ℕ} {x y : P}
    (h : Relation.TransGen ((P.extendedFlowGraph k).restrict U).Adj x y) :
    Relation.TransGen (P.hasseDiagram.restrict U).Adj x y := by
  have step {a b : P} (hab : ((P.extendedFlowGraph k).restrict U).Adj a b) :
      Relation.TransGen (P.hasseDiagram.restrict U).Adj a b := by
    obtain ⟨haU, hbU, hab⟩ := hab
    have lift {t : P} (ht : t ∈ U) {a b : P} (hne : a ≠ b)
        (hp : Relation.ReflTransGen (P.hasseDiagram.restrict (Set.Iic t)).Adj a b) :
        Relation.TransGen (P.hasseDiagram.restrict U).Adj a b :=
      (Relation.reflTransGen_iff_eq_or_transGen.1
        (Relation.ReflTransGen.mono (r := (P.hasseDiagram.restrict (Set.Iic t)).Adj)
          (fun _ _ hab => Digraph.restrict_mono (fun _ hz => U.lower hz ht) hab) _ _ hp)
        ).resolve_left hne.symm
    rcases hab with ⟨hg, hk, hint⟩ | ⟨hk, hg, hint⟩
    · exact lift hbU (fun e => by subst e; omega)
        (reflTransGen_hasseDiagram_of_mem_interior (hU b hbU) false hint)
    · exact lift haU (fun e => by subst e; omega)
        (reflTransGen_hasseDiagram_of_mem_interior (hU a haU) true hint)
  induction h with
  | single hab => exact step hab
  | tail _ hbc ih => exact ih.trans (step hbc)

theorem isAcyclic_extendedFlowGraph_restrict {U : LowerSet P}
    (hU : ∀ x ∈ U, IsMoleculeIn P (.Iic x)) (h : (P.hasseDiagram.restrict U).IsAcyclic) (k : ℕ) :
    ((P.extendedFlowGraph k).restrict U).IsAcyclic :=
  fun v hv => h v (transGen_hasseDiagram_of_transGen_extendedFlowGraph hU hv)

theorem isAcyclic_flowGraph_restrict {U : LowerSet P} {k : ℕ}
    (h : ((P.extendedFlowGraph k).restrict U).IsAcyclic) : ((P.flowGraph k).restrict U).IsAcyclic :=
  fun v hv => h v (transGen_extendedFlowGraph_restrict hv)

theorem IsRDC.isStronglyDimensionwiseAcyclic (hP : P.IsRDC) (h : P.IsAcyclic) :
    P.IsStronglyDimensionwiseAcyclic := fun k => by
  have := isAcyclic_extendedFlowGraph_restrict (U := ⊤) (fun x _ => hP x)
    (by rwa [LowerSet.coe_top, Digraph.restrict_univ]) k
  rwa [LowerSet.coe_top, Digraph.restrict_univ] at this

end Atoms.Molecule.OGP
