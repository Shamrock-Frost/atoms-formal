import Atoms.ForMathlib.Combinatorics.Digraph.Acyclic
import Atoms.Molecule.Interior
import Atoms.Molecule.Layering.Existence
import Atoms.Molecule.Rigidity

universe u v

open CategoryTheory Order Set

namespace Atoms.Molecule.OGP

variable {P : OGP.{u}}

variable (P) in
def hasseDiagram : Digraph P where
  Adj y x := y ∈ P.faces false x ∨ x ∈ P.faces true y

variable (P) in
def flowGraph (k : ℕ) : Digraph P where
  Adj x y := k < grade ℕ x ∧ k < grade ℕ y ∧
    (P.facesIn (Set.Iic x) k true ∩ P.facesIn (Set.Iic y) k false).Nonempty

variable (P) in
def maximalFlowGraph (U : LowerSet P) (k : ℕ) : Digraph P where
  Adj x y := x ∈ P.topsAbove U k ∧ y ∈ P.topsAbove U k ∧ (P.flowGraph k).Adj x y

variable (P) in
def extendedFlowGraph (k : ℕ) : Digraph P where
  Adj a b :=
    (grade ℕ a ≤ k ∧ k < grade ℕ b ∧ a ∈ P.interior (P.boundary (.Iic b) k false)) ∨
    (k < grade ℕ a ∧ grade ℕ b ≤ k ∧ b ∈ P.interior (P.boundary (.Iic a) k true))

variable (P) in
def IsOrdering (U : LowerSet P) (k : ℕ) (l : List P) : Prop :=
  (∀ x, x ∈ l ↔ x ∈ P.topsAbove U k) ∧ (P.maximalFlowGraph U k).IsTopologicalSort l

variable (P) in
def IsAcyclic : Prop := P.hasseDiagram.IsAcyclic

variable (P) in
def IsStronglyDimensionwiseAcyclic : Prop := ∀ k, (P.extendedFlowGraph k).IsAcyclic

variable (P) in
def IsDimensionwiseAcyclic : Prop := ∀ k, (P.flowGraph k).IsAcyclic

@[simp] theorem hasseDiagram_adj {x y : P} :
    P.hasseDiagram.Adj y x ↔ y ∈ P.faces false x ∨ x ∈ P.faces true y :=
  Iff.rfl

@[simp] theorem flowGraph_adj {k : ℕ} {x y : P} :
    (P.flowGraph k).Adj x y ↔ k < grade ℕ x ∧ k < grade ℕ y ∧
      (P.facesIn (Set.Iic x) k true ∩ P.facesIn (Set.Iic y) k false).Nonempty :=
  Iff.rfl

@[simp] theorem maximalFlowGraph_adj {U : LowerSet P} {k : ℕ} {x y : P} :
    (P.maximalFlowGraph U k).Adj x y ↔
      x ∈ P.topsAbove U k ∧ y ∈ P.topsAbove U k ∧ (P.flowGraph k).Adj x y :=
  Iff.rfl

@[simp] theorem extendedFlowGraph_adj {k : ℕ} {a b : P} :
    (P.extendedFlowGraph k).Adj a b ↔
      (grade ℕ a ≤ k ∧ k < grade ℕ b ∧ a ∈ P.interior (P.boundary (.Iic b) k false)) ∨
      (k < grade ℕ a ∧ grade ℕ b ≤ k ∧ b ∈ P.interior (P.boundary (.Iic a) k true)) :=
  Iff.rfl

private theorem notMem_facesIn_Iic_not {k : ℕ} {x z : P} (hk : k < grade ℕ x) (α : Bool)
    (hz : z ∈ P.facesIn (Set.Iic x) k α) : z ∉ P.facesIn (Set.Iic x) k (!α) := fun hz' => by
  have hmax : Maximal (· ∈ LowerSet.Iic x) z :=
    maximal_mem_iff_forall_mem_facesIn.2 fun β => by
      rw [hz.2.1]
      cases α <;> cases β <;> assumption
  have hxz : grade ℕ x ≤ grade ℕ z := grade_mono (hmax.2 (show x ∈ LowerSet.Iic x from le_rfl) hz.1)
  rw [hz.2.1] at hxz
  omega

theorem flowGraph_adj_irrefl (k : ℕ) (x : P) : ¬ (P.flowGraph k).Adj x x :=
  fun ⟨hk, _, _, hz, hz'⟩ => notMem_facesIn_Iic_not hk true hz hz'

theorem not_flowGraph_adj_of_inf_le_boundary {k : ℕ} {V W : LowerSet P}
    (h : V ⊓ W ≤ P.boundary W k false) {x y : P} (hx : x ∈ W) (hy : y ∈ V) :
    ¬ (P.flowGraph k).Adj x y := by
  rintro ⟨hk, -, z, hzx, hzy⟩
  have hzW : z ∈ P.facesIn W k false :=
    mem_facesIn_of_mem_boundary (h ⟨V.lower hzy.1 hy, W.lower hzx.1 hx⟩) hzx.2.1
  exact notMem_facesIn_Iic_not hk true hzx
    (mem_facesIn_of_subset (fun _ hw => W.lower hw hx) hzW hzx.1)

theorem maximalFlowGraph_le (U : LowerSet P) (k : ℕ) : P.maximalFlowGraph U k ≤ P.flowGraph k :=
  fun _ _ h => h.2.2

theorem maximalFlowGraph_adj_of_le {k : ℕ} {V U : LowerSet P} (hVU : V ≤ U) {x y : P} (hx : x ∈ V)
    (hy : y ∈ V) (h : (P.maximalFlowGraph U k).Adj x y) : (P.maximalFlowGraph V k).Adj x y :=
  ⟨⟨h.1.1.mono (fun _ h => hVU h) hx, h.1.2⟩, ⟨h.2.1.1.mono (fun _ h => hVU h) hy, h.2.1.2⟩, h.2.2⟩

theorem maximalFlowGraph_adj_iff_of_subset {k : ℕ} {V U : LowerSet P}
    (h : P.topsAbove V k ⊆ P.topsAbove U k) {x y : P} :
    (P.maximalFlowGraph V k).Adj x y ↔
      x ∈ P.topsAbove V k ∧ y ∈ P.topsAbove V k ∧ (P.maximalFlowGraph U k).Adj x y :=
  ⟨fun hxy => ⟨hxy.1, hxy.2.1, h hxy.1, h hxy.2.1, hxy.2.2⟩,
    fun ⟨hx, hy, hxy⟩ => ⟨hx, hy, hxy.2.2⟩⟩

theorem isAcyclic_maximalFlowGraph_of_subsingleton {k : ℕ} {U : LowerSet P}
    (h : (P.topsAbove U k).Subsingleton) : (P.maximalFlowGraph U k).IsAcyclic :=
  Digraph.IsAcyclic.mono (fun x y hxy => by
    obtain rfl := h hxy.1 hxy.2.1
    exact absurd hxy.2.2 (flowGraph_adj_irrefl k x)) Digraph.isAcyclic_bot

theorem isAcyclic_maximalFlowGraph_of_isAcyclic (U : LowerSet P) {k : ℕ}
    (h : (P.flowGraph k).IsAcyclic) : (P.maximalFlowGraph U k).IsAcyclic :=
  Digraph.IsAcyclic.mono (maximalFlowGraph_le U k) h

theorem flowGraph_adj_iff_exists_mem_faces {n : ℕ} {x y : P}
    (hx : grade ℕ x = n + 1) (hy : grade ℕ y = n + 1) :
    (P.flowGraph n).Adj x y ↔ ∃ z ∈ P.faces true x, z ∈ P.faces false y := by
  constructor
  · rintro ⟨-, -, z, hzx, hzy⟩
    exact ⟨z, (mem_facesIn_Iic_iff_mem_faces hx true).1 hzx,
      (mem_facesIn_Iic_iff_mem_faces hy false).1 hzy⟩
  · rintro ⟨z, hzx, hzy⟩
    exact ⟨by omega, by omega, z, (mem_facesIn_Iic_iff_mem_faces hx true).2 hzx,
      (mem_facesIn_Iic_iff_mem_faces hy false).2 hzy⟩

theorem IsMoleculeIn.subsingleton_maximalFlowGraph_successors {U : LowerSet P} {n : ℕ}
    (hU : IsMoleculeIn P U) (hd : krullDim U = (n + 1 : ℕ)) {x : P}
    (hx : grade ℕ x = n + 1) (ho : (P.faces true x).Subsingleton) :
    {y | (P.maximalFlowGraph U n).Adj x y}.Subsingleton := by
  intro y hy z hz
  have hygrade : grade ℕ y = n + 1 := by
    have ht := hy.2.1
    have heq := P.topsAbove_sub_one_of_krullDim_eq hd (Nat.succ_pos n)
    rw [Nat.add_sub_cancel] at heq
    exact (heq ▸ ht).2
  have hzgrade : grade ℕ z = n + 1 := by
    have ht := hz.2.1
    have heq := P.topsAbove_sub_one_of_krullDim_eq hd (Nat.succ_pos n)
    rw [Nat.add_sub_cancel] at heq
    exact (heq ▸ ht).2
  obtain ⟨a, hax, hay⟩ := (flowGraph_adj_iff_exists_mem_faces hx hygrade).1 hy.2.2
  obtain ⟨b, hbx, hbz⟩ := (flowGraph_adj_iff_exists_mem_faces hx hzgrade).1 hz.2.2
  obtain rfl := ho hax hbx
  exact hU.subsingleton_cofaces_inter (x := a) (by
    rw [hd]
    have := Nat.covBy_iff_add_one_eq.1 (hax.1.grade ℕ)
    exact_mod_cast (by omega : n + 1 ≤ grade ℕ a + 1)) false
    ⟨hay, hy.2.1.1.prop⟩ ⟨hbz, hz.2.1.1.prop⟩

theorem mem_facesIn_of_forall_not_maximalFlowGraph_adj
    {U : LowerSet P} {n : ℕ}
    (hd : krullDim U = (n + 1 : ℕ)) {x o : P} (hx : x ∈ U)
    (hxgrade : grade ℕ x = n + 1) (ho : o ∈ P.faces true x)
    (hsink : ∀ y, ¬ (P.maximalFlowGraph U n).Adj x y) :
    o ∈ P.facesIn U n true := by
  have hograde : grade ℕ o = n := by
    have := Nat.covBy_iff_add_one_eq.1 (ho.1.grade ℕ)
    omega
  refine ⟨U.lower ho.1.le hx, hograde, Set.disjoint_left.2 fun y hoy hyU => ?_⟩
  have hygrade : grade ℕ y = n + 1 := by
    have := Nat.covBy_iff_add_one_eq.1 (hoy.1.grade ℕ)
    omega
  exact hsink y ⟨⟨maximal_mem_of_krullDim_le hx (by rw [hd, hxgrade]), by omega⟩,
    ⟨maximal_mem_of_krullDim_le hyU (by rw [hd, hygrade]), by omega⟩,
    (flowGraph_adj_iff_exists_mem_faces hxgrade hygrade).2 ⟨o, ho, hoy⟩⟩

theorem isAcyclic_maximalFlowGraph_of_isPastingIn {k : ℕ} {V W U : LowerSet P}
    (hp : P.IsPastingIn k V W U) (hV : (P.maximalFlowGraph V k).IsAcyclic)
    (hW : (P.maximalFlowGraph W k).IsAcyclic) : (P.maximalFlowGraph U k).IsAcyclic := by
  have hVU : V ≤ U := hp.sup_eq ▸ le_sup_left
  have hWU : W ≤ U := hp.sup_eq ▸ le_sup_right
  have hmem {x : P} (hx : x ∈ P.topsAbove U k) : x ∈ V ∨ x ∈ W := by
    have hxU := hx.1.prop
    rwa [← hp.sup_eq, LowerSet.mem_sup_iff] at hxU
  have hback {x y : P} (hxy : (P.maximalFlowGraph U k).Adj x y) (hx : x ∈ W) (hy : y ∈ V) :
      False :=
    not_flowGraph_adj_of_inf_le_boundary hp.inf_eq_input.le hx hy hxy.2.2
  have hinV {a b : P} (h : Relation.TransGen (P.maximalFlowGraph U k).Adj a b) (hb : b ∈ V) :
      a ∈ V ∧ Relation.TransGen (P.maximalFlowGraph V k).Adj a b := by
    induction h with
    | single hab =>
      have ha := (hmem hab.1).resolve_right fun ha => hback hab ha hb
      exact ⟨ha, .single (maximalFlowGraph_adj_of_le hVU ha hb hab)⟩
    | tail _ hcb ih =>
      have hc := (hmem hcb.1).resolve_right fun hc => hback hcb hc hb
      obtain ⟨ha, hac⟩ := ih hc
      exact ⟨ha, hac.tail (maximalFlowGraph_adj_of_le hVU hc hb hcb)⟩
  have hinW {a b : P} (h : Relation.TransGen (P.maximalFlowGraph U k).Adj a b) (ha : a ∈ W) :
      b ∈ W ∧ Relation.TransGen (P.maximalFlowGraph W k).Adj a b := by
    induction h with
    | single hab =>
      have hb := (hmem hab.2.1).resolve_left fun hb => hback hab ha hb
      exact ⟨hb, .single (maximalFlowGraph_adj_of_le hWU ha hb hab)⟩
    | tail _ hcb ih =>
      obtain ⟨hc, hac⟩ := ih
      have hb := (hmem hcb.2.1).resolve_left fun hb => hback hcb hc hb
      exact ⟨hb, hac.tail (maximalFlowGraph_adj_of_le hWU hc hb hcb)⟩
  intro v hv
  obtain ⟨w, hvw, -⟩ := Relation.TransGen.head'_iff.1 hv
  rcases hmem hvw.1 with hvV | hvW
  · exact hV v (hinV hv hvV).2
  · exact hW v (hinW hv hvW).2

theorem IsLayering.isAcyclic_maximalFlowGraph {k : ℕ} {U : LowerSet P} {L : List (LowerSet P)}
    (hL : P.IsLayering k U L) : (P.maximalFlowGraph U k).IsAcyclic := by
  have hlayer {i : ℕ} (hi : i < L.length) : (P.maximalFlowGraph (L.getD i ⊥) k).IsAcyclic :=
    isAcyclic_maximalFlowGraph_of_subsingleton fun _ ha _ hb =>
      (hL.existsUnique_top_getD hi).unique ha hb
  have hprefix (i : ℕ) (hi : i < L.length) :
      (P.maximalFlowGraph (prefixUnion L i) k).IsAcyclic := by
    induction i with
    | zero => exact hlayer hi
    | succ i ih =>
      exact isAcyclic_maximalFlowGraph_of_isPastingIn (hL.isPastingIn i hi) (ih (by omega))
        (hlayer hi)
  have hlen : 0 < L.length := List.length_pos_iff.2 hL.ne_nil
  rw [← hL.prefixUnion_eq]
  exact hprefix _ (by omega)

theorem IsLayering.exists_isOrdering_forall₂ {k : ℕ} {U : LowerSet P} {L : List (LowerSet P)}
    (hL : P.IsLayering k U L) :
    ∃ l : List P, P.IsOrdering U k l ∧
      List.Forall₂ (fun t V => Maximal (· ∈ V) t ∧ k < grade ℕ t) l L := by
  have hex : ∀ L' : List (LowerSet P), (∀ V ∈ L', ∃! t : P, Maximal (· ∈ V) t ∧ k < grade ℕ t) →
      ∃ l : List P, List.Forall₂ (fun t V => Maximal (· ∈ V) t ∧ k < grade ℕ t) l L' := by
    intro L' h
    induction L' with
    | nil => exact ⟨[], .nil⟩
    | cons V L' ih =>
      obtain ⟨t, ht, -⟩ := h V List.mem_cons_self
      obtain ⟨l, hl⟩ := ih fun W hW => h W (List.mem_cons_of_mem _ hW)
      exact ⟨t :: l, .cons ht hl⟩
  obtain ⟨l, hl⟩ := hex L hL.existsUnique_top
  obtain ⟨hlen, hR⟩ := List.forall₂_iff_get.1 hl
  have htop (i : ℕ) (hi : i < l.length) :
      Maximal (· ∈ L.getD i ⊥) l[i] ∧ k < grade ℕ l[i] := by
    have := hR i hi (hlen ▸ hi)
    rwa [List.get_eq_getElem, List.get_eq_getElem, ← List.getD_eq_getElem _ ⊥] at this
  refine ⟨l, ⟨fun x => ⟨fun hx => ?_, fun hx => ?_⟩, ?_, ?_, ?_⟩, hl⟩
  · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
    exact ⟨hL.maximal_of_maximal (hlen ▸ hi) (htop i hi).1 (htop i hi).2, (htop i hi).2⟩
  · obtain ⟨i, hi, hxi⟩ := hL.exists_mem_getD hx.1.prop
    have hxt := (hL.existsUnique_top_getD hi).unique
      ⟨hx.1.mono (fun _ h => hL.le hi h) hxi, hx.2⟩ (htop i (hlen ▸ hi))
    exact hxt ▸ List.getElem_mem _
  · refine List.nodup_iff_injective_getElem.2 fun ⟨i, hi⟩ ⟨j, hj⟩ hij => Fin.ext ?_
    have hij' : l[i] = l[j] := hij
    exact hL.eq_of_mem_of_mem (hlen ▸ hi) (hlen ▸ hj) (htop i hi).2 (htop i hi).1.prop
      (hij' ▸ (htop j hj).1.prop)
  · refine List.pairwise_iff_getElem.2 fun i j hi hj hij hadj => ?_
    exact not_flowGraph_adj_of_inf_le_boundary (hL.inf_le_boundary_false hij (hlen ▸ hj))
      (htop j hj).1.prop (htop i hi).1.prop hadj.2.2
  · exact fun a _ h => flowGraph_adj_irrefl k a h.2.2

theorem IsMoleculeIn.isAcyclic_maximalFlowGraph_of_krullDim_eq {U : LowerSet P} {n : ℕ}
    (hU : IsMoleculeIn P U) (hn : krullDim U = ((n + 1 : ℕ) : WithBot ℕ∞)) :
    (P.maximalFlowGraph U n).IsAcyclic := by
  obtain ⟨L, hL⟩ := admitsLayering_pred_krullDim hU hn n.succ_pos
  exact hL.isAcyclic_maximalFlowGraph

theorem IsMoleculeIn.exists_isOrdering_iff {U : LowerSet P} (hU : IsMoleculeIn P U) (k : ℕ) :
    (∃ l, P.IsOrdering U k l) ↔ (P.maximalFlowGraph U k).IsAcyclic := by
  refine ⟨fun ⟨l, hl, hs⟩ => Digraph.isAcyclic_of_isTopologicalSort hs fun a b hab =>
    ⟨(hl a).2 hab.1, (hl b).2 hab.2.1⟩, fun h => ?_⟩
  have hfin : (P.topsAbove U k).Finite := hU.finite.subset fun _ ht => ht.1.prop
  obtain ⟨l, hl, hs⟩ := h.exists_isTopologicalSort hfin.toFinset
  exact ⟨l, fun x => (hl x).trans hfin.mem_toFinset, hs⟩

private theorem image_Iic {Q : OGP.{u}} (f : P ⟶ Q) (x : P) : f '' Set.Iic x = Set.Iic (f x) := by
  rw [← LowerSet.coe_Iic, ← coe_map, map_Iic, LowerSet.coe_Iic]

theorem flowGraph_adj_map_iff {Q : OGP.{u}} (f : P ⟶ Q) [IsInclusion f] (k : ℕ) (x y : P) :
    (Q.flowGraph k).Adj (f x) (f y) ↔ (P.flowGraph k).Adj x y := by
  have himage (z : P) (α : Bool) :
      Q.facesIn (Set.Iic (f z)) k α = f '' P.facesIn (Set.Iic z) k α := by
    rw [image_facesIn, image_Iic]
  simp only [flowGraph_adj, (isMorphism f).grade_eq, himage,
    ← Set.image_inter IsInclusion.injective, Set.image_nonempty]

theorem extendedFlowGraph_adj_map_iff {Q : OGP.{u}} (f : P ⟶ Q) [IsInclusion f] (k : ℕ)
    (a b : P) : (Q.extendedFlowGraph k).Adj (f a) (f b) ↔ (P.extendedFlowGraph k).Adj a b := by
  have hint (z : P) (α : Bool) : Q.interior (Q.boundary (.Iic (f z)) k α) =
      f '' P.interior (P.boundary (.Iic z) k α) := by
    rw [image_interior, map_boundary, map_Iic]
  simp only [extendedFlowGraph_adj, (isMorphism f).grade_eq, hint,
    IsInclusion.injective.mem_set_image]

theorem hasseDiagram_adj_map_iff {Q : OGP.{u}} (f : P ⟶ Q) [IsInclusion f] (x y : P) :
    Q.hasseDiagram.Adj (f y) (f x) ↔ P.hasseDiagram.Adj y x := by
  simp only [hasseDiagram_adj, IsInclusion.mem_faces_iff f]

theorem IsMorphism.isAcyclic {Q : OGP.{v}} {f : P → Q} (hf : IsMorphism f) (hQ : Q.IsAcyclic) :
    P.IsAcyclic := by
  have hadj (y x : P) (h : P.hasseDiagram.Adj y x) : Q.hasseDiagram.Adj (f y) (f x) :=
    h.imp (fun h => (hf.bijOn_faces x false).mapsTo h) fun h => (hf.bijOn_faces y true).mapsTo h
  exact fun v hv => hQ (f v) (hv.lift f hadj)

theorem mem_interior_boundary_of_mem_facesIn {U : LowerSet P} {k : ℕ} {α : Bool} {z : P}
    (hz : z ∈ P.facesIn U k α) : z ∈ P.interior (P.boundary U k α) :=
  mem_interior_of_krullDim_le (mem_boundary_of_mem_facesIn hz le_rfl)
    (by rw [hz.2.1]; exact krullDim_boundary_le U k α)

theorem transGen_extendedFlowGraph_of_transGen_flowGraph {k : ℕ} {x y : P}
    (h : Relation.TransGen (P.flowGraph k).Adj x y) :
    Relation.TransGen (P.extendedFlowGraph k).Adj x y := by
  have step {x y : P} (hxy : (P.flowGraph k).Adj x y) :
      Relation.TransGen (P.extendedFlowGraph k).Adj x y := by
    obtain ⟨hx, hy, z, hzx, hzy⟩ := hxy
    have hz : grade ℕ z ≤ k := hzx.2.1.le
    exact .tail (.single (Or.inr ⟨hx, hz, mem_interior_boundary_of_mem_facesIn hzx⟩))
      (Or.inl ⟨hz, hy, mem_interior_boundary_of_mem_facesIn hzy⟩)
  induction h with
  | single hxy => exact step hxy
  | tail _ hyz ih => exact ih.trans (step hyz)

theorem IsStronglyDimensionwiseAcyclic.isDimensionwiseAcyclic
    (h : P.IsStronglyDimensionwiseAcyclic) : P.IsDimensionwiseAcyclic :=
  fun k v hv => h k v (transGen_extendedFlowGraph_of_transGen_flowGraph hv)

section Decide

section Bound

variable [Fintype P]

private theorem grade_le_gradeBound (x : P) : grade ℕ x ≤ P.gradeBound :=
  Finset.le_sup (f := fun x : P => grade ℕ x) (Finset.mem_univ x)

theorem isDimensionwiseAcyclic_iff_forall_lt_gradeBound :
    P.IsDimensionwiseAcyclic ↔ ∀ k < P.gradeBound, (P.flowGraph k).IsAcyclic := by
  refine ⟨fun h k _ => h k, fun h k => ?_⟩
  by_cases hk : k < P.gradeBound
  · exact h k hk
  · refine Digraph.IsAcyclic.mono (fun x _ hxy => ?_) Digraph.isAcyclic_bot
    have := grade_le_gradeBound x
    exact absurd hxy.1 (by omega)

theorem isStronglyDimensionwiseAcyclic_iff_forall_lt_gradeBound :
    P.IsStronglyDimensionwiseAcyclic ↔ ∀ k < P.gradeBound, (P.extendedFlowGraph k).IsAcyclic := by
  refine ⟨fun h k _ => h k, fun h k => ?_⟩
  by_cases hk : k < P.gradeBound
  · exact h k hk
  · refine Digraph.IsAcyclic.mono (fun x y hxy => ?_) Digraph.isAcyclic_bot
    have := grade_le_gradeBound x
    have := grade_le_gradeBound y
    rcases hxy with ⟨-, h, -⟩ | ⟨h, -, -⟩ <;> exact absurd h (by omega)

end Bound

variable [Fintype P] [DecidableEq P] [DecidableLE P]

instance decidableRelHasseDiagram : DecidableRel P.hasseDiagram.Adj := fun y x =>
  inferInstanceAs (Decidable (y ∈ P.faces false x ∨ x ∈ P.faces true y))

instance decidableRelFlowGraph (k : ℕ) : DecidableRel (P.flowGraph k).Adj := fun x y =>
  decidable_of_iff (k < grade ℕ x ∧ k < grade ℕ y ∧
      ∃ z, z ∈ P.facesIn (Set.Iic x) k true ∧ z ∈ P.facesIn (Set.Iic y) k false) Iff.rfl

instance decidableRelMaximalFlowGraph (U : LowerSet P) [DecidablePred (· ∈ U)] (k : ℕ) :
    DecidableRel (P.maximalFlowGraph U k).Adj := fun x y =>
  decidable_of_iff ((Maximal (· ∈ U) x ∧ k < grade ℕ x) ∧ (Maximal (· ∈ U) y ∧ k < grade ℕ y) ∧
      (P.flowGraph k).Adj x y) Iff.rfl

instance decidableRelExtendedFlowGraph (k : ℕ) : DecidableRel (P.extendedFlowGraph k).Adj :=
  fun a b => decidable_of_iff
    ((grade ℕ a ≤ k ∧ k < grade ℕ b ∧ a ∈ P.interior (P.boundary (.Iic b) k false)) ∨
      (k < grade ℕ a ∧ grade ℕ b ≤ k ∧ b ∈ P.interior (P.boundary (.Iic a) k true))) Iff.rfl

instance decidableIsAcyclic : Decidable P.IsAcyclic :=
  inferInstanceAs (Decidable P.hasseDiagram.IsAcyclic)

instance decidableIsDimensionwiseAcyclic : Decidable P.IsDimensionwiseAcyclic :=
  decidable_of_iff _ isDimensionwiseAcyclic_iff_forall_lt_gradeBound.symm

instance decidableIsStronglyDimensionwiseAcyclic : Decidable P.IsStronglyDimensionwiseAcyclic :=
  decidable_of_iff _ isStronglyDimensionwiseAcyclic_iff_forall_lt_gradeBound.symm

end Decide

end Atoms.Molecule.OGP
