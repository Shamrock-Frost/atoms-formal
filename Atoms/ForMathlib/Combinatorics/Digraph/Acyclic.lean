import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.Fintype.Card
import Mathlib.Order.WellFoundedSet

namespace Digraph

variable {V : Type*} (G : Digraph V)

def IsAcyclic : Prop := ∀ v, ¬ Relation.TransGen G.Adj v v

def IsTopologicalSort (l : List V) : Prop :=
  l.Nodup ∧ l.Pairwise (fun a b => ¬ G.Adj b a) ∧ ∀ a ∈ l, ¬ G.Adj a a

variable {G}

theorem IsAcyclic.mono {H : Digraph V} (h : G ≤ H) (hH : H.IsAcyclic) : G.IsAcyclic :=
  fun v hv => hH v (Relation.TransGen.mono (fun _ _ hab => h hab) _ _ hv)

@[simp] theorem isAcyclic_bot : (⊥ : Digraph V).IsAcyclic :=
  fun _ h => by
    obtain ⟨_, h, -⟩ := Relation.TransGen.head'_iff.1 h
    exact h

theorem IsAcyclic.exists_forall_not_adj (hG : G.IsAcyclic) {s : Set V} (hs : s.Finite)
    (hne : s.Nonempty) : ∃ v ∈ s, ∀ u ∈ s, ¬ G.Adj u v := by
  have : IsStrictOrder V (Relation.TransGen G.Adj) :=
    { irrefl := hG
      trans := fun _ _ _ => Relation.TransGen.trans }
  obtain ⟨v, hv, hmin⟩ := (Set.wellFoundedOn_iff.1
    (hs.wellFoundedOn (r := Relation.TransGen G.Adj))).has_min s hne
  exact ⟨v, hv, fun u hu huv => hmin u hu ⟨.single huv, hu, hv⟩⟩

theorem IsAcyclic.exists_forall_not_adj_right (hG : G.IsAcyclic) {s : Set V}
    (hs : s.Finite) (hne : s.Nonempty) : ∃ v ∈ s, ∀ u ∈ s, ¬ G.Adj v u := by
  let H : Digraph V := ⟨fun a b => G.Adj b a⟩
  have hH : H.IsAcyclic := fun v hv => hG v (Relation.transGen_swap.1 hv)
  exact hH.exists_forall_not_adj hs hne

theorem existsUnique_isChain_cons_of_reflTransGen {x r : V}
    (hsink : ∀ y, ¬ G.Adj r y) (hdet : ∀ a, {b | G.Adj a b}.Subsingleton)
    (hreach : Relation.ReflTransGen G.Adj x r) :
    ∃! l : List V, (x :: l).IsChain G.Adj ∧ (x :: l).getLast (by simp) = r := by
  obtain ⟨l, hl, hr⟩ := List.exists_isChain_cons_of_relationReflTransGen hreach
  refine ⟨l, ⟨hl, hr⟩, fun m hm => ?_⟩
  have unique : ∀ (l m : List V) (a : V),
      (a :: l).IsChain G.Adj → (a :: l).getLast (by simp) = r →
      (a :: m).IsChain G.Adj → (a :: m).getLast (by simp) = r → l = m := by
    intro l
    induction l with
    | nil =>
      intro m a ha har hm hmr
      cases m with
      | nil => rfl
      | cons b m =>
        have hab := (List.isChain_cons_cons.1 hm).1
        exact (hsink b (har ▸ hab)).elim
    | cons b l ih =>
      intro m a ha har hm hmr
      have hab := (List.isChain_cons_cons.1 ha).1
      cases m with
      | nil => exact (hsink b (hmr ▸ hab)).elim
      | cons c m =>
        obtain rfl := hdet a hab (List.isChain_cons_cons.1 hm).1
        exact congrArg (List.cons b) (ih m b (List.isChain_cons_cons.1 ha).2 har
          (List.isChain_cons_cons.1 hm).2 hmr)
  exact unique m l x hm.1 hm.2 hl hr

theorem IsAcyclic.exists_isTopologicalSort (hG : G.IsAcyclic) (s : Finset V) :
    ∃ l : List V, (∀ v, v ∈ l ↔ v ∈ s) ∧ G.IsTopologicalSort l := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hne
    · exact ⟨[], by simp, List.nodup_nil, List.Pairwise.nil, by simp⟩
    obtain ⟨v, hv, hsrc⟩ := hG.exists_forall_not_adj s.finite_toSet (by exact_mod_cast hne)
    obtain ⟨l, hl, hnd, hpw, hloop⟩ := ih (s.erase v) (Finset.erase_ssubset hv)
    refine ⟨v :: l, fun w => ?_, ?_, ?_, ?_⟩
    · rw [List.mem_cons, hl, Finset.mem_erase]
      by_cases hw : w = v
      · simp only [hw, true_or, true_iff]
        exact hv
      · simp only [hw, false_or, ne_eq, not_false_eq_true, true_and]
    · exact List.nodup_cons.2 ⟨fun h => by simpa using (hl v).1 h, hnd⟩
    · exact List.pairwise_cons.2
        ⟨fun b hb => hsrc b (Finset.mem_of_mem_erase ((hl b).1 hb)), hpw⟩
    · rintro a (_ | ⟨_, ha⟩)
      · exact hsrc v hv
      · exact hloop a ha

private theorem idxOf_lt_idxOf_of_adj [DecidableEq V] {l : List V} (hl : G.IsTopologicalSort l)
    {a b : V} (ha : a ∈ l) (hb : b ∈ l) (hab : G.Adj a b) : l.idxOf a < l.idxOf b := by
  obtain ⟨-, hpw, hloop⟩ := hl
  have hia := List.idxOf_lt_length_of_mem ha
  have hib := List.idxOf_lt_length_of_mem hb
  rcases lt_trichotomy (l.idxOf a) (l.idxOf b) with h | h | h
  · exact h
  · have : a = b := by
      rw [← List.getElem_idxOf hia, ← List.getElem_idxOf hib]
      simp only [h]
    exact absurd (this ▸ hab) (hloop b hb)
  · have hba := List.pairwise_iff_getElem.1 hpw _ _ hib hia h
    rw [List.getElem_idxOf, List.getElem_idxOf] at hba
    exact absurd hab hba

theorem isAcyclic_of_isTopologicalSort {l : List V} (hl : G.IsTopologicalSort l)
    (hG : ∀ a b, G.Adj a b → a ∈ l ∧ b ∈ l) : G.IsAcyclic := by
  classical
  have key : ∀ {a b}, Relation.TransGen G.Adj a b → l.idxOf a < l.idxOf b := by
    intro a b h
    induction h with
    | single hab => exact idxOf_lt_idxOf_of_adj hl (hG _ _ hab).1 (hG _ _ hab).2 hab
    | tail _ hbc ih => exact ih.trans (idxOf_lt_idxOf_of_adj hl (hG _ _ hbc).1 (hG _ _ hbc).2 hbc)
  exact fun v hv => lt_irrefl _ (key hv)

section Restrict

variable (G) in
def restrict (s : Set V) : Digraph V where
  Adj a b := a ∈ s ∧ b ∈ s ∧ G.Adj a b

@[simp] theorem restrict_adj {s : Set V} {a b : V} :
    (G.restrict s).Adj a b ↔ a ∈ s ∧ b ∈ s ∧ G.Adj a b :=
  Iff.rfl

theorem restrict_le (s : Set V) : G.restrict s ≤ G :=
  fun _ _ h => h.2.2

@[simp] theorem restrict_univ : G.restrict Set.univ = G := by
  ext a b
  simp

theorem restrict_mono {s t : Set V} (h : s ⊆ t) : G.restrict s ≤ G.restrict t :=
  fun _ _ hab => ⟨h hab.1, h hab.2.1, hab.2.2⟩

instance [DecidableRel G.Adj] {s : Set V} [DecidablePred (· ∈ s)] :
    DecidableRel (G.restrict s).Adj :=
  fun a b => decidable_of_iff (a ∈ s ∧ b ∈ s ∧ G.Adj a b) Iff.rfl

end Restrict

section Decide

variable (G) [Fintype V] [DecidableRel G.Adj]

private def peel (S : Finset V) : Finset V :=
  S.filter fun v => ∃ u ∈ S, G.Adj u v

variable {G}

omit [Fintype V] in
private theorem mem_peel {S : Finset V} {v : V} :
    v ∈ peel G S ↔ v ∈ S ∧ ∃ u ∈ S, G.Adj u v :=
  Finset.mem_filter

private theorem mem_peel_iterate {v : V} (hv : Relation.TransGen G.Adj v v) (n : ℕ) :
    v ∈ (peel G)^[n] Finset.univ := by
  induction n generalizing v with
  | zero => exact Finset.mem_univ v
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    obtain ⟨u, hvu, huv⟩ := Relation.TransGen.tail'_iff.1 hv
    have hu : Relation.TransGen G.Adj u u := Relation.TransGen.head' huv hvu
    exact mem_peel.2 ⟨ih hv, u, ih hu, huv⟩

private theorem card_peel_iterate_le (hG : G.IsAcyclic) (n : ℕ) :
    ((peel G)^[n] Finset.univ).card ≤ Fintype.card V - n := by
  induction n with
  | zero => exact Finset.card_le_univ _
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    set S := (peel G)^[n] Finset.univ
    rcases S.eq_empty_or_nonempty with hS | hS
    · have : peel G S = ∅ := Finset.eq_empty_of_forall_notMem fun v hv => by
        simpa [hS] using (mem_peel.1 hv).1
      simp only [this, Finset.card_empty, Nat.zero_le]
    obtain ⟨v, hv, hsrc⟩ := hG.exists_forall_not_adj S.finite_toSet (by exact_mod_cast hS)
    have hlt : (peel G S).card < S.card := Finset.card_lt_card
      ⟨Finset.filter_subset _ _, fun h => by
        obtain ⟨u, hu, huv⟩ := (mem_peel.1 (h hv)).2
        exact hsrc u hu huv⟩
    omega

variable (G)

private theorem isAcyclic_iff_peel_iterate :
    G.IsAcyclic ↔ ∀ v ∈ (peel G)^[Fintype.card V] Finset.univ, False := by
  refine ⟨fun hG v hv => ?_, fun h v hv => h v (mem_peel_iterate hv _)⟩
  have := card_peel_iterate_le hG (Fintype.card V)
  rw [Nat.sub_self, Nat.le_zero, Finset.card_eq_zero] at this
  simp [this] at hv

instance decidableIsAcyclic : Decidable G.IsAcyclic :=
  decidable_of_iff _ (isAcyclic_iff_peel_iterate G).symm

end Decide

end Digraph
