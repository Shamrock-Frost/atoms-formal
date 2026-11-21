import Atoms.ForMathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Atoms.ForMathlib.Logic.Relation
import Atoms.ForMathlib.Order.Grade
import Mathlib.Order.UpperLower.Fibration
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.UpperLowerSetTopology

open Set

namespace Topology.IsUpperSet

variable {α β : Type*} [Preorder α] [TopologicalSpace α] [Topology.IsUpperSet α]
  [Preorder β] [TopologicalSpace β] [Topology.IsUpperSet β] {f : α → β}

instance instSubtype (s : Set α) : Topology.IsUpperSet s := by
  refine ⟨TopologicalSpace.ext (funext fun V => propext ?_)⟩
  change IsOpen V ↔ IsUpperSet V
  rw [isOpen_induced_iff]
  constructor
  · rintro ⟨t, ht, rfl⟩ a b hab ha
    exact isOpen_iff_isUpperSet.1 ht hab ha
  · intro hV
    refine ⟨upperClosure (Subtype.val '' V), isOpen_iff_isUpperSet.2 (upperClosure _).upper, ?_⟩
    ext a
    simp only [mem_preimage, SetLike.mem_coe, mem_upperClosure, mem_image]
    constructor
    · rintro ⟨_, ⟨b, hb, rfl⟩, hba⟩
      exact hV hba hb
    · exact fun ha => ⟨a, ⟨a, ha, rfl⟩, le_rfl⟩

theorem isClosedMap_iff_fibration :
    IsClosedMap f ↔ Relation.Fibration (· ≤ ·) (· ≤ ·) f := by
  rw [Relation.fibration_iff_isLowerSet_image]
  simp only [IsClosedMap, isClosed_iff_isLower]

instance decidableIsClosedMap [Fintype α] [Fintype β] [DecidableLE α] [DecidableLE β]
    [DecidableEq β] : Decidable (IsClosedMap f) :=
  decidable_of_iff _ isClosedMap_iff_fibration.symm

theorem isPreconnected_iff_reflTransGen {s : Set α} :
    IsPreconnected s ↔ ∀ a ∈ s, ∀ b ∈ s,
      Relation.ReflTransGen (fun x y => x ∈ s ∧ y ∈ s ∧ (x ≤ y ∨ y ≤ x)) a b := by
  refine ⟨fun h a ha b hb => ?_, fun h => ?_⟩
  · let Z := {c | Relation.ReflTransGen (fun x y => x ∈ s ∧ y ∈ s ∧ (x ≤ y ∨ y ≤ x)) a c}
    have hu : IsOpen (upperClosure (s ∩ Z) : Set α) :=
      isOpen_iff_isUpperSet.2 (upperClosure _).upper
    have hv : IsOpen (upperClosure (s \ Z) : Set α) :=
      isOpen_iff_isUpperSet.2 (upperClosure _).upper
    have hcov : s ⊆ upperClosure (s ∩ Z) ∪ upperClosure (s \ Z) := fun x hx => by
      by_cases hxZ : x ∈ Z
      · exact Or.inl (subset_upperClosure ⟨hx, hxZ⟩)
      · exact Or.inr (subset_upperClosure ⟨hx, hxZ⟩)
    have hdisj : s ∩ ((upperClosure (s ∩ Z) : Set α) ∩ upperClosure (s \ Z)) = ∅ := by
      refine eq_empty_of_forall_notMem fun x ⟨hx, hxu, hxv⟩ => ?_
      obtain ⟨z, ⟨hzs, hzZ⟩, hzx⟩ := mem_upperClosure.1 hxu
      obtain ⟨w, ⟨hws, hwZ⟩, hwx⟩ := mem_upperClosure.1 hxv
      exact hwZ ((hzZ.tail ⟨hzs, hx, Or.inl hzx⟩).tail ⟨hx, hws, Or.inr hwx⟩)
    rcases isPreconnected_iff_subset_of_disjoint.1 h _ _ hu hv hcov hdisj with hsu | hsv
    · obtain ⟨z, ⟨hzs, hzZ⟩, hzb⟩ := mem_upperClosure.1 (hsu hb)
      exact hzZ.tail ⟨hzs, hb, Or.inl hzb⟩
    · obtain ⟨w, ⟨hws, hwZ⟩, hwa⟩ := mem_upperClosure.1 (hsv ha)
      exact absurd (Relation.ReflTransGen.single ⟨ha, hws, Or.inr hwa⟩) hwZ
  · rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · exact isPreconnected_empty
    have hpair {c d : α} (hcd : c ≤ d) : IsPreconnected ({c, d} : Set α) := by
      refine isPreconnected_singleton.subset_closure (s := {d}) (by simp) ?_
      rw [closure_singleton]
      rintro x (rfl | rfl)
      exacts [hcd, le_rfl]
    have key (c : α)
        (hc : Relation.ReflTransGen (fun x y => x ∈ s ∧ y ∈ s ∧ (x ≤ y ∨ y ≤ x)) a c) :
        ∃ t ⊆ s, a ∈ t ∧ c ∈ t ∧ IsPreconnected t := by
      induction hc with
      | refl => exact ⟨{a}, singleton_subset_iff.2 ha, rfl, rfl, isPreconnected_singleton⟩
      | @tail c d _ hcd ih =>
        obtain ⟨t, hts, hat, hct, ht⟩ := ih
        have hp : IsPreconnected ({c, d} : Set α) := by
          rcases hcd.2.2 with hle | hle
          · exact hpair hle
          · rw [pair_comm]
            exact hpair hle
        refine ⟨t ∪ {c, d}, union_subset hts (insert_subset hcd.1 (singleton_subset_iff.2
          hcd.2.1)), Or.inl hat, Or.inr (Or.inr rfl), ht.union c hct (Or.inl rfl) hp⟩
    exact isPreconnected_of_forall a fun b hb => key b (h a ha b hb)

theorem isPreconnected_of_isLeast {s : Set α} {a : α} (h : IsLeast s a) : IsPreconnected s :=
  isPreconnected_iff_reflTransGen.2 fun _ hb _ hc =>
    (Relation.ReflTransGen.single ⟨hb, h.1, Or.inr (h.2 hb)⟩).trans
      (Relation.ReflTransGen.single ⟨h.1, hc, Or.inl (h.2 hc)⟩)

theorem isPreconnected_of_isGreatest {s : Set α} {a : α} (h : IsGreatest s a) : IsPreconnected s :=
  isPreconnected_iff_reflTransGen.2 fun _ hb _ hc =>
    (Relation.ReflTransGen.single ⟨hb, h.1, Or.inl (h.2 hb)⟩).trans
      (Relation.ReflTransGen.single ⟨h.1, hc, Or.inr (h.2 hc)⟩)

theorem subsingleton_of_isPreconnected_of_grade_eq {α : Type*} [PartialOrder α]
    [TopologicalSpace α] [Topology.IsUpperSet α] [GradeOrder ℕ α] {s : Set α} {n : ℕ}
    (h : IsPreconnected s) (hs : ∀ x ∈ s, grade ℕ x = n) : s.Subsingleton := fun a ha b hb => by
  have hc := isPreconnected_iff_reflTransGen.1 h a ha b hb
  clear hb
  induction hc with
  | refl => rfl
  | tail _ hbc ih =>
    refine ih.trans ?_
    rcases hbc.2.2 with hle | hle
    · exact GradeOrder.eq_of_le_of_grade_le hle (by rw [hs _ hbc.1, hs _ hbc.2.1])
    · exact (GradeOrder.eq_of_le_of_grade_le hle (by rw [hs _ hbc.1, hs _ hbc.2.1])).symm

instance decidableIsPreconnected [Fintype α] [DecidableEq α] [DecidableLE α] (s : Set α)
    [DecidablePred (· ∈ s)] : Decidable (IsPreconnected s) :=
  haveI : Std.Symm fun x y : α => x ∈ s ∧ y ∈ s ∧ (x ≤ y ∨ y ≤ x) :=
    ⟨fun _ _ h => ⟨h.2.1, h.1, h.2.2.symm⟩⟩
  decidable_of_iff _ isPreconnected_iff_reflTransGen.symm

instance decidableIsConnected [Fintype α] [DecidableEq α] [DecidableLE α] (s : Set α)
    [DecidablePred (· ∈ s)] : Decidable (IsConnected s) :=
  inferInstanceAs (Decidable ((∃ x, x ∈ s) ∧ IsPreconnected s))

end Topology.IsUpperSet

namespace Set

variable {α β γ : Type*} [Preorder α] [TopologicalSpace α] [Preorder β]

def FinalOn (f : α → β) (s : Set α) (t : Set β) : Prop :=
  MapsTo f s t ∧ ∀ y ∈ t, IsConnected (s ∩ f ⁻¹' Ici y)

variable {f : α → β} {s : Set α} {t : Set β}

theorem FinalOn.surjOn (hf : FinalOn f s t) (hfib : Relation.Fibration (· ≤ ·) (· ≤ ·) f)
    (hs : IsLowerSet s) : SurjOn f s t := fun y hy => by
  obtain ⟨x, hxs, hyx⟩ := (hf.2 y hy).nonempty
  obtain ⟨x', hx'x, rfl⟩ := hfib hyx
  exact ⟨x', hs hx'x hxs, rfl⟩

omit [Preorder α] in
theorem FinalOn.of_comp [Preorder γ] {g : β ↪o γ} (h : FinalOn (g ∘ f) s (g '' t)) :
    FinalOn f s t := by
  refine ⟨fun x hx => g.injective.mem_set_image.1 (h.1 hx), fun y hy => ?_⟩
  have he : (g ∘ f) ⁻¹' Ici (g y) = f ⁻¹' Ici y := by
    ext x
    simp
  rw [← he]
  exact h.2 (g y) (mem_image_of_mem g hy)

omit [Preorder α] in
theorem finalOn_singleton (f : α → β) (a : α) : FinalOn f {a} {f a} :=
  ⟨mapsTo_singleton.2 rfl, fun y hy => by
    rw [mem_singleton_iff.1 hy, inter_eq_left.2 fun x hx => by
      rw [mem_singleton_iff.1 hx]
      exact le_rfl]
    exact isConnected_singleton⟩

omit [Preorder α] in
theorem FinalOn.congr {g : α → β} (hf : FinalOn f s t) (h : EqOn f g s) : FinalOn g s t :=
  ⟨fun _ hx => h hx ▸ hf.1 hx, fun y hy => h.inter_preimage_eq (Ici y) ▸ hf.2 y hy⟩

variable [Topology.IsUpperSet α]

theorem finalOn_id (s : Set α) : FinalOn id s s :=
  ⟨mapsTo_id s, fun y hy => ⟨⟨y, hy, le_refl y⟩,
    Topology.IsUpperSet.isPreconnected_of_isLeast ⟨⟨hy, le_refl y⟩, fun _ h => h.2⟩⟩⟩

theorem finalOn_Iic (hf : Monotone f) (x : α) : FinalOn f (Iic x) (Iic (f x)) :=
  ⟨fun _ hy => hf hy, fun _ hy => ⟨⟨x, le_refl x, hy⟩,
    Topology.IsUpperSet.isPreconnected_of_isGreatest ⟨⟨le_refl x, hy⟩, fun _ h => h.1⟩⟩⟩

instance decidableFinalOn [Fintype α] [DecidableEq α] [DecidableLE α] [Fintype β] [DecidableLE β]
    (f : α → β) (s : Set α) (t : Set β) [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)] :
    Decidable (FinalOn f s t) :=
  haveI (y : β) : DecidablePred (· ∈ s ∩ f ⁻¹' Ici y) := fun x =>
    inferInstanceAs (Decidable (x ∈ s ∧ y ≤ f x))
  inferInstanceAs (Decidable ((∀ x, x ∈ s → f x ∈ t) ∧ ∀ y, y ∈ t → IsConnected (s ∩ f ⁻¹' Ici y)))

theorem FinalOn.comp [TopologicalSpace β] [Topology.IsUpperSet β] [Preorder γ] {g : β → γ}
    {u : Set γ} (hg : FinalOn g t u) (hf : FinalOn f s t) (hgm : Monotone g) :
    FinalOn (g ∘ f) s u := by
  refine ⟨hg.1.comp hf.1, fun z hz => ?_⟩
  let A := s ∩ (g ∘ f) ⁻¹' Ici z
  have hfib (c : β) (hc : c ∈ t ∩ g ⁻¹' Ici z) : s ∩ f ⁻¹' Ici c ⊆ A :=
    fun w hw => ⟨hw.1, le_trans hc.2 (hgm hw.2)⟩
  obtain ⟨c₀, hc₀⟩ := (hg.2 z hz).nonempty
  obtain ⟨x₀, hx₀⟩ := (hf.2 c₀ hc₀.1).nonempty
  refine ⟨⟨x₀, hfib c₀ hc₀ hx₀⟩,
    Topology.IsUpperSet.isPreconnected_iff_reflTransGen.2 fun a ha b hb => ?_⟩
  have hfa : f a ∈ t ∩ g ⁻¹' Ici z := ⟨hf.1 ha.1, ha.2⟩
  have hfb : f b ∈ t ∩ g ⁻¹' Ici z := ⟨hf.1 hb.1, hb.2⟩
  have hjoin (c : β) (hc : c ∈ t ∩ g ⁻¹' Ici z) {x x' : α} (hx : x ∈ s ∩ f ⁻¹' Ici c)
      (hx' : x' ∈ s ∩ f ⁻¹' Ici c) :
      Relation.ReflTransGen (fun x y => x ∈ A ∧ y ∈ A ∧ (x ≤ y ∨ y ≤ x)) x x' :=
    Relation.ReflTransGen.mono (fun _ _ h => ⟨hfib c hc h.1, hfib c hc h.2.1, h.2.2⟩) x x'
      (Topology.IsUpperSet.isPreconnected_iff_reflTransGen.1 (hf.2 c hc.1).2 x hx x' hx')
  have key (c : β) (h : Relation.ReflTransGen
      (fun x y => x ∈ t ∩ g ⁻¹' Ici z ∧ y ∈ t ∩ g ⁻¹' Ici z ∧ (x ≤ y ∨ y ≤ x)) (f a) c) :
      ∃ x ∈ s, c ≤ f x ∧
        Relation.ReflTransGen (fun x y => x ∈ A ∧ y ∈ A ∧ (x ≤ y ∨ y ≤ x)) a x := by
    induction h with
    | refl => exact ⟨a, ha.1, le_rfl, Relation.ReflTransGen.refl⟩
    | @tail c d _ hcd ih =>
      obtain ⟨x, hxs, hcx, hax⟩ := ih
      obtain ⟨x', hx'⟩ := (hf.2 d hcd.2.1.1).nonempty
      refine ⟨x', hx'.1, hx'.2, hax.trans ?_⟩
      rcases hcd.2.2 with hle | hle
      · exact hjoin c hcd.1 ⟨hxs, hcx⟩ ⟨hx'.1, le_trans hle hx'.2⟩
      · exact hjoin d hcd.2.1 ⟨hxs, le_trans hle hcx⟩ hx'
  obtain ⟨x, hxs, hbx, hax⟩ := key (f b)
    (Topology.IsUpperSet.isPreconnected_iff_reflTransGen.1 (hg.2 z hz).2 _ hfa _ hfb)
  exact hax.trans (hjoin (f b) hfb ⟨hxs, hbx⟩ ⟨hb.1, le_rfl⟩)

end Set
