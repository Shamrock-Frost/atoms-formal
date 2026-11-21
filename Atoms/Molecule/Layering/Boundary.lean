import Atoms.Molecule.Layering.Existence
import Atoms.Molecule.Interior

universe u

open Order Set

namespace Atoms.Molecule.OGP

variable {P : OGP.{u}} {k : ℕ} {U : LowerSet P} {x : P} {L : List (LowerSet P)}

theorem IsLayering.mem_boundary_prefixUnion_iff (h : IsLayering P k U L) {n : ℕ} (hkn : k < n)
    (β : Bool) {m : ℕ} (hm : m < L.length) {y : P} :
    y ∈ P.boundary (prefixUnion L m) n β ↔ ∃ j ≤ m, y ∈ P.boundary (L.getD j ⊥) n β := by
  induction m with
  | zero => simp only [prefixUnion_zero, Nat.le_zero, exists_eq_left]
  | succ m ih =>
    have hp := (h.isPastingIn m hm).boundary_of_lt
      (h.isMoleculeIn_prefixUnion (i := m) (by omega)).isGlobular
      (h.isMoleculeIn_getD hm).isGlobular hkn β
    rw [← hp.sup_eq, LowerSet.mem_sup_iff, ih (by omega)]
    simp only [← Nat.lt_add_one_iff, Nat.exists_lt_succ_right]

theorem IsLayering.mem_boundary_iff (h : IsLayering P k U L) {n : ℕ} (hkn : k < n) (β : Bool)
    {y : P} :
    y ∈ P.boundary U n β ↔ ∃ j, j < L.length ∧ y ∈ P.boundary (L.getD j ⊥) n β := by
  have hpos : 0 < L.length := List.length_pos_iff.2 h.ne_nil
  rw [← h.prefixUnion_eq, h.mem_boundary_prefixUnion_iff hkn β (by omega)]
  exact ⟨fun ⟨j, hj, hy⟩ => ⟨j, by omega, hy⟩, fun ⟨j, hj, hy⟩ => ⟨j, by omega, hy⟩⟩

theorem IsLayering.isSubmoleculeOf_boundary_getD_prefixUnion (h : IsLayering P k U L) {n : ℕ}
    (hkn : k < n) (β : Bool) {i m : ℕ} (him : i ≤ m) (hm : m < L.length) :
    P.IsSubmoleculeOf (P.boundary (L.getD i ⊥) n β) (P.boundary (prefixUnion L m) n β) := by
  induction m with
  | zero =>
    obtain rfl : i = 0 := by omega
    exact .refl ((h.isMoleculeIn_getD hm).boundary n β)
  | succ m ih =>
    have hp := h.isPastingIn m hm
    have hA := h.isMoleculeIn_prefixUnion (i := m) (by omega)
    have hY := h.isMoleculeIn_getD hm
    rcases eq_or_lt_of_le him with rfl | hlt
    · exact hp.boundary_isSubmoleculeOf_boundary true hA hY (Or.inl hkn)
    · exact (ih (by omega) (by omega)).trans
        (hp.boundary_isSubmoleculeOf_boundary false hY hA (Or.inl hkn))

theorem IsLayering.isSubmoleculeOf_boundary_getD (h : IsLayering P k U L) {n : ℕ}
    (hkn : k < n) (β : Bool) {i : ℕ} (hi : i < L.length) :
    P.IsSubmoleculeOf (P.boundary (L.getD i ⊥) n β) (P.boundary U n β) := by
  have := h.isSubmoleculeOf_boundary_getD_prefixUnion hkn β (i := i) (m := L.length - 1)
    (by omega) (by omega)
  rwa [h.prefixUnion_eq] at this

theorem isSubmoleculeOf_and_boundary_eq_of_topsAbove_eq (hU : IsMoleculeIn P U) :
    ∀ (k : ℕ) (x : P), P.topsAbove U k = {x} → ∀ α : Bool,
      P.IsSubmoleculeOf (P.boundary (.Iic x) k α) (P.boundary U k α) ∧
        (P.boundary U k α : Set P) =
          ((P.boundary U k (!α) : Set P) \ P.interior (P.boundary (.Iic x) k (!α))) ∪
            P.boundary (.Iic x) k α := by
  refine IsMoleculeIn.layeringDim_induction (motive := fun U => ∀ (k : ℕ) (x : P),
      P.topsAbove U k = {x} → ∀ α : Bool,
      P.IsSubmoleculeOf (P.boundary (.Iic x) k α) (P.boundary U k α) ∧
        (P.boundary U k α : Set P) =
          ((P.boundary U k (!α) : Set P) \ P.interior (P.boundary (.Iic x) k (!α))) ∪
            P.boundary (.Iic x) k α) ?_ ?_ hU
  · intro U hA k x hx α
    obtain ⟨hxM, -⟩ : x ∈ P.topsAbove U k := hx ▸ mem_singleton x
    obtain ⟨hUm, t, rfl⟩ := hA
    obtain rfl : t = x := le_antisymm (hxM.2 (LowerSet.mem_Iic_iff.2 le_rfl) hxM.prop) hxM.prop
    have hsub := hUm.isGlobular.properBoundary_boundary_le_boundary k α (!α)
    refine ⟨.refl (hUm.boundary k α), ?_⟩
    rw [diff_interior]
    exact (Set.union_eq_right.2 hsub).symm
  · intro k' U L _ hL hd ih k x hx α
    obtain ⟨hxM, hkx⟩ : x ∈ P.topsAbove U k := hx ▸ mem_singleton x
    have hk' : k' < k := by
      have : P.layeringDim U hL.isMoleculeIn_self ≤ k :=
        (layeringDim_le_iff hL.isMoleculeIn_self).2 (by rw [hx]; exact subsingleton_singleton)
      omega
    obtain ⟨i, hi, hxi⟩ := hL.exists_mem_getD hxM.prop
    have hxMi : Maximal (· ∈ L.getD i ⊥) x := hxM.mono (hL.le hi) hxi
    have hti : P.topsAbove (L.getD i ⊥) k = {x} :=
      Set.eq_singleton_iff_unique_mem.2 ⟨⟨hxMi, hkx⟩, fun y ⟨hyM, hky⟩ =>
        (Set.ext_iff.1 hx y).1 ⟨hL.maximal_of_maximal hi hyM (by omega), hky⟩⟩
    have hLi := hL.isMoleculeIn_getD hi
    obtain ⟨ih1, ih2⟩ := ih _ (getD_mem_of_lt_length hi) k x hti α
    have hdj : ∀ j, j < L.length → j ≠ i → krullDim (L.getD j ⊥) ≤ k := by
      intro j hj hji
      refine krullDim_le_coe_iff.2 fun ⟨y, hy⟩ => ?_
      obtain ⟨z, hyz, hzM⟩ := (hL.isMoleculeIn_getD hj).exists_le_maximal hy
      refine (grade_mono hyz).trans (not_lt.1 fun hkz => hji ?_)
      obtain rfl : z = x :=
        (Set.ext_iff.1 hx z).1 ⟨hL.maximal_of_maximal hj hzM (by omega), hkz⟩
      exact hL.eq_of_mem_of_mem hj hi (by omega) hzM.prop hxi
    have hmem : ∀ (β : Bool) (y : P), y ∈ P.boundary U k β ↔
        y ∈ P.boundary (L.getD i ⊥) k β ∨ ∃ j, j < L.length ∧ j ≠ i ∧ y ∈ L.getD j ⊥ := by
      intro β y
      rw [hL.mem_boundary_iff hk' β]
      constructor
      · rintro ⟨j, hj, hy⟩
        by_cases hji : j = i
        · exact Or.inl (hji ▸ hy)
        · refine Or.inr ⟨j, hj, hji, ?_⟩
          rwa [boundary_eq_self (hdj j hj hji)] at hy
      · rintro (hy | ⟨j, hj, hji, hy⟩)
        · exact ⟨i, hi, hy⟩
        · exact ⟨j, hj, by rwa [boundary_eq_self (hdj j hj hji)]⟩
    refine ⟨ih1.trans (hL.isSubmoleculeOf_boundary_getD hk' α hi), ?_⟩
    have hxs := hLi.Iic_isSubmoleculeOf hxi
    have hcm := (hLi.isAtomIn_Iic hxi).isMoleculeIn
    have hg := hcm.isGlobular
    have key : ∀ y, (∃ j, j < L.length ∧ j ≠ i ∧ y ∈ L.getD j ⊥) →
        y ∈ P.boundary (.Iic x) k (!α) →
        y ∈ P.properBoundary (P.boundary (.Iic x) k (!α)) := by
      rintro y ⟨j, hj, hji, hyj⟩ hyD
      have hyc : y ∈ LowerSet.Iic x := boundary_le (.Iic x) k (!α) hyD
      have hyi := hxs.le hyc
      obtain ⟨β, hyβ⟩ : ∃ β, y ∈ P.boundary (L.getD i ⊥) k' β := by
        rcases Nat.lt_or_gt_of_ne hji with hlt | hlt
        · exact ⟨false, hL.inf_le_boundary_false hlt hi ⟨hyj, hyi⟩⟩
        · exact ⟨true, hL.inf_le_boundary_true hlt hj ⟨hyi, hyj⟩⟩
      have h1 : y ∈ P.boundary (.Iic x) k' β := hxs.inf_boundary_le k' β ⟨hyc, hyβ⟩
      have h2 : y ∈ P.boundary (P.boundary (.Iic x) k (!α)) k' β := by rwa [hg k' k hk' β (!α)]
      have hkc : (k' : WithBot ℕ∞) < krullDim (P.boundary (.Iic x) k (!α)) := by
        rw [hcm.krullDim_boundary (by rw [LowerSet.krullDim_Iic]; exact_mod_cast hkx.le)]
        exact_mod_cast hk'
      exact boundary_le_properBoundary hkc β h2
    ext y
    have hA := hmem α y
    have hB := hmem (!α) y
    have hK := key y
    rw [← SetLike.mem_coe (p := P.boundary (L.getD i ⊥) k α), ih2] at hA
    simp only [mem_union, mem_sdiff, SetLike.mem_coe, OGP.mem_interior] at hA hB ⊢
    constructor
    · intro ha
      rcases hA.1 ha with (⟨hb, hn⟩ | he) | hR
      · exact Or.inl ⟨hB.2 (Or.inl hb), hn⟩
      · exact Or.inr he
      · exact Or.inl ⟨hB.2 (Or.inr hR), fun ⟨hd, hf⟩ => hf (hK hR hd)⟩
    · rintro (⟨ha', hn⟩ | he)
      · rcases hB.1 ha' with hb | hR
        · exact hA.2 (Or.inl (Or.inl ⟨hb, hn⟩))
        · exact hA.2 (Or.inr hR)
      · exact hA.2 (Or.inl (Or.inr he))

theorem IsLayering.boundary_true_getD_eq (h : IsLayering P k U L) {i : ℕ} (hi : i < L.length)
    (hx : Maximal (· ∈ L.getD i ⊥) x) (hk : k < grade ℕ x) :
    (P.boundary (L.getD i ⊥) k true : Set P) =
      ((P.boundary (L.getD i ⊥) k false : Set P) \
          P.interior (P.boundary (.Iic x) k false)) ∪
        P.boundary (.Iic x) k true := by
  have ht : P.topsAbove (L.getD i ⊥) k = {x} := Set.eq_singleton_iff_unique_mem.2
    ⟨⟨hx, hk⟩, fun _ hy => (h.existsUnique_top_getD hi).unique hy ⟨hx, hk⟩⟩
  exact (isSubmoleculeOf_and_boundary_eq_of_topsAbove_eq (h.isMoleculeIn_getD hi) k x ht true).2

section UniqueTop

variable {L : LowerSet P} {t : P}

theorem topsAbove_eq_singleton_of_unique_top {k : ℕ} (ht : t ∈ L) (hdt : grade ℕ t = k + 1)
    (hdim : krullDim L = (k + 1 : ℕ)) (huniq : ∀ y ∈ L, grade ℕ y = k + 1 → y = t) :
    P.topsAbove L k = {t} := by
  refine Set.eq_singleton_iff_unique_mem.2
    ⟨⟨maximal_mem_of_krullDim_le ht (by rw [hdim, hdt]), by omega⟩, fun y ⟨hyM, hyd⟩ => ?_⟩
  have : grade ℕ y ≤ k + 1 := krullDim_le_coe_iff.1 hdim.le ⟨y, hyM.prop⟩
  exact huniq y hyM.prop (by omega)

theorem eq_Iic_sup_lowerClosure_maximal_ne (hL : IsMoleculeIn P L) (ht : t ∈ L) :
    L = .Iic t ⊔ lowerClosure {z | Maximal (· ∈ L) z ∧ z ≠ t} := by
  refine le_antisymm (fun x hx => ?_)
    (sup_le (LowerSet.Iic_le.2 ht) (lowerClosure_le.2 fun z hz => hz.1.prop))
  obtain ⟨z, hxz, hzM⟩ := hL.exists_le_maximal hx
  by_cases hzt : z = t
  · exact Or.inl (hzt ▸ hxz)
  · exact Or.inr (mem_lowerClosure.2 ⟨z, ⟨hzM, hzt⟩, hxz⟩)

theorem lowerClosure_maximal_ne_le_boundary (hdim : krullDim L = (grade ℕ t : WithBot ℕ∞))
    (huniq : ∀ y ∈ L, grade ℕ y = grade ℕ t → y = t) (α : Bool) :
    lowerClosure {z | Maximal (· ∈ L) z ∧ z ≠ t} ≤ P.boundary L (grade ℕ t - 1) α := by
  refine lowerClosure_le.2 fun z ⟨hzM, hzt⟩ => ?_
  have h1 : grade ℕ z ≤ grade ℕ t := krullDim_le_coe_iff.1 hdim.le ⟨z, hzM.prop⟩
  have h2 : grade ℕ z ≠ grade ℕ t := fun h => hzt (huniq z hzM.prop h)
  exact mem_boundary_of_maximal_of_grade_le hzM (by omega) α

theorem boundary_eq_sup_of_unique_top (hL : IsMoleculeIn P L) (ht : t ∈ L)
    (hpos : 0 < grade ℕ t) (hdim : krullDim L = (grade ℕ t : WithBot ℕ∞))
    (huniq : ∀ y ∈ L, grade ℕ y = grade ℕ t → y = t) (α : Bool) :
    P.boundary L (grade ℕ t - 1) α =
      P.boundary (.Iic t) (grade ℕ t - 1) α ⊔ lowerClosure {z | Maximal (· ∈ L) z ∧ z ≠ t} := by
  have htop : P.topsAbove L (grade ℕ t - 1) = {t} :=
    topsAbove_eq_singleton_of_unique_top ht (by omega)
      (by rw [hdim]; exact_mod_cast (by omega : grade ℕ t = grade ℕ t - 1 + 1))
      fun y hy hyd => huniq y hy (by omega)
  refine le_antisymm (fun x hx => ?_) (sup_le
    (isSubmoleculeOf_and_boundary_eq_of_topsAbove_eq hL (grade ℕ t - 1) t htop α).1.le
    (lowerClosure_maximal_ne_le_boundary hdim huniq α))
  obtain ⟨z, hz, hxz⟩ := mem_boundary.1 hx
  by_cases hzM : Maximal (· ∈ L) z
  · have hzt : z ≠ t := by
      rintro rfl
      rcases hz with ⟨-, hd, -⟩ | ⟨-, hd⟩ <;> omega
    exact Or.inr (mem_lowerClosure.2 ⟨z, ⟨hzM, hzt⟩, hxz⟩)
  · rcases hz with ⟨hzL, hzd, hzc⟩ | ⟨hzM', -⟩
    · obtain ⟨w, hzw, hwM⟩ := hL.exists_le_maximal hzL
      have hwt : w = t := by
        by_contra hwt
        have hwd : grade ℕ w ≤ grade ℕ t := krullDim_le_coe_iff.1 hdim.le ⟨w, hwM.prop⟩
        have hwne : grade ℕ w ≠ grade ℕ t := fun h => hwt (huniq w hwM.prop h)
        have hzw' : z < w := hzw.lt_of_ne fun h => hzM (h ▸ hwM)
        have := grade_strictMono (𝕆 := ℕ) hzw'
        omega
      subst hwt
      exact Or.inl (mem_boundary_of_mem_facesIn
        (mem_facesIn_of_subset (LowerSet.Iic_le.2 ht) ⟨hzL, hzd, hzc⟩ hzw) hxz)
    · exact absurd hzM' hzM

theorem lowerClosure_maximal_ne_inf_le_boundary (hL : IsMoleculeIn P L) (ht : t ∈ L)
    (hdim : krullDim L = (grade ℕ t : WithBot ℕ∞))
    (huniq : ∀ y ∈ L, grade ℕ y = grade ℕ t → y = t) (α : Bool) :
    lowerClosure {z | Maximal (· ∈ L) z ∧ z ≠ t} ⊓ .Iic t ≤
      P.boundary (.Iic t) (grade ℕ t - 1) α :=
  fun _ ⟨hx1, hx2⟩ => (hL.Iic_isSubmoleculeOf ht).inf_boundary_le (grade ℕ t - 1) α
    ⟨hx2, lowerClosure_maximal_ne_le_boundary hdim huniq α hx1⟩

theorem boundary_not_eq_of_unique_top (hL : IsMoleculeIn P L) (ht : t ∈ L)
    (hpos : 0 < grade ℕ t) (hdim : krullDim L = (grade ℕ t : WithBot ℕ∞))
    (huniq : ∀ y ∈ L, grade ℕ y = grade ℕ t → y = t) (α : Bool) :
    (P.boundary L (grade ℕ t - 1) (!α) : Set P) =
      ((P.boundary L (grade ℕ t - 1) α : Set P) \
          P.interior (P.boundary (.Iic t) (grade ℕ t - 1) α)) ∪
        P.boundary (.Iic t) (grade ℕ t - 1) (!α) := by
  have := (isSubmoleculeOf_and_boundary_eq_of_topsAbove_eq hL (grade ℕ t - 1) t
    (topsAbove_eq_singleton_of_unique_top ht (k := grade ℕ t - 1) (by omega)
      (by rw [hdim]; exact_mod_cast (by omega : grade ℕ t = grade ℕ t - 1 + 1))
      fun y hy hyd => huniq y hy (by omega)) (!α)).2
  rwa [Bool.not_not] at this

theorem eq_boundary_sup_Iic_of_unique_top {k : ℕ} (hL : IsMoleculeIn P L)
    (ht : t ∈ L) (hdt : grade ℕ t = k + 1) (hdim : krullDim L = (k + 1 : ℕ))
    (huniq : ∀ y ∈ L, grade ℕ y = k + 1 → y = t) (β : Bool) :
    L = P.boundary L k β ⊔ .Iic t := by
  have hk : grade ℕ t - 1 = k := by omega
  have huniq' : ∀ y ∈ L, grade ℕ y = grade ℕ t → y = t := fun y hy hy' => huniq y hy (by omega)
  refine le_antisymm (fun x hx => ?_) (sup_le (boundary_le L k β) (LowerSet.Iic_le.2 ht))
  rw [eq_Iic_sup_lowerClosure_maximal_ne hL ht] at hx
  rcases hx with h | h
  · exact Or.inr h
  · exact Or.inl (hk ▸ lowerClosure_maximal_ne_le_boundary (by rw [hdim, hdt]) huniq' β h)

theorem Iic_inf_boundary_of_unique_top {k : ℕ} (hL : IsMoleculeIn P L)
    (ht : t ∈ L) (hdt : grade ℕ t = k + 1) (hdim : krullDim L = (k + 1 : ℕ))
    (huniq : ∀ y ∈ L, grade ℕ y = k + 1 → y = t) (β : Bool) :
    .Iic t ⊓ P.boundary L k β = P.boundary (.Iic t) k β := by
  have hk : grade ℕ t - 1 = k := by omega
  have huniq' : ∀ y ∈ L, grade ℕ y = grade ℕ t → y = t := fun y hy hy' => huniq y hy (by omega)
  have hb := boundary_eq_sup_of_unique_top hL ht (by omega) (by rw [hdim, hdt]) huniq' β
  have hi := lowerClosure_maximal_ne_inf_le_boundary hL ht (by rw [hdim, hdt]) huniq' β
  rw [hk] at hb hi
  rw [hb, inf_sup_left]
  exact le_antisymm (sup_le inf_le_right (inf_comm (LowerSet.Iic t) _ ▸ hi))
    (fun x hx => Or.inl ⟨boundary_le (.Iic t) k β hx, hx⟩)

end UniqueTop

end Atoms.Molecule.OGP
