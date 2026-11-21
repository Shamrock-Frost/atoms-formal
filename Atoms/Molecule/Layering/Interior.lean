import Atoms.Molecule.Layering.Boundary

universe u v

open Order Set

namespace Atoms.Molecule.OGP

variable {P : OGP.{u}} {U : LowerSet P}

theorem exists_mem_boundary_Iic_of_lt {x t : P} (hxt : x < t) :
    ∃ α : Bool, x ∈ P.boundary (.Iic t) (grade ℕ t - 1) α := by
  have hdt : grade ℕ t = (grade ℕ t - 1) + 1 := by
    have := grade_strictMono (𝕆 := ℕ) hxt; omega
  obtain ⟨z, hxz, hzt⟩ := exists_le_covBy_of_lt hxt
  refine ⟨P.orient hzt, ?_⟩
  rw [boundary_Iic hdt]
  exact mem_lowerClosure.2 ⟨z, ⟨hzt, rfl⟩, hxz⟩

theorem notMem_interior_boundary_Iic (hU : IsMoleculeIn P U) {x y : P}
    (hy : y ∈ U) (hpos : 0 < grade ℕ y) (α : Bool)
    (hα : x ∈ P.boundary (.Iic y) (grade ℕ y - 1) α)
    (hnα : x ∈ P.boundary (.Iic y) (grade ℕ y - 1) (!α)) :
    x ∉ P.interior (P.boundary (.Iic y) (grade ℕ y - 1) α) := by
  intro hx
  refine hx.2 ?_
  have hT := hU.isAtomIn_Iic hy
  rw [← hT.isRound.inf_boundary_eq_properBoundary hT.isMoleculeIn (k := grade ℕ y - 1)
    (by rw [LowerSet.krullDim_Iic]; exact_mod_cast Nat.sub_lt hpos Nat.one_pos) α]
  exact ⟨hα, hnα⟩

theorem mem_interior_boundary_Iic_of_unique_top {L : LowerSet P}
    {t x : P} (hL : IsMoleculeIn P L) (ht : t ∈ L) (hpos : 0 < grade ℕ t)
    (hdim : krullDim L = (grade ℕ t : WithBot ℕ∞))
    (huniq : ∀ y ∈ L, grade ℕ y = grade ℕ t → y = t) (α : Bool)
    (hx : x ∈ P.boundary L (grade ℕ t - 1) α) (hnx : x ∉ P.boundary L (grade ℕ t - 1) (!α)) :
    x ∈ P.interior (P.boundary (.Iic t) (grade ℕ t - 1) α) := by
  have hmem : x ∈ P.boundary (.Iic t) (grade ℕ t - 1) α :=
    Or.resolve_right ((boundary_eq_sup_of_unique_top hL ht hpos hdim huniq α).le hx)
      fun h => hnx (lowerClosure_maximal_ne_le_boundary hdim huniq (!α) h)
  have hnot : x ∉ P.boundary (.Iic t) (grade ℕ t - 1) (!α) := fun h =>
    hnx ((boundary_eq_sup_of_unique_top hL ht hpos hdim huniq (!α)).ge (Or.inl h))
  refine ⟨hmem, fun hb => ?_⟩
  have hT := hL.isAtomIn_Iic ht
  rw [← hT.isRound.inf_boundary_eq_properBoundary hT.isMoleculeIn (k := grade ℕ t - 1)
    (by rw [LowerSet.krullDim_Iic]; exact_mod_cast Nat.sub_lt hpos Nat.one_pos) α] at hb
  exact hnot hb.2

theorem exists_mem_boundary_of_unique_top {L : LowerSet P} {t x : P}
    (hL : IsMoleculeIn P L) (ht : t ∈ L) (hpos : 0 < grade ℕ t)
    (hdim : krullDim L = (grade ℕ t : WithBot ℕ∞))
    (huniq : ∀ y ∈ L, grade ℕ y = grade ℕ t → y = t) (hx : x ∈ L) (hxd : grade ℕ x < grade ℕ t) :
    ∃ α : Bool, x ∈ P.boundary L (grade ℕ t - 1) α := by
  rw [eq_Iic_sup_lowerClosure_maximal_ne hL ht] at hx
  rcases hx with h | h
  · have hxt : x < t := lt_of_le_of_ne h (fun he => by subst he; omega)
    obtain ⟨α, hα⟩ := exists_mem_boundary_Iic_of_lt hxt
    exact ⟨α, (boundary_eq_sup_of_unique_top hL ht hpos hdim huniq α).ge (Or.inl hα)⟩
  · exact ⟨true, lowerClosure_maximal_ne_le_boundary hdim huniq true h⟩

theorem IsLayering.Iic_inf_le_of_lt {k : ℕ} {L : List (LowerSet P)}
    (h : IsLayering P k U L) {i j : ℕ} (hij : i < j) (hj : j < L.length) {y y' : P}
    (hy : y ∈ L.getD i ⊥) (hy' : y' ∈ L.getD j ⊥) :
    .Iic y ⊓ .Iic y' ≤ P.boundary (.Iic y) k true ⊓ P.boundary (.Iic y') k false := by
  have hi : i < L.length := by omega
  rintro x ⟨hxy, hxy'⟩
  have hxi : x ∈ L.getD i ⊥ := (L.getD i ⊥).lower hxy hy
  have hxj : x ∈ L.getD j ⊥ := (L.getD j ⊥).lower hxy' hy'
  obtain ⟨hbi, hbj⟩ := (h.inf_eq hij hj).le ⟨hxi, hxj⟩
  exact ⟨((h.isMoleculeIn_getD hi).Iic_isSubmoleculeOf hy).inf_boundary_le k true ⟨hxy, hbi⟩,
    ((h.isMoleculeIn_getD hj).Iic_isSubmoleculeOf hy').inf_boundary_le k false ⟨hxy', hbj⟩⟩

theorem eq_of_mem_interior_boundary_Iic (hU : IsMoleculeIn P U)
    {x y y' : P} (hy : y ∈ U) (hy' : y' ∈ U) (hyd : (grade ℕ y : WithBot ℕ∞) = krullDim U)
    (hy'd : (grade ℕ y' : WithBot ℕ∞) = krullDim U) (α : Bool)
    (hx : x ∈ P.interior (P.boundary (.Iic y) (grade ℕ y - 1) α))
    (hx' : x ∈ P.interior (P.boundary (.Iic y') (grade ℕ y' - 1) α)) : y = y' := by
  have hxy : x ∈ LowerSet.Iic y := boundary_le (.Iic y) _ _ hx.1
  have hxy' : x ∈ LowerSet.Iic y' := boundary_le (.Iic y') _ _ hx'.1
  have hyy' : grade ℕ y = grade ℕ y' := by exact_mod_cast hyd.trans hy'd.symm
  rcases Nat.eq_zero_or_pos (grade ℕ y) with h0 | hpos
  · have e1 := GradeOrder.eq_of_le_of_grade_le hxy (by omega)
    have e2 := GradeOrder.eq_of_le_of_grade_le hxy' (by omega)
    exact e1.symm.trans e2
  have hUk : krullDim U = (grade ℕ y - 1 + 1 : ℕ) := by
    rw [← hyd]; exact_mod_cast (by omega : grade ℕ y = grade ℕ y - 1 + 1)
  obtain ⟨L, h⟩ := admitsLayering_pred_krullDim hU hyd.symm hpos
  obtain ⟨i, hi, hyi⟩ := h.exists_mem_getD hy
  obtain ⟨j, hj, hyj⟩ := h.exists_mem_getD hy'
  have hmem : x ∈ (.Iic y ⊓ .Iic y' : LowerSet P) := ⟨hxy, hxy'⟩
  rcases lt_trichotomy i j with hij | rfl | hji
  · obtain ⟨h1, h2⟩ := h.Iic_inf_le_of_lt hij hj hyi hyj hmem
    rw [hyy'] at h2
    cases α
    · exact absurd hx (notMem_interior_boundary_Iic hU hy hpos false hx.1 h1)
    · exact absurd hx' (notMem_interior_boundary_Iic hU hy' (by omega) true hx'.1 h2)
  · obtain ⟨t, -, -, -, hu⟩ := h.exists_top_getD hUk hi
    rw [hu y hyi (by omega), hu y' hyj (by omega)]
  · rw [inf_comm] at hmem
    obtain ⟨h1, h2⟩ := h.Iic_inf_le_of_lt hji hi hyj hyi hmem
    rw [hyy'] at h1
    cases α
    · exact absurd hx' (notMem_interior_boundary_Iic hU hy' (by omega) false hx'.1 h1)
    · exact absurd hx (notMem_interior_boundary_Iic hU hy hpos true hx.1 h2)

theorem notMem_boundary_of_mem_interior_boundary_Iic (hU : IsMoleculeIn P U)
    {x y : P} (hy : y ∈ U) (hpos : 0 < grade ℕ y) (α : Bool)
    (hx : x ∈ P.interior (P.boundary (.Iic y) (grade ℕ y - 1) α)) :
    x ∉ P.boundary U (grade ℕ y - 1) (!α) := by
  intro hb
  have hxy : x ∈ LowerSet.Iic y := boundary_le (.Iic y) _ _ hx.1
  exact notMem_interior_boundary_Iic hU hy hpos α hx.1
    ((hU.Iic_isSubmoleculeOf hy).inf_boundary_le (grade ℕ y - 1) (!α) ⟨hxy, hb⟩) hx

theorem mem_interior_iff_of_isMoleculeIn (hU : IsMoleculeIn P U) {x : P} (hx : x ∈ U) :
    x ∈ P.interior U ↔
      (grade ℕ x : WithBot ℕ∞) = krullDim U ∨
        ((grade ℕ x : WithBot ℕ∞) < krullDim U ∧
          ∃ yp ∈ U, ∃ ym ∈ U,
            (grade ℕ yp : WithBot ℕ∞) = krullDim U ∧ (grade ℕ ym : WithBot ℕ∞) = krullDim U ∧
            x ∈ P.interior (P.boundary (.Iic yp) (grade ℕ yp - 1) true) ∧
            x ∈ P.interior (P.boundary (.Iic ym) (grade ℕ ym - 1) false)) := by
  obtain ⟨d, hd⟩ := hU.exists_krullDim_eq
  rcases d with _ | k
  · have hxd : (grade ℕ x : WithBot ℕ∞) = krullDim U :=
      le_antisymm (grade_le_krullDim (⟨x, hx⟩ : U)) (by rw [hd]; exact_mod_cast Nat.zero_le _)
    refine ⟨fun _ => Or.inl hxd, fun _ => ?_⟩
    rw [interior_eq_self (by rw [hd]; rfl)]
    exact hx
  have hd' : krullDim U = k + 1 := by rw [hd]; push_cast; rfl
  constructor
  · intro hint
    rcases (grade_le_krullDim (⟨x, hx⟩ : U)).eq_or_lt with he | hlt
    · exact Or.inl he
    refine Or.inr ⟨hlt, ?_⟩
    have hnb : x ∉ P.bdryFull U := hU.properBoundary_eq_bdryFull ▸ hint.2
    rw [bdryFull, bdry_eq_boundary hd', bdry_eq_boundary hd', LowerSet.mem_sup_iff, not_or] at hnb
    obtain ⟨hnf, hnt⟩ := hnb
    have hxk : grade ℕ x < k + 1 := by rw [hd] at hlt; exact_mod_cast hlt
    obtain ⟨L, h⟩ := admitsLayering_pred_krullDim hU hd (Nat.succ_pos k)
    rw [Nat.add_sub_cancel] at h
    have hstate : ∃ i < L.length, ∃ α, x ∈ P.boundary (L.getD i ⊥) k α := by
      obtain ⟨i, hi, hxi⟩ := h.exists_mem_getD hx
      obtain ⟨t, ht, htd, hdim, hu⟩ := h.exists_top_getD hd hi
      have hb := exists_mem_boundary_of_unique_top (h.isMoleculeIn_getD hi) ht
        (by omega) (by rw [hdim, htd]) (fun y hy hyd => hu y hy (by omega)) hxi (by omega)
      rw [htd, Nat.add_sub_cancel] at hb
      exact ⟨i, hi, hb⟩
    have hexTrue : ∃ j < L.length, x ∈ P.boundary (L.getD j ⊥) k true := by
      obtain ⟨i, hi, _ | _, hb⟩ := hstate
      · cases i with
        | zero => rw [h.boundary_false_getD_zero] at hb; exact absurd hb hnf
        | succ i => rw [h.boundary_false_getD_succ hi] at hb; exact ⟨i, by omega, hb⟩
      · exact ⟨i, hi, hb⟩
    have hexFalse : ∃ j < L.length, x ∈ P.boundary (L.getD j ⊥) k false := by
      obtain ⟨i, hi, hb⟩ := hexTrue
      by_cases hil : i + 1 < L.length
      · exact ⟨i + 1, hil, by rw [h.boundary_false_getD_succ hil]; exact hb⟩
      · have hie : i = L.length - 1 := by omega
        rw [hie, h.boundary_true_getD_last] at hb
        exact absurd hb hnt
    classical
    obtain ⟨j, hj, hxj, hmin⟩ : ∃ j < L.length,
        x ∈ P.boundary (L.getD j ⊥) k true ∧
          ∀ l < j, x ∉ P.boundary (L.getD l ⊥) k true :=
      ⟨Nat.find hexTrue, (Nat.find_spec hexTrue).1, (Nat.find_spec hexTrue).2,
        fun l hl hpl => Nat.find_min hexTrue hl ⟨hl.trans (Nat.find_spec hexTrue).1, hpl⟩⟩
    obtain ⟨l, hl, hxl, hmax⟩ : ∃ l < L.length,
        x ∈ P.boundary (L.getD l ⊥) k false ∧
          ∀ l', l < l' → l' < L.length → x ∉ P.boundary (L.getD l' ⊥) k false := by
      obtain ⟨i, hi, hb⟩ := hexFalse
      let q : ℕ → Prop := fun l => x ∈ P.boundary (L.getD l ⊥) k false
      refine ⟨Nat.findGreatest q (L.length - 1),
        lt_of_le_of_lt (Nat.findGreatest_le (P := q) _) (by omega),
        Nat.findGreatest_spec (P := q) (m := i) (by omega) hb, fun l' hl' hl'm => ?_⟩
      exact Nat.findGreatest_is_greatest (P := q) hl' (by omega)
    obtain ⟨tp, htp, htpd, hpdim, hpu⟩ := h.exists_top_getD hd hj
    obtain ⟨tm, htm, htmd, hmdim, hmu⟩ := h.exists_top_getD hd hl
    have hnj : x ∉ P.boundary (L.getD j ⊥) k false := by
      cases j with
      | zero => rw [h.boundary_false_getD_zero]; exact hnf
      | succ j => rw [h.boundary_false_getD_succ hj]; exact hmin j (by omega)
    have hnl : x ∉ P.boundary (L.getD l ⊥) k true := by
      by_cases hll : l + 1 < L.length
      · rw [← h.boundary_false_getD_succ hll]; exact hmax (l + 1) (by omega) hll
      · have hle : l = L.length - 1 := by omega
        rw [hle, h.boundary_true_getD_last]
        exact hnt
    have hp := mem_interior_boundary_Iic_of_unique_top (h.isMoleculeIn_getD hj)
      htp (by omega) (by rw [hpdim, htpd]) (fun y hy hyd => hpu y hy (by omega)) true
      (by rw [htpd, Nat.add_sub_cancel]; exact hxj) (by rw [htpd, Nat.add_sub_cancel]; exact hnj)
    have hm := mem_interior_boundary_Iic_of_unique_top (h.isMoleculeIn_getD hl)
      htm (by omega) (by rw [hmdim, htmd]) (fun y hy hyd => hmu y hy (by omega)) false
      (by rw [htmd, Nat.add_sub_cancel]; exact hxl) (by rw [htmd, Nat.add_sub_cancel]; exact hnl)
    exact ⟨tp, h.le hj htp, tm, h.le hl htm, by rw [htpd, hd], by rw [htmd, hd], hp, hm⟩
  · intro hx'
    refine ⟨hx, fun hb => ?_⟩
    rw [hU.properBoundary_eq_bdryFull, bdryFull, bdry_eq_boundary hd', bdry_eq_boundary hd'] at hb
    rcases hx' with hxd | ⟨-, yp, hyp, ym, hym, hypd, hymd, hp, hm⟩
    · have hxd' : grade ℕ x = k + 1 := by exact_mod_cast hxd.trans hd
      rcases hb with hb | hb <;> (have := grade_le_of_mem_boundary hb; omega)
    · have hypd' : grade ℕ yp = k + 1 := by exact_mod_cast hypd.trans hd
      have hymd' : grade ℕ ym = k + 1 := by exact_mod_cast hymd.trans hd
      rcases hb with hb | hb
      · exact notMem_boundary_of_mem_interior_boundary_Iic hU hyp (by omega) true hp
          (by rwa [hypd', Nat.add_sub_cancel])
      · exact notMem_boundary_of_mem_interior_boundary_Iic hU hym (by omega) false hm
          (by rwa [hymd', Nat.add_sub_cancel])

section Morphism

variable {P : OGP.{u}} {Q : OGP.{v}} {f : P → Q}

theorem IsMorphism.image_boundary_Iic (hf : IsMorphism f) {x : P}
    (hx : 0 < grade ℕ x) (α : Bool) :
    f '' P.boundary (.Iic x) (grade ℕ x - 1) α =
      Q.boundary (.Iic (f x)) (grade ℕ (f x) - 1) α := by
  have h1 : grade ℕ x = (grade ℕ x - 1) + 1 := by omega
  have h2 : grade ℕ (f x) = (grade ℕ (f x) - 1) + 1 := by rw [hf.grade_eq]; omega
  rw [boundary_Iic h1, boundary_Iic h2, hf.fibration.image_lowerClosure hf.monotone,
    (hf.bijOn_faces x α).image_eq]

theorem IsMorphism.mem_interior_of_mem_interior (hf : IsMorphism f) (n : ℕ) :
    ∀ (U : LowerSet P) (V : LowerSet Q), krullDim U = (n : ℕ) → IsMoleculeIn P U →
      IsMoleculeIn Q V → f '' (U : Set P) ⊆ V → krullDim U = krullDim V →
      ∀ x ∈ P.interior U, f x ∈ Q.interior V := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro U V hn hU hV hUV hd x hx
    have hxU : x ∈ U := P.interior_subset U hx
    have hfxV : f x ∈ V := hUV (mem_image_of_mem f hxU)
    rcases (mem_interior_iff_of_isMoleculeIn hU hxU).1 hx with
      hdx | ⟨hlt, yp, hyp, ym, hym, hdp, hdm, hxp, hxm⟩
    · exact (mem_interior_iff_of_isMoleculeIn hV hfxV).2
        (Or.inl (by rw [hf.grade_eq, hdx, hd]))
    · have step : ∀ (y : P) (α : Bool), y ∈ U → (grade ℕ y : WithBot ℕ∞) = krullDim U →
          x ∈ P.interior (P.boundary (.Iic y) (grade ℕ y - 1) α) →
          f x ∈ Q.interior (Q.boundary (.Iic (f y)) (grade ℕ (f y) - 1) α) := by
        intro y α hy hdy hxy
        have hfy : f y ∈ V := hUV (mem_image_of_mem f hy)
        have hyn : grade ℕ y = n := by exact_mod_cast hdy.trans hn
        have hpos : 0 < grade ℕ y :=
          hyn ▸ (Nat.zero_le (grade ℕ x)).trans_lt (by exact_mod_cast hlt.trans_eq hn)
        have hA := (hU.isAtomIn_Iic hy).isMoleculeIn
        have hB := (hV.isAtomIn_Iic hfy).isMoleculeIn
        have hdA : krullDim (P.boundary (.Iic y) (grade ℕ y - 1) α) = (grade ℕ y - 1 : ℕ) :=
          hA.krullDim_boundary (by rw [LowerSet.krullDim_Iic]; exact_mod_cast (by omega)) α
        have hdB : krullDim (Q.boundary (.Iic (f y)) (grade ℕ (f y) - 1) α) =
            (grade ℕ y - 1 : ℕ) := by
          rw [hf.grade_eq]
          exact hB.krullDim_boundary
            (by rw [LowerSet.krullDim_Iic, hf.grade_eq]; exact_mod_cast (by omega)) α
        exact ih (grade ℕ y - 1) (by omega) _ _ hdA (hA.boundary _ α)
          (hB.boundary _ α) (hf.image_boundary_Iic hpos α).subset (hdA.trans hdB.symm) x hxy
      exact (mem_interior_iff_of_isMoleculeIn hV hfxV).2 (Or.inr
        ⟨by rw [hf.grade_eq, ← hd]; exact hlt,
          f yp, hUV (mem_image_of_mem f hyp), f ym, hUV (mem_image_of_mem f hym),
          by rw [hf.grade_eq, hdp, hd], by rw [hf.grade_eq, hdm, hd],
          step yp true hyp hdp hxp, step ym false hym hdm hxm⟩)

theorem IsMorphism.image_interior_subset (hf : IsMorphism f) {U : LowerSet P}
    {V : LowerSet Q} (hU : IsMoleculeIn P U) (hV : IsMoleculeIn Q V) (hUV : f '' (U : Set P) ⊆ V)
    (hd : krullDim U = krullDim V) : f '' P.interior U ⊆ Q.interior V := by
  obtain ⟨n, hn⟩ := hU.exists_krullDim_eq
  rintro _ ⟨x, hx, rfl⟩
  exact hf.mem_interior_of_mem_interior n U V hn hU hV hUV hd x hx

end Morphism

end Atoms.Molecule.OGP
