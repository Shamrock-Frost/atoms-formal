import Atoms.ForMathlib.Order.UpperLower.CompleteLattice
import Atoms.Molecule.OrientedGradedPoset

universe u

open Order Set

namespace Atoms.Molecule.OGP

variable {P : OGP.{u}} {U V : LowerSet P} {n : ℕ} {α : Bool} {x z : P}

theorem mem_boundary :
    x ∈ P.boundary U n α ↔
      ∃ z, (z ∈ P.facesIn U n α ∨ Maximal (· ∈ U) z ∧ grade ℕ z < n) ∧ x ≤ z :=
  mem_lowerClosure

theorem mem_boundary_of_mem_facesIn (hz : z ∈ P.facesIn U n α) (hxz : x ≤ z) :
    x ∈ P.boundary U n α :=
  mem_boundary.2 ⟨z, Or.inl hz, hxz⟩

theorem mem_boundary_of_maximal (hz : Maximal (· ∈ U) z) (hn : grade ℕ z < n) (hxz : x ≤ z) :
    x ∈ P.boundary U n α :=
  mem_boundary.2 ⟨z, Or.inr ⟨hz, hn⟩, hxz⟩

theorem boundary_congr (hf : P.facesIn U n α = P.facesIn V n α)
    (hm : ∀ x, grade ℕ x < n → (Maximal (· ∈ U) x ↔ Maximal (· ∈ V) x)) :
    P.boundary U n α = P.boundary V n α :=
  SetLike.ext fun x => by
    simp only [mem_boundary, hf]
    exact exists_congr fun z => and_congr_left fun _ => or_congr_right
      ⟨fun h => ⟨(hm z h.2).1 h.1, h.2⟩, fun h => ⟨(hm z h.2).2 h.1, h.2⟩⟩

theorem krullDim_boundary_le (U : LowerSet P) (n : ℕ) (α : Bool) :
    krullDim (P.boundary U n α) ≤ n :=
  krullDim_le_coe_iff.2 fun ⟨x, hx⟩ => by
    obtain ⟨z, hz, hxz⟩ := mem_boundary.1 hx
    exact (grade_mono hxz).trans (hz.elim (fun h => h.2.1.le) fun h => h.2.le)

theorem grade_le_of_mem_boundary (hx : x ∈ P.boundary U n α) : grade ℕ x ≤ n :=
  krullDim_le_coe_iff.1 (krullDim_boundary_le U n α) ⟨x, hx⟩

theorem maximal_mem_of_krullDim_le (hx : x ∈ U) (h : krullDim U ≤ grade ℕ x) :
    Maximal (· ∈ U) x :=
  ⟨hx, fun y hy hxy => (GradeOrder.eq_of_le_of_grade_le hxy
    (krullDim_le_coe_iff.1 h ⟨y, hy⟩)).ge⟩

theorem maximal_mem_iff_forall_mem_facesIn :
    Maximal (· ∈ U) x ↔ ∀ α, x ∈ P.facesIn U (grade ℕ x) α := by
  refine ⟨fun h α => ⟨h.prop, rfl, disjoint_left.2 fun c hc hcU =>
    hc.1.lt.not_ge (h.2 hcU hc.1.le)⟩, fun h => ?_⟩
  by_contra hx
  obtain ⟨y, hxy, hy⟩ := (not_maximal_iff_exists_gt (h false).1).1 hx
  obtain ⟨c, hxc, hcy⟩ := exists_covBy_le_of_lt hxy
  exact disjoint_left.1 (h (!P.orient hxc)).2.2 ⟨hxc, (Bool.not_not _).symm⟩ (U.lower hcy hy)

theorem mem_boundary_of_maximal_of_grade_le (hz : Maximal (· ∈ U) z) (hn : grade ℕ z ≤ n)
    (α : Bool) : z ∈ P.boundary U n α := by
  rcases hn.lt_or_eq with hn | rfl
  · exact mem_boundary_of_maximal hz hn le_rfl
  · exact mem_boundary_of_mem_facesIn (maximal_mem_iff_forall_mem_facesIn.1 hz α) le_rfl

theorem boundary_eq_self (hn : krullDim U ≤ n) (α : Bool) : P.boundary U n α = U := by
  refine le_antisymm (boundary_le U n α) fun x hx => ?_
  have hU : ∀ y ∈ (U : Set P), grade ℕ y ≤ n :=
    fun y hy => krullDim_le_coe_iff.1 hn ⟨y, hy⟩
  obtain ⟨z, hxz, hz⟩ := GradeOrder.exists_le_maximal hU hx
  rcases (hU z hz.prop).eq_or_lt with h | h
  · exact mem_boundary_of_mem_facesIn (h ▸ maximal_mem_iff_forall_mem_facesIn.1 hz α) hxz
  · exact mem_boundary_of_maximal hz h hxz

theorem boundary_eq_self_iff : P.boundary U n α = U ↔ krullDim U ≤ n :=
  ⟨fun h => h ▸ krullDim_boundary_le U n α, fun h => boundary_eq_self h α⟩

theorem boundary_lt_iff : P.boundary U n α < U ↔ (n : WithBot ℕ∞) < krullDim U := by
  rw [(boundary_le U n α).lt_iff_ne, Ne, boundary_eq_self_iff, not_le]

theorem boundary_boundary_of_le {m : ℕ} (h : n ≤ m) (α β : Bool) :
    P.boundary (P.boundary U n β) m α = P.boundary U n β :=
  boundary_eq_self ((krullDim_boundary_le U n β).trans (by exact_mod_cast h)) α

theorem maximal_mem_boundary_iff :
    Maximal (· ∈ P.boundary U n α) x ↔
      x ∈ P.facesIn U n α ∨ Maximal (· ∈ U) x ∧ grade ℕ x < n := by
  refine IsAntichain.maximal_mem_lowerClosure_iff_mem fun a ha b hb hne hab => hne ?_
  have hb' : b ∈ U ∧ grade ℕ b ≤ n := hb.elim (fun h => ⟨h.1, h.2.1.le⟩) fun h => ⟨h.1.prop, h.2.le⟩
  rcases ha with ha | ha
  · exact GradeOrder.eq_of_le_of_grade_le hab (ha.2.1 ▸ hb'.2)
  · exact ha.1.eq_of_le hb'.1 hab

theorem mem_facesIn_of_mem_boundary (hx : x ∈ P.boundary U n α) (hn : grade ℕ x = n) :
    x ∈ P.facesIn U n α :=
  (maximal_mem_boundary_iff.1 (maximal_mem_of_krullDim_le hx
    ((krullDim_boundary_le U n α).trans (by rw [hn])))).resolve_right fun h => h.2.ne hn

theorem maximal_mem_boundary_iff_of_grade_lt (hn : grade ℕ x < n) :
    Maximal (· ∈ P.boundary U n α) x ↔ Maximal (· ∈ U) x := by
  rw [maximal_mem_boundary_iff, or_iff_right fun h => hn.ne h.2.1, and_iff_left hn]

theorem facesIn_eq_of_boundary_eq (h : P.boundary U n α = P.boundary V n α) :
    P.facesIn U n α = P.facesIn V n α := by
  have key (W : LowerSet P) (x : P) :
      x ∈ P.facesIn W n α ↔ Maximal (· ∈ P.boundary W n α) x ∧ grade ℕ x = n := by
    rw [maximal_mem_boundary_iff]
    exact ⟨fun hx => ⟨Or.inl hx, hx.2.1⟩, fun ⟨hx, hn⟩ => hx.resolve_right fun h => h.2.ne hn⟩
  ext x
  rw [key, key, h]

theorem mem_facesIn_of_subset {A B : Set P} (hAB : A ⊆ B) (hx : x ∈ P.facesIn B n α)
    (hxA : x ∈ A) : x ∈ P.facesIn A n α :=
  ⟨hxA, hx.2.1, hx.2.2.mono_right hAB⟩

theorem facesIn_congr {A B : Set P} (h : ∀ c, grade ℕ c ≤ n + 1 → (c ∈ A ↔ c ∈ B)) :
    P.facesIn A n α = P.facesIn B n α := by
  have key (A B : Set P) (h : ∀ c, grade ℕ c ≤ n + 1 → (c ∈ A ↔ c ∈ B)) :
      P.facesIn A n α ⊆ P.facesIn B n α := fun y ⟨hy, hyn, hd⟩ =>
    ⟨(h y (by omega)).1 hy, hyn, disjoint_left.2 fun c hc hcB => disjoint_left.1 hd hc
      ((h c (by have := Nat.covBy_iff_add_one_eq.1 (hc.1.grade ℕ); omega)).2 hcB)⟩
  exact (key A B h).antisymm (key B A fun c hc => (h c hc).symm)

theorem mem_facesIn_sup_iff :
    x ∈ P.facesIn ↑(U ⊔ V) n α ↔
      (x ∈ U ∨ x ∈ V) ∧ (x ∈ U → x ∈ P.facesIn U n α) ∧ (x ∈ V → x ∈ P.facesIn V n α) := by
  refine ⟨fun h => ⟨h.1, mem_facesIn_of_subset subset_union_left h,
    mem_facesIn_of_subset subset_union_right h⟩, fun ⟨hx, hU, hV⟩ => ⟨hx, ?_, ?_⟩⟩
  · exact hx.elim (fun h => (hU h).2.1) fun h => (hV h).2.1
  · refine disjoint_left.2 fun c hc hcUV => ?_
    rcases hcUV with hcU | hcV
    · exact disjoint_left.1 (hU (U.lower hc.1.le hcU)).2.2 hc hcU
    · exact disjoint_left.1 (hV (V.lower hc.1.le hcV)).2.2 hc hcV

private theorem generator_of_generator_sup
    (hz : z ∈ P.facesIn ↑(U ⊔ V) n α ∨ Maximal (· ∈ U ⊔ V) z ∧ grade ℕ z < n) (hzU : z ∈ U) :
    z ∈ P.facesIn U n α ∨ Maximal (· ∈ U) z ∧ grade ℕ z < n :=
  hz.imp (fun h => (mem_facesIn_sup_iff.1 h).2.1 hzU)
    fun h => ⟨(LowerSet.maximal_mem_sup_iff.1 h.1).2.1 hzU, h.2⟩

theorem mem_boundary_sup_of_notMem
    (hz : z ∈ P.facesIn U n α ∨ Maximal (· ∈ U) z ∧ grade ℕ z < n) (hzV : z ∉ V) (hxz : x ≤ z) :
    x ∈ P.boundary (U ⊔ V) n α := by
  rcases hz with hz | ⟨hz, hn⟩
  · exact mem_boundary_of_mem_facesIn
      (mem_facesIn_sup_iff.2 ⟨Or.inl hz.1, fun _ => hz, fun h => absurd h hzV⟩) hxz
  · exact mem_boundary_of_maximal
      (LowerSet.maximal_mem_sup_iff.2 ⟨Or.inl hz.prop, fun _ => hz, fun h => absurd h hzV⟩) hn hxz

theorem boundary_sup_le (U V : LowerSet P) (n : ℕ) (α : Bool) :
    P.boundary (U ⊔ V) n α ≤ P.boundary U n α ⊔ P.boundary V n α := by
  intro x hx
  obtain ⟨z, hz, hxz⟩ := mem_boundary.1 hx
  have hzUV : z ∈ U ⊔ V := hz.elim (fun h => h.1) fun h => h.1.prop
  rcases hzUV with hzU | hzV
  · exact Or.inl (mem_boundary.2 ⟨z, generator_of_generator_sup hz hzU, hxz⟩)
  · exact Or.inr (mem_boundary.2 ⟨z, generator_of_generator_sup (sup_comm U V ▸ hz) hzV, hxz⟩)

theorem boundary_sup_of_inf_eq_boundary {k : ℕ} (h : U ⊓ V = P.boundary V k α) :
    P.boundary (U ⊔ V) k α = P.boundary U k α := by
  refine boundary_congr (Set.ext fun x => ?_) fun x hn => ?_
  · rw [mem_facesIn_sup_iff]
    refine ⟨fun ⟨hx, hU, hV⟩ => hU (hx.elim id fun hxV => ?_), fun hx => ⟨Or.inl hx.1,
      fun _ => hx, fun hxV => mem_facesIn_of_mem_boundary (h ▸ ⟨hx.1, hxV⟩) hx.2.1⟩⟩
    exact (h.symm ▸ mem_boundary_of_mem_facesIn (hV hxV) le_rfl : x ∈ U ⊓ V).1
  · rw [LowerSet.maximal_mem_sup_iff]
    refine ⟨fun ⟨hx, hU, hV⟩ => hU (hx.elim id fun hxV => ?_), fun hx => ⟨Or.inl hx.prop,
      fun _ => hx, fun hxV => ?_⟩⟩
    · exact (h.symm ▸ mem_boundary_of_maximal (hV hxV) hn le_rfl : x ∈ U ⊓ V).1
    · have hI : Maximal (· ∈ U ⊓ V) x := hx.mono (fun _ hy => hy.1) ⟨hx.prop, hxV⟩
      rwa [h, maximal_mem_boundary_iff_of_grade_lt hn] at hI

theorem boundary_sup_of_boundary_eq (h : P.boundary U n α = P.boundary V n α) :
    P.boundary (U ⊔ V) n α = P.boundary U n α := by
  have hf := facesIn_eq_of_boundary_eq h
  have hm (x : P) (hn : grade ℕ x < n) : Maximal (· ∈ U) x ↔ Maximal (· ∈ V) x := by
    rw [← maximal_mem_boundary_iff_of_grade_lt (α := α) hn, h,
      maximal_mem_boundary_iff_of_grade_lt hn]
  refine boundary_congr (Set.ext fun x => ?_) fun x hn => ?_
  · rw [mem_facesIn_sup_iff, ← hf]
    exact ⟨fun ⟨hx, hU, hV⟩ => hx.elim hU hV, fun hx => ⟨Or.inl hx.1, fun _ => hx, fun _ => hx⟩⟩
  · rw [LowerSet.maximal_mem_sup_iff, ← hm x hn]
    exact ⟨fun ⟨hx, hU, hV⟩ => hx.elim hU hV,
      fun hx => ⟨Or.inl hx.prop, fun _ => hx, fun _ => hx⟩⟩

theorem boundary_le_boundary_sup (hUV : U ⊓ V ≤ P.boundary V n α)
    (hd : ∀ x ∈ U ⊓ V, grade ℕ x < n) : P.boundary U n α ≤ P.boundary (U ⊔ V) n α := by
  intro x hx
  obtain ⟨z, hz, hxz⟩ := mem_boundary.1 hx
  have hzU : z ∈ U := hz.elim (fun h => h.1) fun h => h.1.prop
  by_cases hzV : z ∈ V
  swap
  · exact mem_boundary_sup_of_notMem hz hzV hxz
  have hzn := hd z ⟨hzU, hzV⟩
  have hzm : Maximal (· ∈ U) z := (hz.resolve_left fun h => hzn.ne h.2.1).1
  obtain ⟨w, hw, hzw⟩ := mem_boundary.1 (hUV ⟨hzU, hzV⟩)
  by_cases hwU : w ∈ U
  · obtain rfl := hzm.eq_of_le hwU hzw
    have hwm : Maximal (· ∈ V) z := (hw.resolve_left fun h => hzn.ne h.2.1).1
    exact mem_boundary_of_maximal
      (LowerSet.maximal_mem_sup_iff.2 ⟨Or.inl hzU, fun _ => hzm, fun _ => hwm⟩) hzn hxz
  · exact sup_comm V U ▸ mem_boundary_sup_of_notMem hw hwU (hxz.trans hzw)

theorem boundary_Iic (hx : grade ℕ x = n + 1) (α : Bool) :
    P.boundary (LowerSet.Iic x) n α = lowerClosure (P.faces α x) := by
  refine SetLike.ext fun y => ?_
  rw [mem_boundary, mem_lowerClosure]
  refine exists_congr fun z => and_congr_left fun _ => ⟨?_, fun ⟨hzx, hz⟩ => Or.inl ?_⟩
  · rintro (⟨hzx, hzn, hd⟩ | ⟨hz, hzn⟩)
    · have hzx' : z ⋖ x := GradeOrder.covBy_of_le_of_grade_eq_add_one hzx (by rw [hzn, hx])
      refine ⟨hzx', ?_⟩
      by_contra ho
      exact disjoint_left.1 hd ⟨hzx', Bool.eq_not_iff.2 ho⟩ (le_refl x)
    · obtain rfl := hz.eq_of_le (le_refl x) hz.prop
      omega
  · have hzn : grade ℕ z + 1 = grade ℕ x := Nat.covBy_iff_add_one_eq.1 (hzx.grade ℕ)
    refine ⟨hzx.le, by omega, disjoint_left.2 fun c hc hcx => ?_⟩
    obtain rfl : c = x := GradeOrder.eq_of_le_of_grade_le hcx
      ((Nat.covBy_iff_add_one_eq.1 (hc.1.grade ℕ)).symm ▸ hzn.ge)
    simp [hz] at hc

theorem bdry_eq_bot (h : krullDim U ≤ 0) (α : Bool) : P.bdry U α = ⊥ :=
  iSup_eq_bot.2 fun m => iSup_eq_bot.2 fun hm => absurd (hm ▸ h) (by simp)

theorem bdryFull_eq_bot (h : krullDim U ≤ 0) : P.bdryFull U = ⊥ := by
  rw [bdryFull, bdry_eq_bot h, bdry_eq_bot h, sup_bot_eq]

theorem grade_lt_of_mem_bdry (hx : x ∈ P.bdry U α) : (grade ℕ x : WithBot ℕ∞) < krullDim U := by
  obtain ⟨m, hm, hxm⟩ : ∃ m : ℕ, krullDim U = m + 1 ∧ x ∈ P.boundary U m α := by
    simpa [bdry] using hx
  rw [hm]
  exact_mod_cast Nat.lt_succ_of_le (grade_le_of_mem_boundary hxm)

theorem bdry_Iic (x : P) (α : Bool) : P.bdry (LowerSet.Iic x) α = lowerClosure (P.faces α x) := by
  cases hx : grade ℕ x with
  | zero =>
    have hf : P.faces α x = ∅ := eq_empty_of_forall_notMem fun y hy => by
      have := Nat.covBy_iff_add_one_eq.1 (hy.1.grade ℕ)
      omega
    rw [bdry_eq_bot (by rw [LowerSet.krullDim_Iic, hx]; rfl), hf, lowerClosure_empty]
  | succ n =>
    rw [bdry_eq_boundary (by rw [LowerSet.krullDim_Iic, hx]; norm_cast), boundary_Iic hx]

theorem mem_bdry_Iic_of_covBy {y : P} (h : y ⋖ x) : y ∈ P.bdry (LowerSet.Iic x) (P.orient h) := by
  rw [bdry_Iic]
  exact subset_lowerClosure ⟨h, rfl⟩

theorem mem_faces_of_mem_bdry_Iic {y : P} (hy : y ∈ P.bdry (LowerSet.Iic x) α)
    (hd : grade ℕ y + 1 = grade ℕ x) : y ∈ P.faces α x := by
  rw [bdry_Iic] at hy
  obtain ⟨f, hf, hyf⟩ := mem_lowerClosure.1 hy
  have hdf := Nat.covBy_iff_add_one_eq.1 (hf.1.grade ℕ)
  rwa [GradeOrder.eq_of_le_of_grade_le hyf (by omega)]

theorem coe_bdry_Iic_sup (x : P) :
    ((P.bdry (LowerSet.Iic x) false ⊔ P.bdry (LowerSet.Iic x) true : LowerSet P) : Set P) =
      Set.Iio x := by
  ext y
  rw [LowerSet.coe_sup, bdry_Iic, bdry_Iic, Set.mem_union, SetLike.mem_coe, SetLike.mem_coe,
    mem_lowerClosure, mem_lowerClosure, Set.mem_Iio]
  constructor
  · rintro (⟨z, hz, hyz⟩ | ⟨z, hz, hyz⟩)
    · exact hyz.trans_lt hz.1.lt
    · exact hyz.trans_lt hz.1.lt
  · intro hy
    obtain ⟨z, hyz, hz⟩ := exists_le_covBy_of_lt hy
    cases ho : P.orient hz
    · exact Or.inl ⟨z, ⟨hz, ho⟩, hyz⟩
    · exact Or.inr ⟨z, ⟨hz, ho⟩, hyz⟩

theorem bdry_Iic_lt (x : P) (α : Bool) : P.bdry (LowerSet.Iic x) α < LowerSet.Iic x := by
  have hlt (y : P) (hy : y ∈ P.bdry (LowerSet.Iic x) α) : y < x := by
    refine (Set.ext_iff.1 (coe_bdry_Iic_sup x) y).1 ?_
    cases α
    · exact Or.inl hy
    · exact Or.inr hy
  refine lt_of_le_of_ne (fun y hy => (hlt y hy).le) fun h => lt_irrefl x (hlt x ?_)
  rw [h]
  exact LowerSet.mem_Iic_iff.2 le_rfl

end Atoms.Molecule.OGP
