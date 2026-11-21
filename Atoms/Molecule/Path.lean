import Atoms.Molecule.Vertex

universe u

open Order

namespace Atoms.Molecule.OGP

variable {P : OGP.{u}} {U V : LowerSet P}

theorem mem_faces_iff_boundary_Iic_eq {e w : P} (he : IsMoleculeIn P (LowerSet.Iic e))
    (he1 : grade ℕ e = 1) (α : Bool) :
    w ∈ P.faces α e ↔ P.boundary (LowerSet.Iic e) 0 α = LowerSet.Iic w := by
  obtain ⟨x, hx, hbx⟩ := exists_boundary_zero_eq_Iic he α
  have hb : P.boundary (LowerSet.Iic e) 0 α = lowerClosure (P.faces α e) := boundary_Iic he1 α
  have hgrade {z : P} (hz : z ∈ P.faces α e) : grade ℕ z = 0 := by
    have := Nat.covBy_iff_add_one_eq.1 (hz.1.grade ℕ)
    omega
  rw [hbx, LowerSet.Iic_inj]
  constructor
  · intro hw
    have hwx : w ∈ P.boundary (LowerSet.Iic e) 0 α := hb ▸ subset_lowerClosure hw
    rw [hbx, LowerSet.mem_Iic_iff] at hwx
    exact (hx hwx).antisymm hwx
  · rintro rfl
    have hxf : x ∈ lowerClosure (P.faces α e) := by
      rw [← hb, hbx]
      exact LowerSet.mem_Iic_iff.2 le_rfl
    obtain ⟨z, hz, hxz⟩ := mem_lowerClosure.1 hxf
    rwa [GradeOrder.eq_of_le_of_grade_le hxz (by rw [hgrade hz]; exact Nat.zero_le _)]

private theorem le_iff_of_grade_eq_one {e x : P} (he : IsMoleculeIn P (LowerSet.Iic e))
    (he1 : grade ℕ e = 1) :
    x ≤ e ↔ x = e ∨ ∃ β, P.boundary (LowerSet.Iic e) 0 β = LowerSet.Iic x := by
  constructor
  · intro hxe
    rcases hxe.eq_or_lt with rfl | hlt
    · exact Or.inl rfl
    · have h0 : grade ℕ x = 0 := by
        have := grade_strictMono (𝕆 := ℕ) hlt
        omega
      have hc : x ⋖ e := GradeOrder.covBy_of_le_of_grade_eq_add_one hxe (by omega)
      exact Or.inr ⟨P.orient hc, (mem_faces_iff_boundary_Iic_eq he he1 _).1 ⟨hc, rfl⟩⟩
  · rintro (rfl | ⟨β, h⟩)
    · exact le_rfl
    · exact LowerSet.mem_Iic_iff.1 (boundary_le _ 0 β (h ▸ LowerSet.mem_Iic_iff.2 le_rfl))

private theorem grade_le_one (hd : krullDim U ≤ 1) {x : P} (hx : x ∈ U) : grade ℕ x ≤ 1 :=
  krullDim_le_coe_iff.1 (by exact_mod_cast hd) (⟨x, hx⟩ : U)

private theorem exists_grade_eq_one (hVd : krullDim V = 1) : ∃ x ∈ V, grade ℕ x = 1 := by
  by_contra hne
  push Not at hne
  have h0 : krullDim V ≤ (0 : ℕ) := krullDim_le_coe_iff.2 fun ⟨x, hx⟩ => by
    have := grade_le_one hVd.le hx
    have := hne x hx
    exact (by omega : grade ℕ x ≤ 0)
  rw [hVd] at h0
  exact absurd (by exact_mod_cast h0 : (1 : ℕ) ≤ 0) (by omega)

private structure PathData (U : LowerSet P) (n : ℕ) (v e : ℕ → P) : Prop where
  face : ∀ j < n, ∀ β : Bool, v (j + β.toNat) ∈ P.faces β (e j)
  injOn_v : Set.InjOn v (Set.Iic n)
  injOn_e : Set.InjOn e (Set.Iio n)
  mem_e : ∀ x, x ∈ U ∧ grade ℕ x = 1 ↔ ∃ j < n, e j = x
  mem_v : ∀ x, x ∈ U ∧ grade ℕ x = 0 ↔ ∃ j ≤ n, v j = x
  source : P.boundary U 0 false = LowerSet.Iic (v 0)
  target : P.boundary U 0 true = LowerSet.Iic (v n)

namespace PathData

variable {n : ℕ} {v e : ℕ → P}

private theorem mem_e_of_lt (h : PathData U n v e) {j : ℕ} (hj : j < n) :
    e j ∈ U ∧ grade ℕ (e j) = 1 :=
  (h.mem_e _).2 ⟨j, hj, rfl⟩

private theorem mem_v_of_le (h : PathData U n v e) {j : ℕ} (hj : j ≤ n) :
    v j ∈ U ∧ grade ℕ (v j) = 0 :=
  (h.mem_v _).2 ⟨j, hj, rfl⟩

private theorem isMin_v (h : PathData U n v e) {j : ℕ} (hj : j ≤ n) : IsMin (v j) :=
  grade_eq_zero_iff.1 (h.mem_v_of_le hj).2

private theorem isMoleculeIn_Iic_e (h : PathData U n v e) (hU : IsMoleculeIn P U) {j : ℕ}
    (hj : j < n) : IsMoleculeIn P (LowerSet.Iic (e j)) :=
  (hU.isAtomIn_Iic (h.mem_e_of_lt hj).1).isMoleculeIn

private theorem boundary_Iic_e (h : PathData U n v e) (hU : IsMoleculeIn P U) {j : ℕ} (hj : j < n)
    (β : Bool) : P.boundary (LowerSet.Iic (e j)) 0 β = LowerSet.Iic (v (j + β.toNat)) :=
  (mem_faces_iff_boundary_Iic_eq (h.isMoleculeIn_Iic_e hU hj) (h.mem_e_of_lt hj).2 β).1
    (h.face j hj β)

private theorem mem_faces_iff (h : PathData U n v e) (hU : IsMoleculeIn P U) {j : ℕ} (hj : j < n)
    (β : Bool) {w : P} : w ∈ P.faces β (e j) ↔ w = v (j + β.toNat) := by
  rw [mem_faces_iff_boundary_Iic_eq (h.isMoleculeIn_Iic_e hU hj) (h.mem_e_of_lt hj).2 β,
    h.boundary_Iic_e hU hj β, LowerSet.Iic_inj, eq_comm]

private theorem le_e_iff (h : PathData U n v e) (hU : IsMoleculeIn P U) {j : ℕ} (hj : j < n)
    {x : P} : x ≤ e j ↔ x = e j ∨ x = v j ∨ x = v (j + 1) := by
  rw [le_iff_of_grade_eq_one (h.isMoleculeIn_Iic_e hU hj) (h.mem_e_of_lt hj).2, Bool.exists_bool,
    h.boundary_Iic_e hU hj, h.boundary_Iic_e hU hj, LowerSet.Iic_inj, LowerSet.Iic_inj]
  simp only [Bool.toNat_false, Bool.toNat_true, Nat.add_zero, eq_comm (a := v _)]

private theorem eq_of_mem_cofaces (h : PathData U n v e) (hU : IsMoleculeIn P U)
    (hd : krullDim U ≤ 1) (β : Bool) {w x y : P} (hx : x ∈ U) (hy : y ∈ U)
    (hwx : x ∈ P.cofaces β w) (hwy : y ∈ P.cofaces β w) : x = y := by
  have hedge {z : P} (hz : z ∈ U) (hwz : z ∈ P.cofaces β w) :
      ∃ j < n, e j = z ∧ w = v (j + β.toNat) := by
    have h1 : grade ℕ z = 1 := by
      have := grade_strictMono (𝕆 := ℕ) hwz.1.lt
      have := grade_le_one hd hz
      omega
    obtain ⟨j, hj, rfl⟩ := (h.mem_e z).1 ⟨hz, h1⟩
    exact ⟨j, hj, rfl, (h.mem_faces_iff hU hj β).1 hwz⟩
  obtain ⟨j, hj, rfl, hwj⟩ := hedge hx hwx
  obtain ⟨k, hk, rfl, hwk⟩ := hedge hy hwy
  have := Bool.toNat_le β
  have hjk := h.injOn_v (Set.mem_Iic.2 (by omega : j + β.toNat ≤ n))
    (Set.mem_Iic.2 (by omega : k + β.toNat ≤ n)) (hwj.symm.trans hwk)
  rw [show j = k by omega]

end PathData

private theorem pathData_Iic_of_isMin {x : P} (hx : IsMin x) :
    PathData (LowerSet.Iic x) 0 (fun _ => x) (fun _ => x) where
  face j hj := absurd hj (Nat.not_lt_zero j)
  injOn_v a ha b hb _ := by
    rw [Set.mem_Iic] at ha hb
    omega
  injOn_e a ha := absurd (Set.mem_Iio.1 ha) (Nat.not_lt_zero a)
  mem_e y := by
    refine ⟨fun ⟨hy, hy1⟩ => ?_, fun ⟨j, hj, _⟩ => absurd hj (Nat.not_lt_zero j)⟩
    have hy' : y = x := (hx (LowerSet.mem_Iic_iff.1 hy)).antisymm' (LowerSet.mem_Iic_iff.1 hy)
    rw [hy', grade_eq_zero_iff.2 hx] at hy1
    exact absurd hy1 zero_ne_one
  mem_v y := by
    refine ⟨fun ⟨hy, _⟩ => ⟨0, le_rfl, (hx (LowerSet.mem_Iic_iff.1 hy)).antisymm
      (LowerSet.mem_Iic_iff.1 hy)⟩, ?_⟩
    rintro ⟨_, _, rfl⟩
    exact ⟨LowerSet.mem_Iic_iff.2 le_rfl, grade_eq_zero_iff.2 hx⟩
  source := boundary_Iic_of_isMin hx 0 false
  target := boundary_Iic_of_isMin hx 0 true

private theorem exists_pathData_Iic_of_grade_eq_one {t : P}
    (ht : IsMoleculeIn P (LowerSet.Iic t)) (h1 : grade ℕ t = 1) :
    ∃ v, PathData (LowerSet.Iic t) 1 v (fun _ => t) := by
  obtain ⟨a, ha, hba⟩ := exists_boundary_zero_eq_Iic ht false
  obtain ⟨b, hb, hbb⟩ := exists_boundary_zero_eq_Iic ht true
  have hab : a ≠ b := by
    intro hab
    have hmem : a ∈ P.boundary (LowerSet.Iic t) 0 false ⊓ P.boundary (LowerSet.Iic t) 0 true := by
      rw [hba, hbb, hab]
      exact ⟨LowerSet.mem_Iic_iff.2 le_rfl, LowerSet.mem_Iic_iff.2 le_rfl⟩
    rw [(IsAtomIn.isRound ⟨ht, t, rfl⟩).inf_boundary_zero
      (by rw [LowerSet.krullDim_Iic, h1]; exact_mod_cast Nat.one_pos)] at hmem
    simp at hmem
  let v : ℕ → P := fun j => if j = 0 then a else b
  have hv (β : Bool) : P.boundary (LowerSet.Iic t) 0 β = LowerSet.Iic (v β.toNat) := by
    cases β
    · simpa [v] using hba
    · simpa [v] using hbb
  have hvmem (β : Bool) : v β.toNat ∈ LowerSet.Iic t ∧ grade ℕ (v β.toNat) = 0 := by
    have hβ : v β.toNat ∈ P.boundary (LowerSet.Iic t) 0 β := by
      rw [hv]
      exact LowerSet.mem_Iic_iff.2 le_rfl
    refine ⟨boundary_le _ 0 β hβ, grade_eq_zero_iff.2 ?_⟩
    cases β
    · simpa [v] using ha
    · simpa [v] using hb
  have hbool {j : ℕ} (hj : j ≤ 1) : ∃ β : Bool, β.toNat = j := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hj with rfl | rfl
    exacts [⟨false, rfl⟩, ⟨true, rfl⟩]
  refine ⟨v, fun j hj β => ?_, fun i hi j hj hij => ?_, fun i hi j hj _ => ?_, fun x => ?_,
    fun x => ?_, ?_, ?_⟩
  · obtain rfl : j = 0 := by omega
    rw [zero_add]
    exact (mem_faces_iff_boundary_Iic_eq ht h1 β).2 (hv β)
  · rw [Set.mem_Iic] at hi hj
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hi with rfl | rfl <;>
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hj with rfl | rfl
    · rfl
    · exact absurd hij hab
    · exact absurd hij.symm hab
    · rfl
  · rw [Set.mem_Iio] at hi hj
    omega
  · refine ⟨fun ⟨hx, hx1⟩ => ⟨0, Nat.one_pos, GradeOrder.eq_of_le_of_grade_le
      (LowerSet.mem_Iic_iff.1 hx) (by rw [h1, hx1]) |>.symm⟩, ?_⟩
    rintro ⟨_, _, rfl⟩
    exact ⟨LowerSet.mem_Iic_iff.2 le_rfl, h1⟩
  · refine ⟨fun ⟨hx, hx0⟩ => ?_, ?_⟩
    · rcases (le_iff_of_grade_eq_one ht h1).1 (LowerSet.mem_Iic_iff.1 hx) with rfl | ⟨β, hβ⟩
      · rw [h1] at hx0
        exact absurd hx0 one_ne_zero
      · rw [hv, LowerSet.Iic_inj] at hβ
        exact ⟨β.toNat, Bool.toNat_le β, hβ⟩
    · rintro ⟨j, hj, rfl⟩
      obtain ⟨β, rfl⟩ := hbool hj
      exact hvmem β
  · exact hv false
  · exact hv true

private theorem PathData.paste {W : LowerSet P} (hp : P.IsPastingIn 0 V W U) {n₁ n₂ : ℕ}
    {v₁ e₁ v₂ e₂ : ℕ → P} (h₁ : PathData V n₁ v₁ e₁) (h₂ : PathData W n₂ v₂ e₂) :
    ∃ v e, PathData U (n₁ + n₂) v e ∧ (∀ j ≤ n₁, v j = v₁ j) ∧ (∀ j ≤ n₂, v (n₁ + j) = v₂ j) ∧
      (∀ j < n₁, e j = e₁ j) ∧ (∀ j < n₂, e (n₁ + j) = e₂ j) := by
  have hinf : ∀ x, x ∈ V → x ∈ W → x ≤ v₁ n₁ := fun x hxV hxW => by
    have hx : x ∈ V ⊓ W := ⟨hxV, hxW⟩
    rw [hp.inf_eq_output, h₁.target] at hx
    exact LowerSet.mem_Iic_iff.1 hx
  have hmid : v₁ n₁ = v₂ 0 := by
    rw [← LowerSet.Iic_inj, ← h₁.target, ← h₂.source, ← hp.inf_eq_output, hp.inf_eq_input]
  have hcross {i j : ℕ} (hi : i ≤ n₁) (hj : j ≤ n₂) (hij : v₁ i = v₂ j) : i = n₁ ∧ j = 0 := by
    have hle := hinf _ (h₁.mem_v_of_le hi).1 (hij ▸ (h₂.mem_v_of_le hj).1)
    have heq := GradeOrder.eq_of_le_of_grade_le hle
      (by rw [(h₁.mem_v_of_le le_rfl).2]; exact Nat.zero_le _)
    exact ⟨h₁.injOn_v (Set.mem_Iic.2 hi) (Set.mem_Iic.2 le_rfl) heq,
      h₂.injOn_v (Set.mem_Iic.2 hj) (Set.mem_Iic.2 (Nat.zero_le _)) (hij.symm.trans
        (heq.trans hmid))⟩
  let v : ℕ → P := fun j => if j ≤ n₁ then v₁ j else v₂ (j - n₁)
  let e : ℕ → P := fun j => if j < n₁ then e₁ j else e₂ (j - n₁)
  have hv₁ (j : ℕ) (hj : j ≤ n₁) : v j = v₁ j := if_pos hj
  have hv₂ (j : ℕ) (hj : n₁ ≤ j) : v j = v₂ (j - n₁) := by
    rcases hj.eq_or_lt with rfl | hlt
    · rw [hv₁ _ le_rfl, Nat.sub_self, hmid]
    · exact if_neg (not_le.2 hlt)
  have he₁ (j : ℕ) (hj : j < n₁) : e j = e₁ j := if_pos hj
  have he₂ (j : ℕ) (hj : n₁ ≤ j) : e j = e₂ (j - n₁) := if_neg (not_lt.2 hj)
  refine ⟨v, e, ⟨fun k hk β => ?_, fun i hi j hj hij => ?_, fun i hi j hj hij => ?_, fun x => ?_,
    fun x => ?_, ?_, ?_⟩, hv₁, fun j _ => by rw [hv₂ _ (by omega), Nat.add_sub_cancel_left], he₁,
    fun j _ => by rw [he₂ _ (by omega), Nat.add_sub_cancel_left]⟩
  · have := Bool.toNat_le β
    by_cases hk₁ : k < n₁
    · rw [he₁ k hk₁, hv₁ _ (by omega)]
      exact h₁.face k hk₁ β
    · rw [he₂ k (by omega), hv₂ _ (by omega), show k + β.toNat - n₁ = k - n₁ + β.toNat by omega]
      exact h₂.face _ (by omega) β
  · rw [Set.mem_Iic] at hi hj
    rcases le_total i n₁ with hi₁ | hi₁ <;> rcases le_total j n₁ with hj₁ | hj₁
    · rw [hv₁ i hi₁, hv₁ j hj₁] at hij
      exact h₁.injOn_v (Set.mem_Iic.2 hi₁) (Set.mem_Iic.2 hj₁) hij
    · rw [hv₁ i hi₁, hv₂ j hj₁] at hij
      have := hcross hi₁ (by omega) hij
      omega
    · rw [hv₂ i hi₁, hv₁ j hj₁] at hij
      have := hcross hj₁ (by omega) hij.symm
      omega
    · rw [hv₂ i hi₁, hv₂ j hj₁] at hij
      have := h₂.injOn_v (Set.mem_Iic.2 (by omega)) (Set.mem_Iic.2 (by omega)) hij
      omega
  · rw [Set.mem_Iio] at hi hj
    have hne {i j : ℕ} (hi : i < n₁) (hj : j < n₂) : e₁ i ≠ e₂ j := fun h => by
      have hle := grade_mono (𝕆 := ℕ) (hinf _ (h₁.mem_e_of_lt hi).1 (h ▸ (h₂.mem_e_of_lt hj).1))
      rw [(h₁.mem_e_of_lt hi).2, (h₁.mem_v_of_le le_rfl).2] at hle
      exact absurd hle (by omega)
    rcases lt_or_ge i n₁ with hi₁ | hi₁ <;> rcases lt_or_ge j n₁ with hj₁ | hj₁
    · rw [he₁ i hi₁, he₁ j hj₁] at hij
      exact h₁.injOn_e (Set.mem_Iio.2 hi₁) (Set.mem_Iio.2 hj₁) hij
    · rw [he₁ i hi₁, he₂ j hj₁] at hij
      exact absurd hij (hne hi₁ (by omega))
    · rw [he₂ i hi₁, he₁ j hj₁] at hij
      exact absurd hij.symm (hne hj₁ (by omega))
    · rw [he₂ i hi₁, he₂ j hj₁] at hij
      have := h₂.injOn_e (Set.mem_Iio.2 (by omega)) (Set.mem_Iio.2 (by omega)) hij
      omega
  · rw [← hp.sup_eq, LowerSet.mem_sup_iff, or_and_right, h₁.mem_e x, h₂.mem_e x]
    constructor
    · rintro (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩)
      · exact ⟨j, by omega, he₁ j hj⟩
      · exact ⟨n₁ + j, by omega, by rw [he₂ _ (by omega), Nat.add_sub_cancel_left]⟩
    · rintro ⟨j, hj, rfl⟩
      by_cases hj₁ : j < n₁
      · exact Or.inl ⟨j, hj₁, (he₁ j hj₁).symm⟩
      · exact Or.inr ⟨j - n₁, by omega, (he₂ j (by omega)).symm⟩
  · rw [← hp.sup_eq, LowerSet.mem_sup_iff, or_and_right, h₁.mem_v x, h₂.mem_v x]
    constructor
    · rintro (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩)
      · exact ⟨j, by omega, hv₁ j hj⟩
      · exact ⟨n₁ + j, by omega, by rw [hv₂ _ (by omega), Nat.add_sub_cancel_left]⟩
    · rintro ⟨j, hj, rfl⟩
      by_cases hj₁ : j ≤ n₁
      · exact Or.inl ⟨j, hj₁, (hv₁ j hj₁).symm⟩
      · exact Or.inr ⟨j - n₁, by omega, (hv₂ j (by omega)).symm⟩
  · rw [hp.boundary_input, h₁.source, hv₁ 0 (Nat.zero_le _)]
  · rw [hp.boundary_output, h₂.target, hv₂ _ (by omega), Nat.add_sub_cancel_left]

private theorem exists_pathData (hU : IsMoleculeIn P U) (hd : krullDim U ≤ 1) :
    ∃ n v e, PathData U n v e := by
  induction hU with
  | point x hx => exact ⟨0, _, _, pathData_Iic_of_isMin hx⟩
  | atom t hround hbdry _ =>
    have h1 : grade ℕ t ≤ 1 := by
      rw [LowerSet.krullDim_Iic] at hd
      exact_mod_cast hd
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h1 with h0 | h1
    · exact ⟨0, _, _, pathData_Iic_of_isMin (grade_eq_zero_iff.1 h0)⟩
    · obtain ⟨v, hv⟩ := exists_pathData_Iic_of_grade_eq_one (.atom t hround hbdry) h1
      exact ⟨1, v, _, hv⟩
  | paste k V W U hp _ _ hk ihV ihW =>
    have hV : krullDim V ≤ 1 := (LowerSet.krullDim_mono hp.left_le).trans hd
    have hW : krullDim W ≤ 1 := (LowerSet.krullDim_mono hp.right_le).trans hd
    obtain rfl : k = 0 := by
      have hk1 : (k : WithBot ℕ∞) < 1 := (hk.trans_le (min_le_left _ _)).trans_le hV
      have : k < 1 := by exact_mod_cast hk1
      omega
    obtain ⟨n₁, v₁, e₁, h₁⟩ := ihV hV
    obtain ⟨n₂, v₂, e₂, h₂⟩ := ihW hW
    obtain ⟨v, e, h, -⟩ := PathData.paste hp h₁ h₂
    exact ⟨_, v, e, h⟩

theorem existsUnique_edge_of_krullDim_le_one (hU : IsMoleculeIn P U) (hd : krullDim U ≤ 1)
    {v : P} (hv : v ∈ U) (hv0 : grade ℕ v = 0) (α : Bool)
    (hne : P.boundary U 0 (!α) ≠ LowerSet.Iic v) :
    ∃! e : P, e ∈ U ∧ ∃ h : v ⋖ e, P.orient h = α := by
  rw [Ne, boundary_zero_eq_Iic_iff hU hv hv0] at hne
  push Not at hne
  obtain ⟨e, he, hc, ho⟩ := hne
  obtain ⟨n, vs, es, h⟩ := exists_pathData hU hd
  refine ⟨e, ⟨he, hc, by simpa using ho⟩, fun e' ⟨he', hc'⟩ => ?_⟩
  exact h.eq_of_mem_cofaces hU hd α he' he hc' ⟨hc, by simpa using ho⟩

private def findUnique? {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p] : Option α :=
  if h : (Finset.univ.filter p).card = 1 then
    some (Fintype.choose p ((Fintype.existsUnique_iff_card_one p).2 h))
  else none

private theorem findUnique?_eq_some {α : Type*} [Fintype α] {p : α → Prop} [DecidablePred p]
    {a : α} (ha : p a) (hu : ∀ b, p b → b = a) : findUnique? p = some a := by
  have h : ∃! b, p b := ⟨a, ha, hu⟩
  rw [findUnique?, dif_pos ((Fintype.existsUnique_iff_card_one p).1 h)]
  exact congrArg some (hu _ (Fintype.choose_spec p _))

private theorem findUnique?_eq_none {α : Type*} [Fintype α] {p : α → Prop} [DecidablePred p]
    (h : ∀ b, ¬ p b) : findUnique? p = none := by
  rw [findUnique?, dif_neg]
  intro hc
  obtain ⟨a, ha, -⟩ := (Fintype.existsUnique_iff_card_one p).2 hc
  exact h a ha

section EdgeList

variable [Fintype P] [DecidableLE P]

def walkEdges (U : LowerSet P) [DecidablePred (· ∈ U)] (v : P) : ℕ → List P
  | 0 => []
  | n + 1 =>
    match findUnique? (fun e => e ∈ U ∧ e ∈ P.cofaces false v) with
    | none => []
    | some e =>
      match findUnique? (· ∈ P.faces true e) with
      | none => [e]
      | some w => e :: walkEdges U w n

def edgeList (U : LowerSet P) [DecidablePred (· ∈ U)] : List P :=
  match findUnique? (· ∈ P.boundary U 0 false) with
  | none => []
  | some v => walkEdges U v (Fintype.card P)

variable [DecidablePred (· ∈ U)]

namespace PathData

variable {n : ℕ} {v e : ℕ → P}

private theorem walkEdges_eq (h : PathData U n v e) (hU : IsMoleculeIn P U)
    (hd : krullDim U ≤ 1) (m : ℕ) :
    ∀ j ≤ n, n - j ≤ m → walkEdges U (v j) m = (List.range' j (n - j)).map e := by
  induction m with
  | zero =>
    intro j _ hm
    rw [walkEdges, show n - j = 0 by omega]
    rfl
  | succ m ih =>
    intro j hj hm
    rcases hj.lt_or_eq with hj | rfl
    · have hin : e j ∈ P.cofaces false (v j) := by simpa using h.face j hj false
      have hfe : findUnique? (fun x => x ∈ U ∧ x ∈ P.cofaces false (v j)) = some (e j) :=
        findUnique?_eq_some ⟨(h.mem_e_of_lt hj).1, hin⟩
          fun x ⟨hx, hc⟩ => h.eq_of_mem_cofaces hU hd false hx (h.mem_e_of_lt hj).1 hc hin
      have hfw : findUnique? (· ∈ P.faces true (e j)) = some (v (j + 1)) :=
        findUnique?_eq_some (h.face j hj true) fun w hw => (h.mem_faces_iff hU hj true).1 hw
      simp only [walkEdges, hfe, hfw]
      rw [ih (j + 1) (by omega) (by omega), show n - j = n - (j + 1) + 1 by omega,
        List.range'_succ, List.map_cons]
    · have hout := (boundary_zero_eq_Iic_iff hU (h.mem_v_of_le le_rfl).1 (h.mem_v_of_le le_rfl).2
        true).1 h.target
      have hnone : findUnique? (fun x => x ∈ U ∧ x ∈ P.cofaces false (v j)) = none :=
        findUnique?_eq_none fun x ⟨hx, hc, ho⟩ => by simp [hout x hx hc] at ho
      simp only [walkEdges, hnone, Nat.sub_self, List.range'_zero, List.map_nil]

private theorem edgeList_eq (h : PathData U n v e) (hU : IsMoleculeIn P U)
    (hd : krullDim U ≤ 1) : edgeList U = (List.range n).map e := by
  have hv : findUnique? (· ∈ P.boundary U 0 false) = some (v 0) := by
    refine findUnique?_eq_some (by rw [h.source]; exact LowerSet.mem_Iic_iff.2 le_rfl)
      fun x hx => ?_
    rw [h.source, LowerSet.mem_Iic_iff] at hx
    exact hx.antisymm (h.isMin_v (Nat.zero_le n) hx)
  have hcard : n ≤ Fintype.card P := by
    classical
    have := Finset.card_le_univ ((Finset.range n).image e)
    rwa [Finset.card_image_of_injOn (by rw [Finset.coe_range]; exact h.injOn_e),
      Finset.card_range] at this
  simp only [edgeList, hv]
  rw [h.walkEdges_eq hU hd _ 0 (Nat.zero_le n) (by omega), Nat.sub_zero, List.range_eq_range']

end PathData

theorem mem_edgeList_iff (hU : IsMoleculeIn P U) (hd : krullDim U ≤ 1) {x : P} :
    x ∈ edgeList U ↔ x ∈ U ∧ grade ℕ x = 1 := by
  obtain ⟨n, v, e, h⟩ := exists_pathData hU hd
  rw [h.edgeList_eq hU hd, h.mem_e x, List.mem_map]
  simp only [List.mem_range]

theorem edgeList_ne_nil (hU : IsMoleculeIn P U) (hd : krullDim U = 1) : edgeList U ≠ [] := by
  obtain ⟨x, hx, hx1⟩ := exists_grade_eq_one hd
  exact List.ne_nil_of_mem ((mem_edgeList_iff hU hd.le).2 ⟨hx, hx1⟩)

theorem nodup_edgeList (hU : IsMoleculeIn P U) (hd : krullDim U ≤ 1) : (edgeList U).Nodup := by
  obtain ⟨n, v, e, h⟩ := exists_pathData hU hd
  rw [h.edgeList_eq hU hd]
  exact List.nodup_range.map_on fun a ha b hb => h.injOn_e (Set.mem_Iio.2 (List.mem_range.1 ha))
    (Set.mem_Iio.2 (List.mem_range.1 hb))

theorem edgeList_isChain (hU : IsMoleculeIn P U) (hd : krullDim U ≤ 1) :
    (edgeList U).IsChain (fun x y => P.boundary (LowerSet.Iic x) 0 true =
      P.boundary (LowerSet.Iic y) 0 false) := by
  obtain ⟨n, v, e, h⟩ := exists_pathData hU hd
  rw [h.edgeList_eq hU hd, List.isChain_map, List.isChain_range]
  intro j hj
  rw [h.boundary_Iic_e hU (by omega), h.boundary_Iic_e hU (by omega)]
  simp

theorem boundary_Iic_of_mem_head?_edgeList (hU : IsMoleculeIn P U) (hd : krullDim U ≤ 1) {x : P}
    (hx : x ∈ (edgeList U).head?) :
    P.boundary (LowerSet.Iic x) 0 false = P.boundary U 0 false := by
  obtain ⟨n, v, e, h⟩ := exists_pathData hU hd
  rw [h.edgeList_eq hU hd] at hx
  rcases n with _ | m
  · simp at hx
  rw [List.range_succ_eq_map, List.map_cons, List.head?_cons, Option.mem_some_iff] at hx
  rw [← hx, h.boundary_Iic_e hU (Nat.succ_pos m), h.source]
  rfl

theorem boundary_Iic_of_mem_getLast?_edgeList (hU : IsMoleculeIn P U) (hd : krullDim U ≤ 1)
    {x : P} (hx : x ∈ (edgeList U).getLast?) :
    P.boundary (LowerSet.Iic x) 0 true = P.boundary U 0 true := by
  obtain ⟨n, v, e, h⟩ := exists_pathData hU hd
  rw [h.edgeList_eq hU hd] at hx
  rcases n with _ | m
  · simp at hx
  rw [List.range_succ, List.map_append, List.map_singleton, List.getLast?_concat,
    Option.mem_some_iff] at hx
  rw [← hx, h.boundary_Iic_e hU (Nat.lt_succ_self m), h.target]
  rfl

end EdgeList

private def seg (e : ℕ → P) (a b : ℕ) : LowerSet P := lowerClosure (e '' Set.Ico a b)

private theorem seg_add_one (e : ℕ → P) (a : ℕ) : seg e a (a + 1) = LowerSet.Iic (e a) := by
  have : Set.Ico a (a + 1) = {a} :=
    Set.ext fun j => by simp only [Set.mem_Ico, Set.mem_singleton_iff]; omega
  rw [seg, this, Set.image_singleton, lowerClosure_singleton]

namespace PathData

variable {n : ℕ} {v e : ℕ → P}

private theorem mem_seg (h : PathData U n v e) (hU : IsMoleculeIn P U) {a b : ℕ} (hab : a < b)
    (hb : b ≤ n) {x : P} :
    x ∈ seg e a b ↔ (∃ j, a ≤ j ∧ j < b ∧ e j = x) ∨ ∃ j, a ≤ j ∧ j ≤ b ∧ v j = x := by
  rw [seg, mem_lowerClosure]
  constructor
  · rintro ⟨_, ⟨j, ⟨hj₁, hj₂⟩, rfl⟩, hx⟩
    rcases (h.le_e_iff hU (by omega)).1 hx with rfl | rfl | rfl
    · exact Or.inl ⟨j, hj₁, hj₂, rfl⟩
    · exact Or.inr ⟨j, hj₁, by omega, rfl⟩
    · exact Or.inr ⟨j + 1, by omega, by omega, rfl⟩
  · rintro (⟨j, hj₁, hj₂, rfl⟩ | ⟨j, hj₁, hj₂, rfl⟩)
    · exact ⟨e j, ⟨j, ⟨hj₁, hj₂⟩, rfl⟩, le_rfl⟩
    · rcases hj₂.lt_or_eq with hj₂ | rfl
      · exact ⟨e j, ⟨j, ⟨hj₁, hj₂⟩, rfl⟩, (h.le_e_iff hU (by omega)).2 (Or.inr (Or.inl rfl))⟩
      · refine ⟨e (j - 1), ⟨j - 1, ⟨by omega, by omega⟩, rfl⟩, (h.le_e_iff hU (by omega)).2
          (Or.inr (Or.inr ?_))⟩
        rw [Nat.sub_add_cancel (by omega)]

private theorem boundary_seg (h : PathData U n v e) (hU : IsMoleculeIn P U) {a b : ℕ}
    (hab : a < b) (hb : b ≤ n) (α : Bool) :
    P.boundary (seg e a b) 0 α = LowerSet.Iic (v (cond α b a)) := by
  have hα : a ≤ cond α b a ∧ cond α b a ≤ b := by cases α <;> simp <;> omega
  have hvj {j : ℕ} (hj : j ≤ n) : grade ℕ (v j) = 0 := (h.mem_v_of_le hj).2
  have hej {j : ℕ} (hj : j < n) : grade ℕ (e j) = 1 := (h.mem_e_of_lt hj).2
  have hfaces (z : P) : z ∈ P.facesIn (seg e a b) 0 α ↔ z = v (cond α b a) := by
    constructor
    · rintro ⟨hz, hz0, hdisj⟩
      rcases (h.mem_seg hU hab hb).1 hz with ⟨j, -, hj, rfl⟩ | ⟨j, hj₁, hj₂, rfl⟩
      · rw [hej (by omega)] at hz0
        exact absurd hz0 one_ne_zero
      by_contra hne
      have hk : a ≤ j - (!α).toNat ∧ j - (!α).toNat < b ∧ j - (!α).toNat + (!α).toNat = j := by
        have : j ≠ cond α b a := fun h' => hne (by rw [h'])
        cases α <;> simp at this ⊢ <;> omega
      have hc : e (j - (!α).toNat) ∈ P.cofaces (!α) (v j) := by
        have := h.face (j - (!α).toNat) (by omega) (!α)
        rwa [hk.2.2] at this
      exact Set.disjoint_left.1 hdisj hc
        ((h.mem_seg hU hab hb).2 (Or.inl ⟨_, hk.1, hk.2.1, rfl⟩))
    · rintro rfl
      refine ⟨(h.mem_seg hU hab hb).2 (Or.inr ⟨_, hα.1, hα.2, rfl⟩), hvj (by omega),
        Set.disjoint_left.2 fun c hc hcs => ?_⟩
      rcases (h.mem_seg hU hab hb).1 hcs with ⟨j, hj₁, hj₂, rfl⟩ | ⟨j, -, hj, rfl⟩
      · have hv := (h.mem_faces_iff hU (by omega) (!α)).1 hc
        have := h.injOn_v (Set.mem_Iic.2 (by omega)) (Set.mem_Iic.2 (by cases α <;> simp <;> omega))
          hv
        cases α <;> simp at this <;> omega
      · have := grade_strictMono (𝕆 := ℕ) hc.1.lt
        rw [hvj (by omega), hvj (by omega)] at this
        exact absurd this (lt_irrefl 0)
  ext x
  rw [SetLike.mem_coe, mem_boundary, SetLike.mem_coe, LowerSet.mem_Iic_iff]
  constructor
  · rintro ⟨z, hz | ⟨-, hz⟩, hxz⟩
    · rwa [← (hfaces z).1 hz]
    · exact absurd hz (Nat.not_lt_zero _)
  · exact fun hx => ⟨_, Or.inl ((hfaces _).2 rfl), hx⟩

private theorem seg_inf_seg (h : PathData U n v e) (hU : IsMoleculeIn P U) {a b c : ℕ}
    (hab : a < b) (hbc : b < c) (hc : c ≤ n) :
    seg e a b ⊓ seg e b c = LowerSet.Iic (v b) := by
  have hvj {j : ℕ} (hj : j ≤ n) : grade ℕ (v j) = 0 := (h.mem_v_of_le hj).2
  have hej {j : ℕ} (hj : j < n) : grade ℕ (e j) = 1 := (h.mem_e_of_lt hj).2
  ext x
  rw [SetLike.mem_coe, LowerSet.mem_inf_iff, h.mem_seg hU hab (by omega), h.mem_seg hU hbc hc,
    SetLike.mem_coe, LowerSet.mem_Iic_iff]
  constructor
  · rintro ⟨⟨j, -, hj, rfl⟩ | ⟨j, -, hj, rfl⟩, ⟨k, hk, hk', hjk⟩ | ⟨k, hk, hk', hjk⟩⟩
    · have := h.injOn_e (Set.mem_Iio.2 (by omega)) (Set.mem_Iio.2 (by omega)) hjk
      omega
    · have := congrArg (grade ℕ) hjk
      rw [hvj (by omega), hej (by omega)] at this
      exact absurd this zero_ne_one
    · have := congrArg (grade ℕ) hjk
      rw [hvj (by omega), hej (by omega)] at this
      exact absurd this one_ne_zero
    · have := h.injOn_v (Set.mem_Iic.2 (by omega)) (Set.mem_Iic.2 (by omega)) hjk
      rw [show j = b by omega]
  · intro hx
    obtain rfl := hx.antisymm (h.isMin_v (by omega) hx)
    exact ⟨Or.inr ⟨b, hab.le, le_rfl, rfl⟩, Or.inr ⟨b, le_rfl, hbc.le, rfl⟩⟩

private theorem isPastingIn_seg (h : PathData U n v e) (hU : IsMoleculeIn P U) {a b c : ℕ}
    (hab : a < b) (hbc : b < c) (hc : c ≤ n) :
    P.IsPastingIn 0 (seg e a b) (seg e b c) (seg e a c) where
  sup_eq := by rw [seg, seg, seg, ← lowerClosure_union, ← Set.image_union,
    Set.Ico_union_Ico_eq_Ico hab.le hbc.le]
  inf_eq_output := by rw [h.seg_inf_seg hU hab hbc hc, h.boundary_seg hU hab (by omega)]; rfl
  inf_eq_input := by rw [h.seg_inf_seg hU hab hbc hc, h.boundary_seg hU hbc hc]; rfl

private theorem isMoleculeIn_seg (h : PathData U n v e) (hU : IsMoleculeIn P U) {a b : ℕ}
    (hab : a < b) (hb : b ≤ n) : IsMoleculeIn P (seg e a b) := by
  induction b, hab using Nat.le_induction with
  | base =>
    rw [Nat.succ_eq_add_one, seg_add_one]
    exact h.isMoleculeIn_Iic_e hU (by omega)
  | succ b hab ih =>
    exact (h.isPastingIn_seg hU hab (Nat.lt_succ_self b) hb).isMoleculeIn (ih (by omega))
      (by
        rw [seg_add_one]
        exact h.isMoleculeIn_Iic_e hU (by omega))

private theorem seg_zero (h : PathData U n v e) (hU : IsMoleculeIn P U) (hd : krullDim U ≤ 1)
    (hn : 0 < n) : seg e 0 n = U := by
  ext x
  rw [SetLike.mem_coe, SetLike.mem_coe, h.mem_seg hU hn le_rfl]
  constructor
  · rintro (⟨j, -, hj, rfl⟩ | ⟨j, -, hj, rfl⟩)
    exacts [(h.mem_e_of_lt hj).1, (h.mem_v_of_le hj).1]
  · intro hx
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (grade_le_one hd hx) with h0 | h1
    · obtain ⟨j, hj, rfl⟩ := (h.mem_v x).1 ⟨hx, h0⟩
      exact Or.inr ⟨j, Nat.zero_le j, hj, rfl⟩
    · obtain ⟨j, hj, rfl⟩ := (h.mem_e x).1 ⟨hx, h1⟩
      exact Or.inl ⟨j, Nat.zero_le j, hj, rfl⟩

private theorem isSubmoleculeOf_seg (h : PathData U n v e) (hU : IsMoleculeIn P U)
    {a b c d : ℕ} (hab : a ≤ b) (hbc : b < c) (hcd : c ≤ d) (hd : d ≤ n) :
    P.IsSubmoleculeOf (seg e b c) (seg e a d) := by
  have h₁ : P.IsSubmoleculeOf (seg e b c) (seg e b d) := by
    rcases hcd.lt_or_eq with hcd | rfl
    · exact (IsPastingIn.isPastingFactorOf false (h.isMoleculeIn_seg hU hbc (by omega))
        (h.isMoleculeIn_seg hU hcd hd) (h.isPastingIn_seg hU hbc hcd hd)).isSubmoleculeOf
    · exact .refl (h.isMoleculeIn_seg hU hbc hd)
  have h₂ : P.IsSubmoleculeOf (seg e b d) (seg e a d) := by
    rcases hab.lt_or_eq with hab | rfl
    · exact (IsPastingIn.isPastingFactorOf true (h.isMoleculeIn_seg hU (by omega) hd)
        (h.isMoleculeIn_seg hU hab (by omega))
        (h.isPastingIn_seg hU hab (by omega) hd)).isSubmoleculeOf
    · exact .refl (h.isMoleculeIn_seg hU (by omega) hd)
  exact h₁.trans h₂

end PathData

section Segment

variable [Fintype P] [DecidableLE P]

def segment (U : LowerSet P) [DecidablePred (· ∈ U)] (i m : ℕ) : LowerSet P :=
  if m = 0 then
    match (edgeList U)[i]? with
    | some x => P.boundary (LowerSet.Iic x) 0 false
    | none => P.boundary U 0 true
  else lowerClosure {x | ∃ j, i ≤ j ∧ j < i + m ∧ (edgeList U)[j]? = some x}

variable [DecidablePred (· ∈ U)]

namespace PathData

variable {n : ℕ} {v e : ℕ → P}

private theorem length_edgeList (h : PathData U n v e) (hU : IsMoleculeIn P U)
    (hd : krullDim U ≤ 1) : (edgeList U).length = n := by
  rw [h.edgeList_eq hU hd, List.length_map, List.length_range]

private theorem segment_eq_seg (h : PathData U n v e) (hU : IsMoleculeIn P U)
    (hd : krullDim U ≤ 1) {i m : ℕ} (hm : 0 < m) (him : i + m ≤ n) :
    segment U i m = seg e i (i + m) := by
  rw [segment, if_neg hm.ne', seg, h.edgeList_eq hU hd]
  congr 1
  ext x
  simp only [List.getElem?_map, Set.mem_image, Set.mem_Ico]
  constructor
  · rintro ⟨j, hj₁, hj₂, hx⟩
    rw [List.getElem?_range (by omega), Option.map_some, Option.some_inj] at hx
    exact ⟨j, ⟨hj₁, hj₂⟩, hx⟩
  · rintro ⟨j, ⟨hj₁, hj₂⟩, rfl⟩
    exact ⟨j, hj₁, hj₂, by rw [List.getElem?_range (by omega), Option.map_some]⟩

private theorem segment_zero (h : PathData U n v e) (hU : IsMoleculeIn P U)
    (hd : krullDim U ≤ 1) {i : ℕ} (hi : i ≤ n) : segment U i 0 = LowerSet.Iic (v i) := by
  rw [segment, if_pos rfl, h.edgeList_eq hU hd, List.getElem?_map]
  rcases hi.lt_or_eq with hi | rfl
  · rw [List.getElem?_range hi, Option.map_some]
    exact h.boundary_Iic_e hU hi false
  · rw [List.getElem?_eq_none (by simp), Option.map_none, h.target]

end PathData

theorem isPastingIn_segment (hU : IsMoleculeIn P U) (hd : krullDim U ≤ 1) {i : ℕ}
    (hi : 0 < i) (hi' : i < (edgeList U).length) :
    P.IsPastingIn 0 (segment U 0 i) (segment U i ((edgeList U).length - i)) U := by
  obtain ⟨n, v, e, h⟩ := exists_pathData hU hd
  rw [h.length_edgeList hU hd] at hi' ⊢
  rw [h.segment_eq_seg hU hd hi (by omega), h.segment_eq_seg hU hd (by omega) (by omega),
    Nat.zero_add, Nat.add_sub_cancel' hi'.le]
  have hp := h.isPastingIn_seg hU hi hi' le_rfl
  rwa [h.seg_zero hU hd (by omega)] at hp

theorem boundary_segment (hU : IsMoleculeIn P U) (hd : krullDim U ≤ 1) {i m : ℕ} (hm : 0 < m)
    (him : i + m ≤ (edgeList U).length) (α : Bool) :
    P.boundary (segment U i m) 0 α = segment U (i + cond α m 0) 0 := by
  obtain ⟨n, v, e, h⟩ := exists_pathData hU hd
  rw [h.length_edgeList hU hd] at him
  rw [h.segment_eq_seg hU hd hm him, h.boundary_seg hU (by omega) him,
    h.segment_zero hU hd (by cases α <;> simp <;> omega)]
  cases α <;> rfl

theorem isSubmoleculeOf_segment (hU : IsMoleculeIn P U) (hd : krullDim U ≤ 1) {i m : ℕ}
    (hm : 0 < m) (him : i + m ≤ (edgeList U).length) :
    P.IsSubmoleculeOf (segment U i m) U := by
  obtain ⟨n, v, e, h⟩ := exists_pathData hU hd
  rw [h.length_edgeList hU hd] at him
  rw [h.segment_eq_seg hU hd hm him, ← h.seg_zero hU hd (by omega)]
  exact h.isSubmoleculeOf_seg hU (Nat.zero_le i) (by omega) him le_rfl

theorem exists_segment_eq (hU : IsMoleculeIn P U) (hd : krullDim U ≤ 1)
    (hV : IsMoleculeIn P V) (hVd : krullDim V = 1) (hVU : V ≤ U) :
    ∃ i m, 0 < m ∧ i + m ≤ (edgeList U).length ∧ V = segment U i m := by
  obtain ⟨n, v, e, h⟩ := exists_pathData hU hd
  obtain ⟨n', v', e', h'⟩ := exists_pathData hV hVd.le
  obtain ⟨x, hxV, hx1⟩ := exists_grade_eq_one hVd
  obtain ⟨j₀, hj₀, -⟩ := (h'.mem_e x).1 ⟨hxV, hx1⟩
  obtain ⟨i, hi, hie⟩ := (h.mem_e (e' 0)).1 ⟨hVU (h'.mem_e_of_lt (by omega)).1,
    (h'.mem_e_of_lt (by omega)).2⟩
  have hrun : ∀ j < n', i + j < n ∧ e' j = e (i + j) := by
    intro j
    induction j with
    | zero => exact fun _ => ⟨by omega, hie.symm⟩
    | succ j ih =>
      intro hj
      obtain ⟨hij, hej⟩ := ih (by omega)
      have hout : v' (j + 1) = v (i + j + 1) :=
        (h.mem_faces_iff hU hij true).1 (by simpa [hej] using h'.face j (by omega) true)
      obtain ⟨k, hk, hke⟩ := (h.mem_e (e' (j + 1))).1 ⟨hVU (h'.mem_e_of_lt hj).1,
        (h'.mem_e_of_lt hj).2⟩
      have hin : v' (j + 1) = v k := by
        have := (h.mem_faces_iff hU hk false).1 (by simpa [← hke] using h'.face (j + 1) hj false)
        simpa using this
      have hk' := h.injOn_v (Set.mem_Iic.2 hk.le) (Set.mem_Iic.2 (by omega : i + j + 1 ≤ n))
        (hin.symm.trans hout)
      exact ⟨by omega, by rw [← hke, hk', Nat.add_assoc]⟩
  have hn' : 0 < n' := by omega
  have hlen : i + n' ≤ n := by have := (hrun (n' - 1) (by omega)).1; omega
  refine ⟨i, n', hn', by rwa [h.length_edgeList hU hd], ?_⟩
  rw [h.segment_eq_seg hU hd hn' hlen, ← h'.seg_zero hV hVd.le hn', seg, seg]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_Ico]
  constructor
  · rintro ⟨j, ⟨-, hj⟩, rfl⟩
    exact ⟨i + j, ⟨by omega, by omega⟩, (hrun j hj).2.symm⟩
  · rintro ⟨k, ⟨hk₁, hk₂⟩, rfl⟩
    exact ⟨k - i, ⟨Nat.zero_le _, by omega⟩, by rw [(hrun (k - i) (by omega)).2,
      Nat.add_sub_cancel' hk₁]⟩

instance decidableMemSegment (i m : ℕ) : DecidablePred (· ∈ segment U i m) := fun x =>
  if hm : m = 0 then
    match h : (edgeList U)[i]? with
    | some y => decidable_of_iff (x ∈ P.boundary (LowerSet.Iic y) 0 false)
        (by rw [segment, if_pos hm, h])
    | none => decidable_of_iff (x ∈ P.boundary U 0 true) (by rw [segment, if_pos hm, h])
  else
    decidable_of_iff (∃ j ∈ List.range' i m, ∃ y ∈ (edgeList U)[j]?, x ≤ y) (by
      rw [segment, if_neg hm]
      change _ ↔ x ∈ lowerClosure _
      rw [mem_lowerClosure]
      constructor
      · rintro ⟨j, hj, y, hy, hxy⟩
        rw [List.mem_range'_1] at hj
        exact ⟨y, ⟨j, hj.1, hj.2, hy⟩, hxy⟩
      · rintro ⟨y, ⟨j, h₁, h₂, hy⟩, hxy⟩
        exact ⟨j, List.mem_range'_1.2 ⟨h₁, h₂⟩, y, hy, hxy⟩)

private theorem exists_segment_zero_eq_Iic (hU : IsMoleculeIn P U) (hd : krullDim U ≤ 1) {i : ℕ}
    (hi : i ≤ (edgeList U).length) : ∃ v, IsMin v ∧ v ∈ U ∧ segment U i 0 = LowerSet.Iic v := by
  obtain ⟨n, v, e, h⟩ := exists_pathData hU hd
  rw [h.length_edgeList hU hd] at hi
  exact ⟨v i, h.isMin_v hi, (h.mem_v_of_le hi).1, h.segment_zero hU hd hi⟩

theorem segment_le (hU : IsMoleculeIn P U) (hd : krullDim U ≤ 1) {i m : ℕ}
    (him : i + m ≤ (edgeList U).length) : segment U i m ≤ U := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · obtain ⟨v, -, hv, he⟩ := exists_segment_zero_eq_Iic hU hd (i := i) (by omega)
    rw [he]
    exact LowerSet.Iic_le.2 hv
  · exact (isSubmoleculeOf_segment hU hd hm him).le

theorem isMoleculeIn_segment (hU : IsMoleculeIn P U) (hd : krullDim U ≤ 1) {i m : ℕ}
    (him : i + m ≤ (edgeList U).length) : IsMoleculeIn P (segment U i m) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · obtain ⟨v, hv, -, he⟩ := exists_segment_zero_eq_Iic hU hd (i := i) (by omega)
    rw [he]
    exact .point v hv
  · exact (isSubmoleculeOf_segment hU hd hm him).isMoleculeIn

theorem boundary_segment_zero (hU : IsMoleculeIn P U) (hd : krullDim U ≤ 1) {i : ℕ}
    (hi : i ≤ (edgeList U).length) (n : ℕ) (α : Bool) :
    P.boundary (segment U i 0) n α = segment U i 0 := by
  obtain ⟨v, hv, -, he⟩ := exists_segment_zero_eq_Iic hU hd hi
  rw [he]
  exact boundary_Iic_of_isMin hv n α

theorem segment_cond_zero (hU : IsMoleculeIn P U) (hd : krullDim U ≤ 1) (α : Bool) :
    segment U (cond α (edgeList U).length 0) 0 = P.boundary U 0 α := by
  obtain ⟨n, v, e, h⟩ := exists_pathData hU hd
  rw [h.length_edgeList hU hd]
  cases α
  · exact (h.segment_zero hU hd (Nat.zero_le n)).trans h.source.symm
  · exact (h.segment_zero hU hd le_rfl).trans h.target.symm

theorem le_of_forall_mem_edgeList (hU : IsMoleculeIn P U) (hd : krullDim U ≤ 1)
    (hne : edgeList U ≠ []) {R : LowerSet P} (hR : ∀ x ∈ edgeList U, x ∈ R) : U ≤ R := by
  obtain ⟨n, v, e, h⟩ := exists_pathData hU hd
  have hn : 0 < n := by
    rw [← h.length_edgeList hU hd]
    exact List.length_pos_iff.2 hne
  rw [← h.seg_zero hU hd hn, seg]
  rintro x ⟨_, ⟨j, ⟨-, hj⟩, rfl⟩, hxe⟩
  refine R.lower hxe (hR _ ?_)
  rw [h.edgeList_eq hU hd]
  exact List.mem_map_of_mem (List.mem_range.2 hj)

theorem edgeList_eq_of_isChain (hU : IsMoleculeIn P U) (hd : krullDim U ≤ 1) {l : List P}
    (hl : ∀ x ∈ l, x ∈ U ∧ grade ℕ x = 1)
    (hc : l.IsChain fun x y => P.boundary (LowerSet.Iic x) 0 true =
      P.boundary (LowerSet.Iic y) 0 false)
    (hh : ∀ x ∈ l.head?, P.boundary (LowerSet.Iic x) 0 false = P.boundary U 0 false)
    (ht : ∀ x ∈ l.getLast?, P.boundary (LowerSet.Iic x) 0 true = P.boundary U 0 true)
    (hn : l = [] → P.boundary U 0 false = P.boundary U 0 true) : l = edgeList U := by
  obtain ⟨n, v, e, h⟩ := exists_pathData hU hd
  rw [h.edgeList_eq hU hd, List.range_eq_range']
  rw [h.source] at hh hn
  rw [h.target] at ht hn
  suffices key : ∀ (l : List P) (j : ℕ), j ≤ n → (∀ x ∈ l, x ∈ U ∧ grade ℕ x = 1) →
      l.IsChain (fun x y => P.boundary (LowerSet.Iic x) 0 true =
        P.boundary (LowerSet.Iic y) 0 false) →
      (∀ x ∈ l.head?, P.boundary (LowerSet.Iic x) 0 false = LowerSet.Iic (v j)) →
      (∀ x ∈ l.getLast?, P.boundary (LowerSet.Iic x) 0 true = LowerSet.Iic (v n)) →
      (l = [] → v j = v n) → l = (List.range' j (n - j)).map e by
    simpa using key l 0 (Nat.zero_le n) hl hc hh ht fun hl => LowerSet.Iic_inj.1 (hn hl)
  intro l
  induction l with
  | nil =>
    intro j hj _ _ _ _ hnil
    obtain rfl : j = n := h.injOn_v (Set.mem_Iic.2 hj) (Set.mem_Iic.2 le_rfl) (hnil rfl)
    simp
  | cons x l ih =>
    intro j hj hl hc hh ht _
    have hx := hl x List.mem_cons_self
    have hxm : IsMoleculeIn P (LowerSet.Iic x) := (hU.isAtomIn_Iic hx.1).isMoleculeIn
    have hf : v j ∈ P.faces false x :=
      (mem_faces_iff_boundary_Iic_eq hxm hx.2 false).2 (hh x rfl)
    have hjn : j < n := by
      by_contra hjn
      obtain rfl : j = n := by omega
      have hout := (boundary_zero_eq_Iic_iff hU (h.mem_v_of_le le_rfl).1
        (h.mem_v_of_le le_rfl).2 true).1 h.target
      obtain ⟨hcov, ho⟩ := hf
      simp [hout x hx.1 hcov] at ho
    have hxe : x = e j := h.eq_of_mem_cofaces hU hd false hx.1 (h.mem_e_of_lt hjn).1
      (by simpa using hf) (by simpa using h.face j hjn false)
    subst hxe
    rw [show n - j = n - (j + 1) + 1 by omega, List.range'_succ, List.map_cons]
    refine congrArg _ (ih (j + 1) hjn (fun y hy => hl y (List.mem_cons_of_mem _ hy))
      hc.tail ?_ ?_ ?_)
    · intro y hy
      rw [← (List.isChain_cons.1 hc).1 y hy]
      simpa using h.boundary_Iic_e hU hjn true
    · intro y hy
      refine ht y ?_
      rw [Option.mem_def] at hy ⊢
      rw [List.getLast?_cons, hy]
      rfl
    · intro hnil
      subst hnil
      have := ht (e j) rfl
      rw [h.boundary_Iic_e hU hjn true] at this
      simpa using LowerSet.Iic_inj.1 this

end Segment

section Position

variable [Fintype P] [DecidableLE P] {W : LowerSet P}

theorem edgeList_congr {U' : LowerSet P} [DecidablePred (· ∈ U)] [DecidablePred (· ∈ U')]
    (h : U = U') : edgeList U = edgeList U' := by
  subst h
  congr

def IsPathPos (U : LowerSet P) (y : ℕ) (x : P) : Prop :=
  ∀ _ : DecidablePred (· ∈ U), y ≤ 2 * (edgeList U).length ∧
    segment U (y / 2) (y % 2) = LowerSet.Iic x

theorem isPathPos_iff [DecidablePred (· ∈ U)] {y : ℕ} {x : P} :
    IsPathPos U y x ↔ y ≤ 2 * (edgeList U).length ∧ segment U (y / 2) (y % 2) = LowerSet.Iic x :=
  ⟨fun h => h _, fun h _ => by convert h⟩

namespace PathData

variable {n : ℕ} {v e : ℕ → P}

private theorem isPathPos_iff (h : PathData U n v e) (hU : IsMoleculeIn P U)
    (hd : krullDim U ≤ 1) {y : ℕ} {x : P} :
    IsPathPos U y x ↔ y ≤ 2 * n ∧ x = if y % 2 = 0 then v (y / 2) else e (y / 2) := by
  classical
  rw [OGP.isPathPos_iff, h.length_edgeList hU hd]
  refine and_congr_right fun hy => ?_
  rcases Nat.mod_two_eq_zero_or_one y with h0 | h1
  · rw [h0, if_pos rfl, h.segment_zero hU hd (by omega), LowerSet.Iic_inj, eq_comm]
  · rw [h1, if_neg (by omega), h.segment_eq_seg hU hd Nat.one_pos (by omega), seg_add_one,
      LowerSet.Iic_inj, eq_comm]

end PathData

theorem exists_isPathPos (hU : IsMoleculeIn P U) (hd : krullDim U ≤ 1) {x : P} (hx : x ∈ U) :
    ∃ y, IsPathPos U y x := by
  obtain ⟨n, v, e, h⟩ := exists_pathData hU hd
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (grade_le_one hd hx) with h0 | h1
  · obtain ⟨j, hj, rfl⟩ := (h.mem_v x).1 ⟨hx, h0⟩
    exact ⟨2 * j, (h.isPathPos_iff hU hd).2 ⟨by omega, by
      rw [if_pos (by omega), show 2 * j / 2 = j by omega]⟩⟩
  · obtain ⟨j, hj, rfl⟩ := (h.mem_e x).1 ⟨hx, h1⟩
    exact ⟨2 * j + 1, (h.isPathPos_iff hU hd).2 ⟨by omega, by
      rw [if_neg (by omega), show (2 * j + 1) / 2 = j by omega]⟩⟩

namespace IsPathPos

theorem mem (hU : IsMoleculeIn P U) (hd : krullDim U ≤ 1) {y : ℕ} {x : P}
    (h : IsPathPos U y x) : x ∈ U := by
  obtain ⟨n, v, e, hp⟩ := exists_pathData hU hd
  obtain ⟨hy, rfl⟩ := (hp.isPathPos_iff hU hd).1 h
  split_ifs with h0
  · exact (hp.mem_v_of_le (by omega)).1
  · exact (hp.mem_e_of_lt (by omega)).1

theorem le [DecidablePred (· ∈ U)] {y : ℕ} {x : P} (h : IsPathPos U y x) :
    y ≤ 2 * (edgeList U).length :=
  (isPathPos_iff.1 h).1

theorem unique (hU : IsMoleculeIn P U) (hd : krullDim U ≤ 1) {y y' : ℕ} {x : P}
    (h₁ : IsPathPos U y x) (h₂ : IsPathPos U y' x) : y = y' := by
  obtain ⟨n, v, e, h⟩ := exists_pathData hU hd
  obtain ⟨hy, rfl⟩ := (h.isPathPos_iff hU hd).1 h₁
  obtain ⟨hy', hx⟩ := (h.isPathPos_iff hU hd).1 h₂
  split_ifs at hx with ha hb hb
  · have := h.injOn_v (Set.mem_Iic.2 (by omega : y / 2 ≤ n))
      (Set.mem_Iic.2 (by omega : y' / 2 ≤ n)) hx
    omega
  · have h0 := (h.mem_v_of_le (by omega : y / 2 ≤ n)).2
    rw [hx, (h.mem_e_of_lt (by omega : y' / 2 < n)).2] at h0
    exact absurd h0 one_ne_zero
  · have h0 := (h.mem_e_of_lt (by omega : y / 2 < n)).2
    rw [hx, (h.mem_v_of_le (by omega : y' / 2 ≤ n)).2] at h0
    exact absurd h0 zero_ne_one
  · have := h.injOn_e (Set.mem_Iio.2 (by omega : y / 2 < n))
      (Set.mem_Iio.2 (by omega : y' / 2 < n)) hx
    omega

end IsPathPos

theorem isPathPos_cond_iff [DecidablePred (· ∈ U)] (hU : IsMoleculeIn P U) (hd : krullDim U ≤ 1)
    (α : Bool) {x : P} :
    IsPathPos U (cond α (2 * (edgeList U).length) 0) x ↔ P.boundary U 0 α = LowerSet.Iic x := by
  rw [isPathPos_iff, ← segment_cond_zero hU hd α]
  cases α
  · simp only [cond_false, Nat.zero_div, Nat.zero_mod, Nat.zero_le, true_and]
  · simp only [cond_true, le_refl, true_and, Nat.mul_mod_right,
      Nat.mul_div_cancel_left _ Nat.two_pos]

namespace IsPastingIn

variable (hp : P.IsPastingIn 0 V W U) (hV : IsMoleculeIn P V) (hW : IsMoleculeIn P W)
  (hd : krullDim U ≤ 1)
include hp hV hW hd

theorem edgeList_eq_append [DecidablePred (· ∈ U)] [DecidablePred (· ∈ V)]
    [DecidablePred (· ∈ W)] : edgeList U = edgeList V ++ edgeList W := by
  have hdV : krullDim V ≤ 1 := (LowerSet.krullDim_mono hp.left_le).trans hd
  have hdW : krullDim W ≤ 1 := (LowerSet.krullDim_mono hp.right_le).trans hd
  have hU := hp.isMoleculeIn hV hW
  obtain ⟨n₁, v₁, e₁, h₁⟩ := exists_pathData hV hdV
  obtain ⟨n₂, v₂, e₂, h₂⟩ := exists_pathData hW hdW
  obtain ⟨v, e, h, -, -, he₁, he₂⟩ := PathData.paste hp h₁ h₂
  rw [h.edgeList_eq hU hd, h₁.edgeList_eq hV hdV, h₂.edgeList_eq hW hdW, List.range_add,
    List.map_append, List.map_map]
  congr 1
  · exact List.map_congr_left fun j hj => he₁ j (List.mem_range.1 hj)
  · exact List.map_congr_left fun j hj => he₂ j (List.mem_range.1 hj)

theorem length_edgeList_eq_add [DecidablePred (· ∈ U)] [DecidablePred (· ∈ V)]
    [DecidablePred (· ∈ W)] :
    (edgeList U).length = (edgeList V).length + (edgeList W).length := by
  rw [hp.edgeList_eq_append hV hW hd, List.length_append]

theorem isPathPos_left {y : ℕ} {x : P} (h : IsPathPos V y x) : IsPathPos U y x := by
  have hdV : krullDim V ≤ 1 := (LowerSet.krullDim_mono hp.left_le).trans hd
  have hdW : krullDim W ≤ 1 := (LowerSet.krullDim_mono hp.right_le).trans hd
  have hU := hp.isMoleculeIn hV hW
  obtain ⟨n₁, v₁, e₁, h₁⟩ := exists_pathData hV hdV
  obtain ⟨n₂, v₂, e₂, h₂⟩ := exists_pathData hW hdW
  obtain ⟨v, e, h', hv₁, -, he₁, -⟩ := PathData.paste hp h₁ h₂
  obtain ⟨hy, rfl⟩ := (h₁.isPathPos_iff hV hdV).1 h
  refine (h'.isPathPos_iff hU hd).2 ⟨by omega, ?_⟩
  split_ifs with h0
  · exact (hv₁ _ (by omega)).symm
  · exact (he₁ _ (by omega)).symm

theorem isPathPos_right [DecidablePred (· ∈ V)] {y : ℕ} {x : P} (h : IsPathPos W y x) :
    IsPathPos U (2 * (edgeList V).length + y) x := by
  have hdV : krullDim V ≤ 1 := (LowerSet.krullDim_mono hp.left_le).trans hd
  have hdW : krullDim W ≤ 1 := (LowerSet.krullDim_mono hp.right_le).trans hd
  have hU := hp.isMoleculeIn hV hW
  obtain ⟨n₁, v₁, e₁, h₁⟩ := exists_pathData hV hdV
  obtain ⟨n₂, v₂, e₂, h₂⟩ := exists_pathData hW hdW
  obtain ⟨v, e, h', -, hv₂, -, he₂⟩ := PathData.paste hp h₁ h₂
  obtain ⟨hy, rfl⟩ := (h₂.isPathPos_iff hW hdW).1 h
  rw [h₁.length_edgeList hV hdV]
  refine (h'.isPathPos_iff hU hd).2 ⟨by omega, ?_⟩
  rw [show (2 * n₁ + y) / 2 = n₁ + y / 2 by omega, show (2 * n₁ + y) % 2 = y % 2 by omega]
  split_ifs with h0
  · exact (hv₂ _ (by omega)).symm
  · exact (he₂ _ (by omega)).symm

end IsPastingIn

theorem edgeList_map {Q : OGP.{u}} [Fintype Q] [DecidableLE Q] (f : P ⟶ Q) [IsInclusion f]
    [DecidablePred (· ∈ U)] [DecidablePred (· ∈ OGP.map f U)] (hU : IsMoleculeIn P U)
    (hd : krullDim U = 1) : edgeList (OGP.map f U) = (edgeList U).map f := by
  refine (edgeList_eq_of_isChain ((isMoleculeIn_map_iff f U).2 hU)
    ((krullDim_map f U).trans_le hd.le) ?_ ?_ ?_ ?_ ?_).symm
  · simp only [List.mem_map]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hxU, hx1⟩ := (mem_edgeList_iff hU hd.le).1 hx
    exact ⟨⟨x, hxU, rfl⟩, ((isMorphism f).grade_eq x).trans hx1⟩
  · rw [List.isChain_map]
    refine (edgeList_isChain hU hd.le).imp fun x y h => ?_
    rw [← map_Iic, ← map_Iic, ← map_boundary, ← map_boundary, h]
  · intro y hy
    rw [List.head?_map, Option.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [← map_Iic, ← map_boundary, boundary_Iic_of_mem_head?_edgeList hU hd.le hx, map_boundary]
  · intro y hy
    rw [List.getLast?_map, Option.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [← map_Iic, ← map_boundary, boundary_Iic_of_mem_getLast?_edgeList hU hd.le hx,
      map_boundary]
  · intro h
    exact absurd (List.map_eq_nil_iff.1 h) (edgeList_ne_nil hU hd)

theorem length_edgeList_of_isAtomIn [DecidablePred (· ∈ U)] (h : P.IsAtomIn U)
    (hd : krullDim U = 1) : (edgeList U).length = 1 := by
  obtain ⟨hU, t, rfl⟩ := h
  have h1 : grade ℕ t = 1 := by
    rw [LowerSet.krullDim_Iic] at hd
    exact_mod_cast hd
  obtain ⟨v, hv⟩ := exists_pathData_Iic_of_grade_eq_one hU h1
  exact hv.length_edgeList hU hd.le

end Position

theorem isSubmoleculeOf_of_le [Finite P] (hU : IsMoleculeIn P U) (hd : krullDim U ≤ 1)
    (hV : IsMoleculeIn P V) (hVd : krullDim V = 1) (hVU : V ≤ U) : P.IsSubmoleculeOf V U := by
  classical
  have := Fintype.ofFinite P
  obtain ⟨i, m, hm, him, rfl⟩ := exists_segment_eq hU hd hV hVd hVU
  exact isSubmoleculeOf_segment hU hd hm him

theorem krullDim_bdry_Iic_of_grade_eq_two {t : P} (ht : P.IsAtomIn (LowerSet.Iic t))
    (h2 : grade ℕ t = 2) (α : Bool) : krullDim (P.bdry (LowerSet.Iic t) α) = 1 := by
  have := ht.isMoleculeIn.krullDim_bdry (n := 1) (by rw [LowerSet.krullDim_Iic, h2]) α
  exact_mod_cast this

theorem bdry_Iic_inf_bdry_Iic_of_grade_eq_two {t : P} (ht : P.IsAtomIn (LowerSet.Iic t))
    (h2 : grade ℕ t = 2) :
    P.bdry (LowerSet.Iic t) false ⊓ P.bdry (LowerSet.Iic t) true =
      P.boundaryFull (LowerSet.Iic t) 0 := by
  have hU : krullDim (LowerSet.Iic t) = (1 : ℕ) + 1 := by
    rw [LowerSet.krullDim_Iic, h2]
    rfl
  rw [bdry_eq_boundary hU, bdry_eq_boundary hU]
  exact ht.isRound.inf_boundary_succ 0 (by rw [hU]; exact_mod_cast Nat.one_lt_two)

end Atoms.Molecule.OGP
