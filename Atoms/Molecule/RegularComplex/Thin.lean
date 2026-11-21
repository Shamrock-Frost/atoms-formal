import Atoms.Molecule.Decidable
import Atoms.Molecule.Rigidity
import Atoms.Molecule.RegularComplex.Basic

universe u

open Order Set

namespace Atoms.Molecule.OGP

variable (P : OGP.{u})

def IsSignedDiamond (P : OGP.{u}) (y x : P) : Prop :=
  ∃ z₁ z₂, z₁ ≠ z₂ ∧ Ioo y x = {z₁, z₂} ∧
    ∀ (h₁ : y ⋖ z₁) (h₁' : z₁ ⋖ x) (h₂ : y ⋖ z₂) (h₂' : z₂ ⋖ x),
      (P.orient h₁ == P.orient h₁') ≠ (P.orient h₂ == P.orient h₂')

def HasSignedDiamonds (P : OGP.{u}) : Prop :=
  ∀ x y : P, y < x → grade ℕ x = grade ℕ y + 2 → P.IsSignedDiamond y x

structure IsOrientedThin : Prop where
  exists_faces_eq_singleton : ∀ x : P, grade ℕ x = 1 → ∀ α, ∃ y, P.faces α x = {y}
  diamond : P.HasSignedDiamonds

variable {P}

theorem IsOrientedThin.exists_faces_eq (h : P.IsOrientedThin) {x : P} (hx : grade ℕ x = 1) :
    ∃ s t, s ≠ t ∧ P.faces false x = {s} ∧ P.faces true x = {t} := by
  obtain ⟨s, hs⟩ := h.exists_faces_eq_singleton x hx false
  obtain ⟨t, ht⟩ := h.exists_faces_eq_singleton x hx true
  refine ⟨s, t, fun he => ?_, hs, ht⟩
  have hs' : s ∈ P.faces false x := hs ▸ rfl
  have ht' : s ∈ P.faces true x := he ▸ ht ▸ rfl
  exact Set.disjoint_left.1 (P.disjoint_faces x false) hs' ht'

theorem IsRDC.exists_faces_eq_singleton (h : P.IsRDC) {x : P} (hx : grade ℕ x = 1)
    (α : Bool) : ∃ y, P.faces α x = {y} := by
  have hpos : 0 < krullDim (LowerSet.Iic x) := by
    rw [LowerSet.krullDim_Iic, hx]
    exact_mod_cast Nat.one_pos
  have hmol := (h x).bdry hpos α
  have hd := krullDim_bdry_Iic (n := 0) hx hmol.nonempty
  obtain ⟨y, hy, hW⟩ := hmol.exists_eq_Iic_of_krullDim_eq_zero (by exact_mod_cast hd)
  refine ⟨y, Set.ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩⟩
  · have hzW : z ∈ P.bdry (.Iic x) α := by
      rw [bdry_Iic]
      exact subset_lowerClosure hz
    rw [hW] at hzW
    exact le_antisymm hzW (hy hzW)
  · rw [Set.mem_singleton_iff.1 hz]
    have hyW : y ∈ P.bdry (.Iic x) α := by
      rw [hW]
      exact LowerSet.mem_Iic_iff.2 le_rfl
    exact mem_faces_of_mem_bdry_Iic hyW (by rw [grade_eq_zero_iff.2 hy, hx])

theorem IsRDC.diamond (h : P.IsRDC) {x y : P} (hyx : y < x)
    (hd : grade ℕ x = grade ℕ y + 2) :
    P.IsSignedDiamond y x := by
  have hx : grade ℕ x = (grade ℕ y + 1) + 1 := hd
  have hpos : 0 < krullDim (LowerSet.Iic x) := by
    rw [LowerSet.krullDim_Iic, hx]
    exact_mod_cast Nat.succ_pos _
  have hmol (α : Bool) : IsMoleculeIn P (P.bdry (.Iic x) α) := (h x).bdry hpos α
  have hdim (α : Bool) : krullDim (P.bdry (.Iic x) α) = (grade ℕ y + 1 : ℕ) :=
    krullDim_bdry_Iic hx (hmol α).nonempty
  obtain ⟨hround, hbdry, hinf⟩ := (IsAtomIn.isRound ⟨h x, x, rfl⟩).halves hx
    fun α => (hmol α).nonempty
  have huniq {α β : Bool} {z z' : P} (hz : z ∈ P.cofaces β y ∩ P.bdry (.Iic x) α)
      (hz' : z' ∈ P.cofaces β y ∩ P.bdry (.Iic x) α) : z = z' :=
    (hmol α).subsingleton_cofaces_inter (hdim α).le β hz hz'
  have hb (α γ : Bool) : P.bdry (P.bdry (.Iic x) α) γ = P.bdry (P.bdry (.Iic x) false) γ := by
    cases α
    · rfl
    · exact (hbdry γ).symm
  have hbα (α γ : Bool) :
      P.bdry (P.bdry (.Iic x) α) γ = P.boundary (P.bdry (.Iic x) α) (grade ℕ y) γ :=
    bdry_eq_boundary (by rw [hdim α]; push_cast; rfl) γ
  have hIoo {z : P} (hz : z ∈ Ioo y x) : y ⋖ z ∧ z ⋖ x := by
    have h₁ := grade_strictMono (𝕆 := ℕ) hz.1
    have h₂ := grade_strictMono (𝕆 := ℕ) hz.2
    exact ⟨GradeOrder.covBy_of_le_of_grade_eq_add_one hz.1.le (by omega),
      GradeOrder.covBy_of_le_of_grade_eq_add_one hz.2.le (by omega)⟩
  have hface {α : Bool} {z : P} (hzW : z ∈ P.bdry (.Iic x) α) (hyz : y ⋖ z) :
      z ∈ P.faces α x ∧ z ∈ Ioo y x := by
    have hzd := Nat.covBy_iff_add_one_eq.1 (hyz.grade ℕ)
    have hzx := mem_faces_of_mem_bdry_Iic hzW (by omega)
    exact ⟨hzx, hyz.lt, hzx.1.lt⟩
  obtain ⟨z₁, hyz₁, hz₁x⟩ := exists_covBy_le_of_lt hyx
  have hz₁ : z₁ ∈ Ioo y x := ⟨hyz₁.lt, hz₁x.lt_of_ne fun e => by
    have := Nat.covBy_iff_add_one_eq.1 (hyz₁.grade ℕ)
    rw [e] at this
    omega⟩
  have hz₁x' := (hIoo hz₁).2
  obtain ⟨α, hα⟩ : ∃ α, P.orient hz₁x' = α := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β, P.orient hyz₁ = β := ⟨_, rfl⟩
  have hz₁W : z₁ ∈ P.bdry (.Iic x) α := hα ▸ mem_bdry_Iic_of_covBy hz₁x'
  have hc₁ : z₁ ∈ P.cofaces β y ∩ P.bdry (.Iic x) α := ⟨⟨hyz₁, hβ⟩, hz₁W⟩
  have hyW (γ : Bool) {z : P} (hz : z ∈ P.bdry (.Iic x) γ) (hyz : y ⋖ z) :
      y ∈ P.bdry (.Iic x) γ :=
    (P.bdry (.Iic x) γ).lower hyz.le hz
  have hcof {z : P} (hz : z ∈ Ioo y x) :
      z ∈ P.cofaces (P.orient (hIoo hz).1) y ∩ P.bdry (.Iic x) (P.orient (hIoo hz).2) :=
    ⟨⟨(hIoo hz).1, rfl⟩, mem_bdry_Iic_of_covBy (hIoo hz).2⟩
  by_cases hc : ∃ c, c ∈ P.cofaces (!β) y ∩ P.bdry (.Iic x) α
  · obtain ⟨c, ⟨hyc, hoc⟩, hcW⟩ := hc
    obtain ⟨⟨hcx, hxc⟩, hcI⟩ := hface hcW hyc
    refine ⟨z₁, c, fun e => ?_, ?_, ?_⟩
    · subst e
      have hββ : β = !β := hβ.symm.trans hoc
      cases β <;> exact absurd hββ (by decide)
    · refine Set.ext fun z => ⟨fun hz => ?_, ?_⟩
      · obtain ⟨⟨hyz, -⟩, hzW⟩ := hcof hz
        rcases Bool.eq_or_eq_not (P.orient (hIoo hz).2) α with hzα | hzα
        · rw [hzα] at hzW
          rcases Bool.eq_or_eq_not (P.orient hyz) β with hzβ | hzβ
          · exact Or.inl (huniq ⟨⟨hyz, hzβ⟩, hzW⟩ hc₁)
          · exact Or.inr (huniq ⟨⟨hyz, hzβ⟩, hzW⟩ ⟨⟨hyc, hoc⟩, hcW⟩)
        · rw [hzα] at hzW
          exfalso
          have hy : y ∈ P.bdry (.Iic x) α ⊓ P.bdry (.Iic x) (!α) :=
            ⟨hyW α hz₁W hyz₁, hyW (!α) hzW hyz⟩
          have hy' : y ∈ P.bdryFull (P.bdry (.Iic x) false) := by
            rw [← hinf]
            cases α
            · exact hy
            · exact ⟨hy.2, hy.1⟩
          obtain ⟨γ, hγ⟩ : ∃ γ, y ∈ P.bdry (P.bdry (.Iic x) false) γ :=
            (LowerSet.mem_sup_iff.1 hy').elim (⟨false, ·⟩) (⟨true, ·⟩)
          rw [← hb α, hbα] at hγ
          have hfin := (mem_facesIn_of_mem_boundary hγ rfl).2.2
          rcases Bool.eq_or_eq_not β γ with hβγ | hβγ
          · exact Set.disjoint_left.1 hfin ⟨hyc, hoc.trans (by rw [hβγ])⟩ hcW
          · exact Set.disjoint_left.1 hfin ⟨hyz₁, hβ.trans hβγ⟩ hz₁W
      · rintro (rfl | rfl)
        · exact hz₁
        · exact hcI
    · intro h₁ h₁' h₂ h₂'
      rw [(hβ : P.orient h₁ = β), (hα : P.orient h₁' = α), (hoc : P.orient h₂ = !β),
        (hxc : P.orient h₂' = α)]
      cases α <;> cases β <;> decide
  · have hyF : y ∈ P.facesIn (P.bdry (.Iic x) α) (grade ℕ y) β :=
      ⟨hyW α hz₁W hyz₁, rfl, Set.disjoint_left.2 fun c hc' hcW => hc ⟨c, hc', hcW⟩⟩
    have hyB := mem_boundary_of_mem_facesIn hyF le_rfl
    rw [← hbα, hb α, ← hb (!α), hbα] at hyB
    have hyF' := mem_facesIn_of_mem_boundary hyB rfl
    have hnmax : ¬ Maximal (· ∈ P.bdry (.Iic x) (!α)) y := fun hm => by
      have := (hround (!α)).grade_eq_of_maximal (hdim (!α)) hm
      omega
    rw [maximal_mem_iff_forall_cofaces_inter_eq_empty hyF'.1] at hnmax
    obtain ⟨γ, hγ⟩ := not_forall.1 hnmax
    obtain ⟨m, ⟨hym, -⟩, hmW⟩ := Set.nonempty_iff_ne_empty.2 hγ
    have homβ : P.orient hym = β := by
      rcases Bool.eq_or_eq_not (P.orient hym) β with hmβ | hmβ
      · exact hmβ
      · exact (Set.disjoint_left.1 hyF'.2.2 ⟨hym, hmβ⟩ hmW).elim
    obtain ⟨⟨hmx, hxm⟩, hmI⟩ := hface hmW hym
    refine ⟨z₁, m, fun e => ?_, ?_, ?_⟩
    · subst e
      have hαα : α = !α := hα.symm.trans hxm
      cases α <;> exact absurd hαα (by decide)
    · refine Set.ext fun z => ⟨fun hz => ?_, ?_⟩
      · obtain ⟨⟨hyz, -⟩, hzW⟩ := hcof hz
        rcases Bool.eq_or_eq_not (P.orient (hIoo hz).2) α with hzα | hzα
        · rw [hzα] at hzW
          rcases Bool.eq_or_eq_not (P.orient hyz) β with hzβ | hzβ
          · exact Or.inl (huniq ⟨⟨hyz, hzβ⟩, hzW⟩ hc₁)
          · exact (hc ⟨z, ⟨hyz, hzβ⟩, hzW⟩).elim
        · rw [hzα] at hzW
          rcases Bool.eq_or_eq_not (P.orient hyz) β with hzβ | hzβ
          · exact Or.inr (huniq ⟨⟨hyz, hzβ⟩, hzW⟩ ⟨⟨hym, homβ⟩, hmW⟩)
          · exact (Set.disjoint_left.1 hyF'.2.2 ⟨hyz, hzβ⟩ hzW).elim
      · rintro (rfl | rfl)
        · exact hz₁
        · exact hmI
    · intro h₁ h₁' h₂ h₂'
      rw [(hβ : P.orient h₁ = β), (hα : P.orient h₁' = α), (homβ : P.orient h₂ = β),
        (hxm : P.orient h₂' = !α)]
      cases α <;> cases β <;> decide

theorem IsRDC.isOrientedThin (h : P.IsRDC) : P.IsOrientedThin :=
  ⟨fun _ hx α => h.exists_faces_eq_singleton hx α, fun _ _ hyx hd => h.diamond hyx hd⟩

theorem isOrientedThin_iff : P.IsOrientedThin ↔
    (∀ x : P, grade ℕ x = 1 → ∀ α, ∃ y, P.faces α x = {y}) ∧
      P.HasSignedDiamonds :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

section Decide

variable (P) [Fintype P] [DecidableEq P] [DecidableLE P]

instance decidableIsOrientedThin : Decidable P.IsOrientedThin :=
  letI : DecidableLT P := decidableLTOfDecidableLE
  letI : Decidable (∀ x : P, grade ℕ x = 1 → ∀ α, ∃ y, ∀ z, z ∈ P.faces α x ↔ z = y) :=
    inferInstance
  letI : Decidable (∀ x y : P, y < x → grade ℕ x = grade ℕ y + 2 →
      ∃ z₁ z₂, z₁ ≠ z₂ ∧ (∀ z, y < z ∧ z < x ↔ z = z₁ ∨ z = z₂) ∧
        ∀ (h₁ : y ⋖ z₁) (h₁' : z₁ ⋖ x) (h₂ : y ⋖ z₂) (h₂' : z₂ ⋖ x),
          (P.orient h₁ == P.orient h₁') ≠ (P.orient h₂ == P.orient h₂')) :=
    inferInstance
  decidable_of_iff'
    ((∀ x : P, grade ℕ x = 1 → ∀ α, ∃ y, ∀ z, z ∈ P.faces α x ↔ z = y) ∧
      ∀ x y : P, y < x → grade ℕ x = grade ℕ y + 2 →
        ∃ z₁ z₂, z₁ ≠ z₂ ∧ (∀ z, y < z ∧ z < x ↔ z = z₁ ∨ z = z₂) ∧
          ∀ (h₁ : y ⋖ z₁) (h₁' : z₁ ⋖ x) (h₂ : y ⋖ z₂) (h₂' : z₂ ⋖ x),
            (P.orient h₁ == P.orient h₁') ≠ (P.orient h₂ == P.orient h₂'))
    (isOrientedThin_iff.trans (by
      simp only [HasSignedDiamonds, IsSignedDiamond, Set.ext_iff, Set.mem_singleton_iff,
        Set.mem_Ioo, Set.mem_insert_iff]))

end Decide

end Atoms.Molecule.OGP
