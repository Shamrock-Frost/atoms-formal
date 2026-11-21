import Atoms.Molecule.Construction.GrayProductMap

universe u

open CategoryTheory Order Set Topology

namespace Atoms.Molecule.OGP

abbrev ArrowElt : Type := Option Bool

def PartialCylinderCarrier (U : OGP.{u}) (K : LowerSet U) : Type u :=
  {x : U // x ∈ K} ⊕ (ULift.{u} ArrowElt × {x : U // x ∉ K})

namespace PartialCylinderCarrier

variable {U : OGP.{u}} {K : LowerSet U}

transfer_instances PartialCylinderCarrier U K with Fintype DecidableEq

def proj : PartialCylinderCarrier U K → U
  | Sum.inl x => x.1
  | Sum.inr p => p.2.1

def ArrowLE (j i : ArrowElt) : Prop := j = i ∨ i = none

protected def le : PartialCylinderCarrier U K → PartialCylinderCarrier U K → Prop
  | Sum.inl y, Sum.inl x => y.1 ≤ x.1
  | Sum.inl y, Sum.inr p => y.1 ≤ p.2.1
  | Sum.inr _, Sum.inl _ => False
  | Sum.inr q, Sum.inr p => ArrowLE q.1.down p.1.down ∧ q.2.1 ≤ p.2.1

private instance decidableLE' [DecidableLE U] :
    DecidableRel (PartialCylinderCarrier.le (U := U) (K := K))
  | Sum.inl y, Sum.inl x => inferInstanceAs (Decidable (y.1 ≤ x.1))
  | Sum.inl y, Sum.inr p => inferInstanceAs (Decidable (y.1 ≤ p.2.1))
  | Sum.inr _, Sum.inl _ => inferInstanceAs (Decidable False)
  | Sum.inr q, Sum.inr p => inferInstanceAs
      (Decidable ((q.1.down = p.1.down ∨ p.1.down = none) ∧ q.2.1 ≤ p.2.1))

instance instPartialOrder : PartialOrder (PartialCylinderCarrier U K) where
  le := PartialCylinderCarrier.le
  le_refl := by
    rintro (x | ⟨⟨i⟩, x⟩)
    · exact le_refl x.1
    · exact ⟨Or.inl rfl, le_refl x.1⟩
  le_trans := by
    rintro (x | ⟨⟨i⟩, x⟩) (y | ⟨⟨j⟩, y⟩) (z | ⟨⟨k⟩, z⟩) h₁ h₂ <;>
      simp only [PartialCylinderCarrier.le, ArrowLE] at h₁ h₂ ⊢ <;>
      first
        | exact le_trans h₁ h₂
        | exact le_trans h₁ h₂.2
        | exact h₁.elim
        | exact h₂.elim
        | refine ⟨?_, le_trans h₁.2 h₂.2⟩
          rcases h₁.1 with rfl | rfl <;> rcases h₂.1 with rfl | rfl <;> simp
  le_antisymm := by
    rintro (x | ⟨⟨i⟩, x⟩) (y | ⟨⟨j⟩, y⟩) h₁ h₂ <;>
      simp only [PartialCylinderCarrier.le, ArrowLE] at h₁ h₂
    · exact congrArg Sum.inl (Subtype.ext (le_antisymm h₁ h₂))
    · have hij : i = j := by
        rcases h₁.1 with h | rfl
        · exact h
        · rcases h₂.1 with h | rfl <;> first | exact h.symm | rfl
      subst hij
      rw [Subtype.ext (le_antisymm h₁.2 h₂.2)]

instance instDecidableLE [DecidableLE U] : DecidableLE (PartialCylinderCarrier U K) :=
  decidableLE'

theorem not_inr_le_inl {y : {x : U // x ∈ K}}
    {p : ULift.{u} ArrowElt × {x : U // x ∉ K}} :
    ¬ @LE.le (PartialCylinderCarrier U K) _ (Sum.inr p) (Sum.inl y) := id

theorem inr_le_inr_iff {q p : ULift.{u} ArrowElt × {x : U // x ∉ K}} :
    @LE.le (PartialCylinderCarrier U K) _ (Sum.inr q) (Sum.inr p) ↔
      (q.1.down = p.1.down ∨ p.1.down = none) ∧ q.2.1 ≤ p.2.1 := Iff.rfl

theorem lt_of_le_of_proj_lt {a b : PartialCylinderCarrier U K} (h : a ≤ b)
    (hp : proj a < proj b) : a < b :=
  lt_of_le_of_ne h fun he => hp.ne (congrArg proj he)

def dimFn : PartialCylinderCarrier U K → ℕ
  | Sum.inl x => grade ℕ x.1
  | Sum.inr (⟨some _⟩, x) => grade ℕ x.1
  | Sum.inr (⟨none⟩, x) => grade ℕ x.1 + 1

theorem dimFn_lt_of_lt {a b : PartialCylinderCarrier U K} (h : a < b) : dimFn a < dimFn b := by
  have hle := h.le
  have hne := h.ne
  rcases a with ⟨y, hy⟩ | ⟨⟨j⟩, ⟨y, hy⟩⟩ <;> rcases b with ⟨x, hx⟩ | ⟨⟨i⟩, ⟨x, hx⟩⟩
  · have hyx : y < x := lt_of_le_of_ne hle fun he => hne (by subst he; rfl)
    exact grade_strictMono hyx
  · have hyx : y < x := lt_of_le_of_ne hle fun he => hx (he ▸ hy)
    have := grade_strictMono (𝕆 := ℕ) hyx
    rcases i with _ | β <;> simp only [dimFn] <;> omega
  · exact (not_inr_le_inl hle).elim
  · obtain ⟨hji, hyx⟩ := (inr_le_inr_iff).1 hle
    simp only at hji hyx
    rcases eq_or_lt_of_le hyx with he | hlt
    · subst he
      rcases hji with rfl | rfl
      · exact (hne rfl).elim
      · rcases j with _ | β
        · exact (hne rfl).elim
        · simp [dimFn]
    · have := grade_strictMono (𝕆 := ℕ) hlt
      rcases j with _ | β <;> rcases i with _ | γ <;> simp only [dimFn] <;>
        first | omega | (rcases hji with h | h <;> simp at h)

theorem covBy_iff {a b : PartialCylinderCarrier U K} :
    a ⋖ b ↔ a < b ∧ dimFn b = dimFn a + 1 := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    by_contra hd
    have hlt := dimFn_lt_of_lt h.1
    have hle := h.1.le
    suffices ∃ c, a < c ∧ c < b by
      obtain ⟨c, h1, h2⟩ := this
      exact h.2 h1 h2
    rcases a with ⟨y, hy⟩ | ⟨⟨j⟩, ⟨y, hy⟩⟩ <;> rcases b with ⟨x, hx⟩ | ⟨⟨i⟩, ⟨x, hx⟩⟩
    · have hyx : y < x := lt_of_le_of_ne hle fun he => h.1.ne (by subst he; rfl)
      obtain ⟨z, h1, h2⟩ := (not_covBy_iff hyx).1 fun hc =>
        hd (by simpa [dimFn] using (Nat.covBy_iff_add_one_eq.1 (hc.grade ℕ)).symm)
      have hz : z ∈ K := K.lower h2.le hx
      exact ⟨Sum.inl ⟨z, hz⟩, lt_of_le_of_proj_lt h1.le h1, lt_of_le_of_proj_lt h2.le h2⟩
    · have hyx : y < x := lt_of_le_of_ne hle fun he => hx (he ▸ hy)
      rcases i with _ | β
      · refine ⟨Sum.inr (⟨some false⟩, ⟨x, hx⟩), lt_of_le_of_ne hyx.le (fun h => by cases h), ?_⟩
        exact lt_of_le_of_ne ⟨Or.inr rfl, le_rfl⟩ (fun h => by cases h)
      · obtain ⟨z, h1, h2⟩ := (not_covBy_iff hyx).1 fun hc =>
          hd (by simpa [dimFn] using (Nat.covBy_iff_add_one_eq.1 (hc.grade ℕ)).symm)
        by_cases hz : z ∈ K
        · exact ⟨Sum.inl ⟨z, hz⟩, lt_of_le_of_proj_lt h1.le h1, lt_of_le_of_proj_lt h2.le h2⟩
        · exact ⟨Sum.inr (⟨some β⟩, ⟨z, hz⟩), lt_of_le_of_proj_lt h1.le h1,
            lt_of_le_of_proj_lt ⟨Or.inl rfl, h2.le⟩ h2⟩
    · exact (not_inr_le_inl hle).elim
    · obtain ⟨hji, hyx⟩ := (inr_le_inr_iff).1 hle
      simp only at hji hyx
      rcases eq_or_lt_of_le hyx with he | hyx
      · subst he
        rcases hji with rfl | rfl
        · exact (h.1.ne rfl).elim
        · rcases j with _ | β
          · exact (h.1.ne rfl).elim
          · exact (hd (by simp [dimFn])).elim
      · have hz' : ∀ z, y < z → z ∉ K := fun z hyz hz => hy (K.lower hyz.le hz)
        by_cases he : j = i
        · subst he
          obtain ⟨z, h1, h2⟩ := (not_covBy_iff hyx).1 fun hc =>
            hd (by cases j <;>
              simpa [dimFn] using (Nat.covBy_iff_add_one_eq.1 (hc.grade ℕ)).symm)
          exact ⟨Sum.inr (⟨j⟩, ⟨z, hz' z h1⟩),
            lt_of_le_of_proj_lt ⟨Or.inl rfl, h1.le⟩ h1,
            lt_of_le_of_proj_lt ⟨Or.inl rfl, h2.le⟩ h2⟩
        · obtain rfl := hji.resolve_left he
          rcases j with _ | β
          · exact (he rfl).elim
          · exact ⟨Sum.inr (⟨some β⟩, ⟨x, hx⟩),
              lt_of_le_of_proj_lt ⟨Or.inl rfl, hyx.le⟩ hyx,
              lt_of_le_of_ne ⟨Or.inr rfl, le_rfl⟩ (fun h => by cases h)⟩
  · rintro ⟨hlt, hd⟩
    refine ⟨hlt, fun c h1 h2 => ?_⟩
    have := dimFn_lt_of_lt h1
    have := dimFn_lt_of_lt h2
    omega

theorem dimFn_eq_zero_of_isMin (a : PartialCylinderCarrier U K)
    (h : ∀ b, ¬ b < a) : dimFn a = 0 := by
  rcases a with ⟨x, hx⟩ | ⟨⟨_ | β⟩, ⟨x, hx⟩⟩
  · change grade ℕ x = 0
    refine grade_eq_zero_iff.2 fun z hz => (hz.eq_of_not_lt fun hzx => ?_).ge
    exact h (Sum.inl ⟨z, K.lower hz hx⟩) (lt_of_le_of_proj_lt hz hzx)
  · exact (h (Sum.inr (⟨some false⟩, ⟨x, hx⟩))
      (lt_of_le_of_ne ⟨Or.inr rfl, le_rfl⟩ (fun h => by cases h))).elim
  · change grade ℕ x = 0
    refine grade_eq_zero_iff.2 fun z hz => (hz.eq_of_not_lt fun hzx => ?_).ge
    by_cases hzK : z ∈ K
    · exact h (Sum.inl ⟨z, hzK⟩) (lt_of_le_of_proj_lt hz hzx)
    · exact h (Sum.inr (⟨some β⟩, ⟨z, hzK⟩))
        (lt_of_le_of_proj_lt ⟨Or.inl rfl, hz⟩ hzx)

instance instGradeMinOrder : GradeMinOrder ℕ (PartialCylinderCarrier U K) where
  grade := dimFn
  grade_strictMono _ _ h := dimFn_lt_of_lt h
  covBy_grade _ _ h := Nat.covBy_iff_add_one_eq.2 (covBy_iff.1 h).2.symm
  isMin_grade a h := isMin_iff_eq_bot.2 (dimFn_eq_zero_of_isMin a fun _ hb => h.not_lt hb)

theorem proj_le_proj {a b : PartialCylinderCarrier U K} (h : a ≤ b) :
    proj a ≤ proj b := by
  rcases a with y | q <;> rcases b with x | p <;>
    first | exact h | exact (not_inr_le_inl h).elim | exact h.2

theorem proj_covBy_of_covBy_inl {x : {x : U // x ∈ K}} {b : PartialCylinderCarrier U K}
    (h : b ⋖ Sum.inl x) : proj b ⋖ x.1 := by
  obtain ⟨hlt, hd⟩ := covBy_iff.1 h
  rcases b with ⟨y, hy⟩ | ⟨⟨j⟩, ⟨y, hy⟩⟩
  · exact GradeOrder.covBy_of_le_of_grade_eq_add_one hlt.le hd
  · exact (not_inr_le_inl hlt.le).elim

theorem proj_covBy_of_covBy_inr_some {α : Bool} {x : {x : U // x ∉ K}}
    {b : PartialCylinderCarrier U K} (h : b ⋖ Sum.inr (⟨some α⟩, x)) : proj b ⋖ x.1 := by
  obtain ⟨hlt, hd⟩ := covBy_iff.1 h
  rcases b with ⟨y, hy⟩ | ⟨⟨_ | β⟩, ⟨y, hy⟩⟩
  · exact GradeOrder.covBy_of_le_of_grade_eq_add_one hlt.le hd
  · rcases hlt.le.1 with h' | h' <;> cases h'
  · exact GradeOrder.covBy_of_le_of_grade_eq_add_one hlt.le.2 hd

theorem proj_covBy_of_covBy_inr_none {x y : {x : U // x ∉ K}}
    (h : @CovBy (PartialCylinderCarrier U K) _ (Sum.inr (⟨none⟩, y)) (Sum.inr (⟨none⟩, x))) :
    y.1 ⋖ x.1 := by
  obtain ⟨hlt, hd⟩ := covBy_iff.1 h
  exact GradeOrder.covBy_of_le_of_grade_eq_add_one hlt.le.2 (Nat.add_right_cancel hd)

theorem not_covBy_inl_inr_none {y : {x : U // x ∈ K}} {x : {x : U // x ∉ K}} :
    ¬ @CovBy (PartialCylinderCarrier U K) _ (Sum.inl y) (Sum.inr (⟨none⟩, x)) := by
  intro h
  obtain ⟨hlt, hd⟩ := covBy_iff.1 h
  have hyx : y.1 < x.1 := lt_of_le_of_ne hlt.le fun he => x.2 (he ▸ y.2)
  have := grade_strictMono (𝕆 := ℕ) hyx
  have hd' : grade ℕ x.1 + 1 = grade ℕ y.1 + 1 := hd
  omega

def orientFn : ∀ a b : PartialCylinderCarrier U K, b ⋖ a → Bool
  | Sum.inr (⟨none⟩, _), Sum.inr (⟨some β⟩, _), _ => β
  | Sum.inr (⟨none⟩, _), Sum.inr (⟨none⟩, _), h => !U.orient (proj_covBy_of_covBy_inr_none h)
  | Sum.inr (⟨none⟩, _), Sum.inl _, h => (not_covBy_inl_inr_none h).elim
  | Sum.inr (⟨some _⟩, _), _, h => U.orient (proj_covBy_of_covBy_inr_some h)
  | Sum.inl _, _, h => U.orient (proj_covBy_of_covBy_inl h)

end PartialCylinderCarrier

open PartialCylinderCarrier in
def partialCylinder (U : OGP.{u}) (K : LowerSet U) : OGP.{u} where
  carrier := PartialCylinderCarrier U K
  orient {a b} h := orientFn a b h

def partialCylinderProj (U : OGP.{u}) (K : LowerSet U) :
    partialCylinder U K → U :=
  PartialCylinderCarrier.proj

namespace PartialCylinder

open PartialCylinderCarrier

variable {U : OGP.{u}} {K : LowerSet U}

abbrev mkK (K : LowerSet U) (x : U) (hx : x ∈ K) : partialCylinder U K :=
  Sum.inl ⟨x, hx⟩

abbrev mkI (K : LowerSet U) (i : ArrowElt) (x : U) (hx : x ∉ K) :
    partialCylinder U K :=
  Sum.inr (⟨i⟩, ⟨x, hx⟩)

variable {x y : U}

theorem covBy_mkK_mkK (hy : y ∈ K) (hx : x ∈ K) : mkK K y hy ⋖ mkK K x hx ↔ y ⋖ x := by
  refine ⟨proj_covBy_of_covBy_inl, fun h => PartialCylinderCarrier.covBy_iff.2 ⟨?_, ?_⟩⟩
  · exact PartialCylinderCarrier.lt_of_le_of_proj_lt h.le h.lt
  · exact (Nat.covBy_iff_add_one_eq.1 (h.grade ℕ)).symm

theorem covBy_mkK_mkI_some (hy : y ∈ K) (β : Bool) (hx : x ∉ K) :
    mkK K y hy ⋖ mkI K (some β) x hx ↔ y ⋖ x := by
  refine ⟨proj_covBy_of_covBy_inr_some, fun h => PartialCylinderCarrier.covBy_iff.2 ⟨?_, ?_⟩⟩
  · exact PartialCylinderCarrier.lt_of_le_of_proj_lt h.le h.lt
  · exact (Nat.covBy_iff_add_one_eq.1 (h.grade ℕ)).symm

theorem not_covBy_mkK_mkI_none (hy : y ∈ K) (hx : x ∉ K) :
    ¬ mkK K y hy ⋖ mkI K none x hx :=
  PartialCylinderCarrier.not_covBy_inl_inr_none

theorem not_covBy_mkI_mkK (i : ArrowElt) (hy : y ∉ K) (hx : x ∈ K) :
    ¬ mkI K i y hy ⋖ mkK K x hx := fun h => h.1.le

theorem covBy_mkI_some_mkI_some (β γ : Bool) (hy : y ∉ K) (hx : x ∉ K) :
    mkI K (some β) y hy ⋖ mkI K (some γ) x hx ↔ β = γ ∧ y ⋖ x := by
  refine ⟨fun h => ⟨?_, proj_covBy_of_covBy_inr_some h⟩, ?_⟩
  · rcases h.1.le.1 with h' | h'
    · exact Option.some_inj.1 h'
    · cases h'
  · rintro ⟨rfl, h⟩
    exact PartialCylinderCarrier.covBy_iff.2
      ⟨PartialCylinderCarrier.lt_of_le_of_proj_lt ⟨Or.inl rfl, h.le⟩ h.lt,
        (Nat.covBy_iff_add_one_eq.1 (h.grade ℕ)).symm⟩

theorem covBy_mkI_some_mkI_none (β : Bool) (hy : y ∉ K) (hx : x ∉ K) :
    mkI K (some β) y hy ⋖ mkI K none x hx ↔ y = x := by
  refine PartialCylinderCarrier.covBy_iff.trans ?_
  constructor
  · rintro ⟨h1, h2⟩
    have h2 : grade ℕ x + 1 = grade ℕ y + 1 := h2
    exact GradeOrder.eq_of_le_of_grade_le h1.le.2 (by omega)
  · rintro rfl
    exact ⟨lt_of_le_of_ne ⟨Or.inr rfl, le_rfl⟩ (fun h => by cases h), rfl⟩

theorem not_covBy_mkI_none_mkI_some (γ : Bool) (hy : y ∉ K) (hx : x ∉ K) :
    ¬ mkI K none y hy ⋖ mkI K (some γ) x hx := by
  intro h
  rcases h.1.le.1 with h' | h' <;> cases h'

theorem covBy_mkI_none_mkI_none (hy : y ∉ K) (hx : x ∉ K) :
    mkI K none y hy ⋖ mkI K none x hx ↔ y ⋖ x := by
  refine ⟨PartialCylinderCarrier.proj_covBy_of_covBy_inr_none, fun h => ?_⟩
  refine PartialCylinderCarrier.covBy_iff.2
    ⟨PartialCylinderCarrier.lt_of_le_of_proj_lt ⟨Or.inl rfl, h.le⟩ h.lt, ?_⟩
  have := Nat.covBy_iff_add_one_eq.1 (h.grade ℕ)
  change grade ℕ x + 1 = grade ℕ y + 1 + 1
  omega

theorem orient_of_covBy {a b : partialCylinder U K} (h : b ⋖ a) :
    (partialCylinder U K).orient h = PartialCylinderCarrier.orientFn a b h := rfl

@[simp] theorem orient_mkI_none_mkI_some (β : Bool) (hx : x ∉ K)
    (h : mkI K (some β) x hx ⋖ mkI K none x hx) : (partialCylinder U K).orient h = β := rfl

theorem orient_mkI_none_mkI_none (hx : x ∉ K) (hy : y ∉ K) (h : y ⋖ x)
    (hc : mkI K none y hy ⋖ mkI K none x hx) : (partialCylinder U K).orient hc = !U.orient h := rfl

theorem orient_mkK (hx : x ∈ K) {b : partialCylinder U K} (h : b ⋖ mkK K x hx)
    (hp : partialCylinderProj U K b ⋖ x) : (partialCylinder U K).orient h = U.orient hp := rfl

theorem orient_mkI_some (β : Bool) (hx : x ∉ K) {b : partialCylinder U K}
    (h : b ⋖ mkI K (some β) x hx) (hp : partialCylinderProj U K b ⋖ x) :
    (partialCylinder U K).orient h = U.orient hp := rfl

@[simp] theorem grade_mkK (hx : x ∈ K) : grade ℕ (mkK K x hx) = grade ℕ x := rfl

@[simp] theorem grade_mkI_some (β : Bool) (hx : x ∉ K) :
    grade ℕ (mkI K (some β) x hx) = grade ℕ x := rfl

@[simp] theorem grade_mkI_none (hx : x ∉ K) :
    grade ℕ (mkI K none x hx) = grade ℕ x + 1 := rfl

@[simp] theorem proj_mkK (hx : x ∈ K) : partialCylinderProj U K (mkK K x hx) = x := rfl

@[simp] theorem proj_mkI (i : ArrowElt) (hx : x ∉ K) :
    partialCylinderProj U K (mkI K i x hx) = x := rfl

theorem proj_le_proj {a b : partialCylinder U K} (h : a ≤ b) :
    partialCylinderProj U K a ≤ partialCylinderProj U K b := PartialCylinderCarrier.proj_le_proj h

theorem exists_eq_mkK_of_le_mkK {a : partialCylinder U K} (hy : y ∈ K)
    (h : a ≤ mkK K y hy) : ∃ (z : U) (hz : z ∈ K), a = mkK K z hz := by
  rcases a with ⟨z, hz⟩ | ⟨i, ⟨z, hz⟩⟩
  · exact ⟨z, hz, rfl⟩
  · exact (PartialCylinderCarrier.not_inr_le_inl h).elim

theorem eq_mkK_of_proj_mem {a : partialCylinder U K}
    (h : partialCylinderProj U K a ∈ K) : a = mkK K _ h := by
  rcases a with ⟨z, hz⟩ | ⟨i, ⟨z, hz⟩⟩
  · rfl
  · exact (hz h).elim

theorem covBy_mkI_some_cases {β : Bool} (hx : x ∉ K) {c : partialCylinder U K}
    (hc : mkI K (some β) x hx ⋖ c) :
    c = mkI K none x hx ∨ ∃ (w : U) (hw : w ∉ K), x ⋖ w ∧ c = mkI K (some β) w hw := by
  rcases c with ⟨w, hw⟩ | ⟨⟨_ | γ⟩, ⟨w, hw⟩⟩
  · exact (PartialCylinderCarrier.not_inr_le_inl hc.1.le).elim
  · obtain rfl := (covBy_mkI_some_mkI_none β hx hw).1 hc; exact Or.inl rfl
  · obtain ⟨rfl, hcov⟩ := (covBy_mkI_some_mkI_some β γ hx hw).1 hc; exact Or.inr ⟨w, hw, hcov, rfl⟩

theorem grade_proj_le (z : partialCylinder U K) :
    grade ℕ (partialCylinderProj U K z) ≤ grade ℕ z := by
  rcases z with ⟨a, ha⟩ | ⟨⟨_ | β⟩, ⟨a, ha⟩⟩ <;> first | exact le_rfl | exact Nat.le_succ _

theorem grade_le_grade_proj_add_one (z : partialCylinder U K) :
    grade ℕ z ≤ grade ℕ (partialCylinderProj U K z) + 1 := by
  rcases z with ⟨x, hx⟩ | ⟨⟨_ | γ⟩, ⟨x, hx⟩⟩ <;> first | exact le_rfl | exact Nat.le_succ _

end PartialCylinder

open PartialCylinder

def partialCylinderEndpointFun (U : OGP.{u}) (K : LowerSet U) [DecidablePred (· ∈ K)] (α : Bool) :
    U → partialCylinder U K := fun x =>
  if h : x ∈ K then Sum.inl ⟨x, h⟩ else Sum.inr (⟨some α⟩, ⟨x, h⟩)

namespace PartialCylinder

variable {U : OGP.{u}} {K : LowerSet U} [DecidablePred (· ∈ K)] {x y : U}

theorem endpointFun_of_mem (α : Bool) (hx : x ∈ K) :
    partialCylinderEndpointFun U K α x = mkK K x hx := dif_pos hx

theorem endpointFun_of_notMem (α : Bool) (hx : x ∉ K) :
    partialCylinderEndpointFun U K α x = mkI K (some α) x hx := dif_neg hx

def endpointInitialSeg (U : OGP.{u}) (K : LowerSet U) [DecidablePred (· ∈ K)] (α : Bool) :
    U ≤i partialCylinder U K where
  toRelEmbedding :=
    (OrderEmbedding.ofMapLEIff (partialCylinderEndpointFun U K α) fun x y => by
      change PartialCylinderCarrier.le (partialCylinderEndpointFun U K α x)
        (partialCylinderEndpointFun U K α y) ↔ x ≤ y
      by_cases hx : x ∈ K <;> by_cases hy : y ∈ K <;>
        simp only [PartialCylinderCarrier.le, partialCylinderEndpointFun, hx, ↓reduceDIte, hy,
          false_iff, PartialCylinderCarrier.ArrowLE, reduceCtorEq, or_false, true_and]
      exact fun h => hx (K.lower h hy)).ltEmbedding
  mem_range_of_rel' {x b} h := by
    have hba : b ≤ partialCylinderEndpointFun U K α x := h.le
    refine ⟨partialCylinderProj U K b, ?_⟩
    change partialCylinderEndpointFun U K α (partialCylinderProj U K b) = b
    rcases b with ⟨z, hz⟩ | ⟨⟨i⟩, ⟨z, hz⟩⟩
    · exact endpointFun_of_mem α hz
    · by_cases hx : x ∈ K
      · rw [endpointFun_of_mem α hx] at hba; exact hba.elim
      · rw [endpointFun_of_notMem α hx] at hba
        rcases hba.1 with rfl | hfalse
        · exact endpointFun_of_notMem α hz
        · cases hfalse

end PartialCylinder

def partialCylinderEndpoint (U : OGP.{u}) (K : LowerSet U) [DecidablePred (· ∈ K)] (α : Bool) :
    U ⟶ partialCylinder U K :=
  ConcreteCategory.ofHom ⟨partialCylinderEndpointFun U K α,
    IsMorphism.of_initialSeg (endpointInitialSeg U K α) fun {x y} hxy => by
      have hc := (endpointInitialSeg U K α).apply_covBy_apply_iff.2 hxy
      change (partialCylinder U K).orient hc = U.orient hxy
      change partialCylinderEndpointFun U K α y ⋖ partialCylinderEndpointFun U K α x at hc
      revert hc
      change ∀ hc : partialCylinderEndpointFun U K α y ⋖ partialCylinderEndpointFun U K α x,
        (partialCylinder U K).orient hc = U.orient hxy
      by_cases hx : x ∈ K <;> by_cases hy : y ∈ K
      · simp only [endpointFun_of_mem α hx, endpointFun_of_mem α hy]; intro hc; rfl
      · exact (hy (K.lower hxy.le hx)).elim
      · simp only [endpointFun_of_notMem α hx, endpointFun_of_mem α hy]; intro hc; rfl
      · simp only [endpointFun_of_notMem α hx, endpointFun_of_notMem α hy]; intro hc; rfl⟩

instance isInclusion_partialCylinderEndpoint (U : OGP.{u}) (K : LowerSet U)
    [DecidablePred (· ∈ K)] (α : Bool) : IsInclusion (partialCylinderEndpoint U K α) :=
  ⟨(endpointInitialSeg U K α).injective⟩

namespace PartialCylinder

variable {U : OGP.{u}} {K : LowerSet U} {x y : U}

theorem endpoint_of_mem [DecidablePred (· ∈ K)] (α : Bool) (hx : x ∈ K) :
    partialCylinderEndpoint U K α x = mkK K x hx := dif_pos hx

theorem endpoint_of_notMem [DecidablePred (· ∈ K)] (α : Bool) (hx : x ∉ K) :
    partialCylinderEndpoint U K α x = mkI K (some α) x hx := dif_neg hx

end PartialCylinder

theorem partialCylinderProj_endpoint (U : OGP.{u}) (K : LowerSet U) [DecidablePred (· ∈ K)]
    (α : Bool) (x : U) :
    partialCylinderProj U K (partialCylinderEndpoint U K α x) = x := by
  by_cases hx : x ∈ K
  · rw [endpoint_of_mem α hx]; rfl
  · rw [endpoint_of_notMem α hx]; rfl

theorem surjective_partialCylinderProj (U : OGP.{u}) (K : LowerSet U) :
    Function.Surjective (partialCylinderProj U K) := fun x => by
  classical
  exact ⟨partialCylinderEndpoint U K false x, partialCylinderProj_endpoint U K false x⟩

namespace PartialCylinder

variable {U : OGP.{u}} {K : LowerSet U} {x y : U}

theorem mkI_eq_mkI_iff {i j : ArrowElt} (hx : x ∉ K) (hy : y ∉ K) :
    mkI K i x hx = mkI K j y hy ↔ i = j ∧ x = y :=
  Sum.inr_injective.eq_iff.trans
    (by simp only [Prod.mk.injEq, ULift.up.injEq, Subtype.mk.injEq])

theorem mkK_eq_mkK_iff (hx : x ∈ K) (hy : y ∈ K) : mkK K x hx = mkK K y hy ↔ x = y :=
  Sum.inl_injective.eq_iff.trans (by simp)

theorem mkK_ne_mkI {i : ArrowElt} (hx : x ∈ K) (hy : y ∉ K) : mkK K x hx ≠ mkI K i y hy :=
  fun h => by cases h

variable (K) in
def over (V : LowerSet U) : LowerSet (partialCylinder U K) :=
  ⟨partialCylinderProj U K ⁻¹' V, V.lower.preimage fun _ _ h => proj_le_proj h⟩

instance decidableMemOver (V : LowerSet U) [DecidablePred (· ∈ V)] :
    DecidablePred (· ∈ over K V) := fun a =>
  inferInstanceAs (Decidable (partialCylinderProj U K a ∈ V))

variable (K) in
def InCopy (α : Bool) (V : LowerSet U) : partialCylinder U K → Prop
  | Sum.inl x => x.1 ∈ V
  | Sum.inr (⟨some β⟩, x) => β = α ∧ x.1 ∈ V
  | Sum.inr (⟨none⟩, _) => False

variable (K) in
def copy (α : Bool) (V : LowerSet U) : LowerSet (partialCylinder U K) where
  carrier := {a | InCopy K α V a}
  lower' := by
    rintro (x | ⟨⟨_ | β⟩, x⟩) (y | ⟨⟨_ | γ⟩, y⟩) h ha <;>
      try first | exact V.lower h ha | exact h.elim | exact False.elim ha | exact V.lower h ha.2
    · rcases h.1 with h' | h' <;> cases h'
    · rcases h.1 with h' | h'
      · exact ⟨(Option.some_inj.1 h').trans ha.1, V.lower h.2 ha.2⟩
      · cases h'

instance decidableMemCopy (α : Bool) (V : LowerSet U) [DecidablePred (· ∈ V)] :
    DecidablePred (· ∈ copy K α V)
  | Sum.inl x => inferInstanceAs (Decidable (x.1 ∈ V))
  | Sum.inr (⟨some β⟩, x) => inferInstanceAs (Decidable (β = α ∧ x.1 ∈ V))
  | Sum.inr (⟨none⟩, _) => isFalse id

@[simp] theorem mem_over {V : LowerSet U} {a : partialCylinder U K} :
    a ∈ over K V ↔ partialCylinderProj U K a ∈ V := Iff.rfl

@[simp] theorem mkK_mem_copy {V : LowerSet U} {α : Bool} (hx : x ∈ K) :
    mkK K x hx ∈ copy K α V ↔ x ∈ V := Iff.rfl

@[simp] theorem mkI_some_mem_copy {V : LowerSet U} {α β : Bool} (hx : x ∉ K) :
    mkI K (some β) x hx ∈ copy K α V ↔ β = α ∧ x ∈ V := Iff.rfl

@[simp] theorem mkI_none_notMem_copy {V : LowerSet U} {α : Bool} (hx : x ∉ K) :
    mkI K none x hx ∉ copy K α V := id

theorem mem_copy [DecidablePred (· ∈ K)] {V : LowerSet U} {α : Bool} {a : partialCylinder U K} :
    a ∈ copy K α V ↔ partialCylinderProj U K a ∈ V ∧
      partialCylinderEndpoint U K α (partialCylinderProj U K a) = a := by
  rcases a with ⟨x, hx⟩ | ⟨⟨_ | β⟩, ⟨x, hx⟩⟩
  · rw [mkK_mem_copy, proj_mkK, endpoint_of_mem α hx]; simp
  · rw [proj_mkI, endpoint_of_notMem α hx, mkI_eq_mkI_iff]
    exact ⟨fun h => False.elim h, fun h => by simp at h⟩
  · rw [mkI_some_mem_copy, proj_mkI, endpoint_of_notMem α hx, mkI_eq_mkI_iff]
    simp [eq_comm, and_comm]

@[simp] theorem map_partialCylinderEndpoint [DecidablePred (· ∈ K)] (α : Bool) (V : LowerSet U) :
    map (partialCylinderEndpoint U K α) V = copy K α V :=
  SetLike.ext fun a => by
    rw [mem_map, mem_copy]
    exact ⟨fun ⟨x, hx, h⟩ => h ▸ by rw [partialCylinderProj_endpoint]; exact ⟨hx, rfl⟩,
      fun ⟨hx, h⟩ => ⟨_, hx, h⟩⟩

theorem copy_le_over (α : Bool) (V : LowerSet U) : copy K α V ≤ over K V := by
  rintro (x | ⟨⟨_ | β⟩, x⟩) h <;> first | exact h | exact False.elim h | exact h.2

theorem mkI_none_mem_facesIn_over {V : LowerSet U} {α : Bool} (hx : x ∉ K) :
    mkI K none x hx ∈ (partialCylinder U K).facesIn (over K V) (grade ℕ x + 1) α ↔
      x ∈ U.facesIn V (grade ℕ x) (!α) := by
  simp only [facesIn, mem_ofPred_eq, SetLike.mem_coe, mem_over, proj_mkI, grade_mkI_none, true_and,
    Bool.not_not, disjoint_left, mem_cofaces]
  refine and_congr_right fun _ => ⟨fun h y ⟨hcov, hor⟩ hyV => ?_, fun h b ⟨hcov, hor⟩ hbV => ?_⟩
  · have hy : y ∉ K := fun hy => hx (K.lower hcov.le hy)
    exact h ⟨(covBy_mkI_none_mkI_none hx hy).2 hcov, congrArg (!·) hor⟩ hyV
  · rcases b with ⟨y, hy⟩ | ⟨⟨_ | γ⟩, ⟨y, hy⟩⟩
    · exact not_covBy_mkI_mkK _ hx hy hcov
    · refine h ⟨(covBy_mkI_none_mkI_none hx hy).1 hcov, ?_⟩ hbV
      change (!U.orient _) = !α at hor
      simpa using hor
    · exact not_covBy_mkI_none_mkI_some γ hx hy hcov

theorem mkI_some_mem_facesIn_over {V : LowerSet U} {n : ℕ} {α β : Bool} (hx : x ∉ K) :
    mkI K (some β) x hx ∈ (partialCylinder U K).facesIn (over K V) n α ↔
      β = α ∧ x ∈ U.facesIn V n α := by
  simp only [facesIn, mem_ofPred_eq, SetLike.mem_coe, mem_over, proj_mkI, grade_mkI_some,
    disjoint_left, mem_cofaces]
  constructor
  · rintro ⟨hxV, hxn, h⟩
    refine ⟨?_, hxV, hxn, fun y ⟨hcov, hor⟩ hyV => ?_⟩
    · by_contra hne
      refine h (a := mkI K none x hx) ⟨(covBy_mkI_some_mkI_none β hx hx).2 rfl, ?_⟩ hxV
      rw [orient_mkI_none_mkI_some]
      cases α <;> cases β <;> first | exact absurd rfl hne | rfl
    · have hy : y ∉ K := fun hy => hx (K.lower hcov.le hy)
      have hc := (covBy_mkI_some_mkI_some (K := K) β β hx hy).2 ⟨rfl, hcov⟩
      exact h (a := mkI K (some β) y hy) ⟨hc, hor⟩ hyV
  · rintro ⟨rfl, hxV, hxn, h⟩
    refine ⟨hxV, hxn, fun b ⟨hcov, hor⟩ hbV => ?_⟩
    rcases b with ⟨y, hy⟩ | ⟨⟨_ | γ⟩, ⟨y, hy⟩⟩
    · exact not_covBy_mkI_mkK _ hx hy hcov
    · have hor' : β = !β := hor
      cases β <;> simp at hor'
    · obtain ⟨-, hcov'⟩ := (covBy_mkI_some_mkI_some β γ hx hy).1 hcov
      exact h ⟨hcov', hor⟩ hbV

theorem mkK_mem_facesIn_over {V : LowerSet U} {n : ℕ} {α : Bool} (hx : x ∈ K) :
    mkK K x hx ∈ (partialCylinder U K).facesIn (over K V) n α ↔ x ∈ U.facesIn V n α := by
  simp only [facesIn, mem_ofPred_eq, SetLike.mem_coe, mem_over, proj_mkK, grade_mkK,
    disjoint_left, mem_cofaces]
  refine and_congr_right fun _ => and_congr_right fun _ =>
    ⟨fun h y ⟨hcov, hor⟩ hyV => ?_, fun h b ⟨hcov, hor⟩ hbV => ?_⟩
  · by_cases hy : y ∈ K
    · have hc := (covBy_mkK_mkK (K := K) hx hy).2 hcov
      exact h (a := mkK K y hy) ⟨hc, hor⟩ hyV
    · have hc := (covBy_mkK_mkI_some (K := K) hx false hy).2 hcov
      exact h (a := mkI K (some false) y hy) ⟨hc, hor⟩ hyV
  · rcases b with ⟨y, hy⟩ | ⟨⟨_ | γ⟩, ⟨y, hy⟩⟩
    · exact h ⟨(covBy_mkK_mkK hx hy).1 hcov, hor⟩ hbV
    · exact not_covBy_mkK_mkI_none hx hy hcov
    · exact h ⟨(covBy_mkK_mkI_some hx γ hy).1 hcov, hor⟩ hbV

theorem mkI_none_maximal_over {V : LowerSet U} (hx : x ∉ K) :
    Maximal (· ∈ over K V) (mkI K none x hx) ↔ Maximal (· ∈ V) x := by
  refine ⟨fun ⟨hxV, h⟩ => ⟨hxV, fun y hyV hxy => ?_⟩,
    fun ⟨hxV, h⟩ => ⟨hxV, fun b hbV hxb => ?_⟩⟩
  · have hy : y ∉ K := fun hy => hx (K.lower hxy hy)
    exact (@h (mkI K none y hy) hyV ⟨Or.inl rfl, hxy⟩).2
  · rcases b with ⟨y, hy⟩ | ⟨⟨_ | γ⟩, ⟨y, hy⟩⟩
    · exact hxb.elim
    · exact ⟨Or.inl rfl, h hbV hxb.2⟩
    · rcases hxb.1 with h' | h' <;> cases h'

theorem mkI_some_not_maximal_over {V : LowerSet U} (β : Bool) (hx : x ∉ K) :
    ¬ Maximal (· ∈ over K V) (mkI K (some β) x hx) := by
  rintro ⟨hxV, h⟩
  have hle := @h (mkI K none x hx) hxV ⟨Or.inr rfl, le_rfl⟩
  rcases hle.1 with h' | h' <;> cases h'

theorem mkK_maximal_over {V : LowerSet U} (hx : x ∈ K) :
    Maximal (· ∈ over K V) (mkK K x hx) ↔ Maximal (· ∈ V) x := by
  refine ⟨fun ⟨hxV, h⟩ => ⟨hxV, fun y hyV hxy => ?_⟩,
    fun ⟨hxV, h⟩ => ⟨hxV, fun b hbV hxb => ?_⟩⟩
  · by_cases hy : y ∈ K
    · exact @h (mkK K y hy) hyV hxy
    · exact (@h (mkI K (some false) y hy) hyV hxy).elim
  · rcases b with ⟨y, hy⟩ | ⟨i, ⟨y, hy⟩⟩
    · exact h hbV hxb
    · have hxy : x ≤ y := hxb
      obtain rfl : x = y := le_antisymm hxy (h hbV hxy)
      exact (hy hx).elim

theorem le_mkI_none_of_proj_le {a : partialCylinder U K} (hx : x ∉ K)
    (h : partialCylinderProj U K a ≤ x) : a ≤ mkI K none x hx := by
  rcases a with ⟨y, hy⟩ | ⟨i, ⟨y, hy⟩⟩
  · exact h
  · exact ⟨Or.inr rfl, h⟩

theorem endpoint_le_mkI_none [DecidablePred (· ∈ K)] (α : Bool) (hx : x ∉ K) (h : y ≤ x) :
    partialCylinderEndpoint U K α y ≤ mkI K none x hx :=
  le_mkI_none_of_proj_le hx (by rw [partialCylinderProj_endpoint]; exact h)

theorem copy_boundary_le_boundary_over (V : LowerSet U) (m : ℕ) (α : Bool) :
    copy K α (U.boundary V m α) ≤ (partialCylinder U K).boundary (over K V) m α := by
  classical
  rw [← map_partialCylinderEndpoint]
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨w, hw, hyw⟩ := mem_boundary.1 hy
  have hle : partialCylinderEndpoint U K α y ≤ partialCylinderEndpoint U K α w :=
    (isMorphism (partialCylinderEndpoint U K α)).monotone hyw
  refine ((partialCylinder U K).boundary (over K V) m α).lower hle ?_
  rcases hw with hf | ⟨hm, hd⟩
  · refine mem_boundary_of_mem_facesIn ?_ le_rfl
    by_cases hwK : w ∈ K
    · rw [endpoint_of_mem α hwK]; exact (mkK_mem_facesIn_over hwK).2 hf
    · rw [endpoint_of_notMem α hwK]; exact (mkI_some_mem_facesIn_over hwK).2 ⟨rfl, hf⟩
  · by_cases hwK : w ∈ K
    · rw [endpoint_of_mem α hwK]
      exact mem_boundary_of_maximal ((mkK_maximal_over hwK).2 hm) hd le_rfl
    · have hle' := endpoint_le_mkI_none (K := K) α hwK (le_refl w)
      refine ((partialCylinder U K).boundary (over K V) m α).lower hle' ?_
      rcases Nat.lt_or_ge (grade ℕ w + 1) m with h | h
      · exact mem_boundary_of_maximal ((mkI_none_maximal_over hwK).2 hm) h le_rfl
      · have hmw : m = grade ℕ w + 1 := by omega
        rw [hmw]
        exact mem_boundary_of_mem_facesIn
          ((mkI_none_mem_facesIn_over hwK).2 (maximal_mem_iff_forall_mem_facesIn.1 hm (!α)))
          le_rfl

theorem mem_copy_or_mem_over_of_mem_boundary_over {V : LowerSet U} {m : ℕ} {α : Bool}
    {z : partialCylinder U K}
    (hz : z ∈ (partialCylinder U K).boundary (over K V) m α) :
    z ∈ copy K α (U.boundary V m α) ∨
      (0 < m ∧ z ∈ over K (U.boundary V (m - 1) (!α))) := by
  classical
  obtain ⟨w, hw, hzw⟩ := mem_boundary.1 hz
  have hB : ∀ x, x ∈ U.boundary V m α →
      partialCylinderEndpoint U K α x = w → z ∈ copy K α (U.boundary V m α) := by
    intro x hx hxw
    refine (copy K α (U.boundary V m α)).lower hzw ?_
    rw [← hxw, ← map_partialCylinderEndpoint]
    exact ⟨x, hx, rfl⟩
  have hT : partialCylinderProj U K w ∈ U.boundary V (m - 1) (!α) →
      z ∈ over K (U.boundary V (m - 1) (!α)) :=
    (over K (U.boundary V (m - 1) (!α))).lower hzw
  rcases w with ⟨x, hx⟩ | ⟨⟨_ | β⟩, ⟨x, hx⟩⟩
  · refine Or.inl (hB x ?_ (endpoint_of_mem α hx))
    rcases hw with hf | ⟨hm, hd⟩
    · exact mem_boundary_of_mem_facesIn ((mkK_mem_facesIn_over hx).1 hf) le_rfl
    · exact mem_boundary_of_maximal ((mkK_maximal_over hx).1 hm) hd le_rfl
  · rcases hw with hf | ⟨hm, hd⟩
    · have hd : grade ℕ x + 1 = m := hf.2.1
      have hfx : x ∈ U.facesIn V (m - 1) (!α) := by
        rw [show m - 1 = grade ℕ x by omega]
        exact (mkI_none_mem_facesIn_over hx).1 (hd ▸ hf)
      exact Or.inr ⟨by omega, hT (mem_boundary_of_mem_facesIn hfx le_rfl)⟩
    · have hd : grade ℕ x + 1 < m := hd
      exact Or.inr ⟨by omega, hT
        (mem_boundary_of_maximal ((mkI_none_maximal_over hx).1 hm) (by omega) le_rfl)⟩
  · rcases hw with hf | ⟨hm, -⟩
    · obtain ⟨rfl, hf⟩ := (mkI_some_mem_facesIn_over hx).1 hf
      exact Or.inl (hB x (mem_boundary_of_mem_facesIn hf le_rfl) (endpoint_of_notMem β hx))
    · exact (mkI_some_not_maximal_over β hx hm).elim

theorem boundary_over_zero (V : LowerSet U) (α : Bool) :
    (partialCylinder U K).boundary (over K V) 0 α = copy K α (U.boundary V 0 α) := by
  refine le_antisymm (fun z hz => ?_) (copy_boundary_le_boundary_over V 0 α)
  rcases mem_copy_or_mem_over_of_mem_boundary_over hz with h | ⟨h, -⟩
  · exact h
  · exact absurd h (lt_irrefl 0)

theorem boundary_over_succ {V : LowerSet U} (hg : U.IsGlobular V) (n : ℕ) (α : Bool) :
    (partialCylinder U K).boundary (over K V) (n + 1) α =
      copy K α (U.boundary V (n + 1) α) ⊔ over K (U.boundary V n (!α)) := by
  refine le_antisymm (fun z hz => ?_) (sup_le
    (copy_boundary_le_boundary_over V (n + 1) α) (fun z hz => ?_))
  · exact (mem_copy_or_mem_over_of_mem_boundary_over hz).imp_right And.right
  · have hy := mem_over.1 hz
    rcases z with ⟨y, hy'⟩ | ⟨i, ⟨y, hy'⟩⟩
    · refine copy_boundary_le_boundary_over V (n + 1) α ?_
      exact (mkK_mem_copy hy').2
        (hg.boundary_le_boundary (Nat.lt_succ_self n) (!α) α hy)
    · obtain ⟨w, hw, hyw⟩ := mem_boundary.1 hy
      have hwK : w ∉ K := fun h => hy' (K.lower hyw h)
      refine ((partialCylinder U K).boundary (over K V) (n + 1) α).lower
        (le_mkI_none_of_proj_le hwK hyw) ?_
      rcases hw with hf | ⟨hm, hd⟩
      · have hgn : grade ℕ w = n := hf.2.1
        rw [← hgn]
        exact mem_boundary_of_mem_facesIn ((mkI_none_mem_facesIn_over hwK).2 (hgn ▸ hf)) le_rfl
      · exact mem_boundary_of_maximal ((mkI_none_maximal_over hwK).2 hm)
          (Nat.add_lt_add_right hd 1) le_rfl

theorem over_boundary_le_boundary_over {V : LowerSet U} (hg : U.IsGlobular V)
    (n : ℕ) (α : Bool) :
    over K (U.boundary V n (!α)) ≤ (partialCylinder U K).boundary (over K V) (n + 1) α := by
  rw [boundary_over_succ hg]; exact le_sup_right

theorem over_sup (A B : LowerSet U) : over K (A ⊔ B) = over K A ⊔ over K B := rfl

theorem over_inf (A B : LowerSet U) : over K (A ⊓ B) = over K A ⊓ over K B := rfl

theorem over_mono {A B : LowerSet U} (h : A ≤ B) : over K A ≤ over K B := fun _ hz => h hz

@[simp] theorem over_top : over K (⊤ : LowerSet U) = ⊤ := rfl

@[simp] theorem over_bot : over K (⊥ : LowerSet U) = ⊥ := rfl

@[simp] theorem over_eq_bot_iff {V : LowerSet U} : over K V = ⊥ ↔ V = ⊥ := by
  rw [← SetLike.coe_set_eq, ← SetLike.coe_set_eq (p := V)]
  change partialCylinderProj U K ⁻¹' (V : Set U) = ∅ ↔ (V : Set U) = ∅
  exact (surjective_partialCylinderProj U K).preimage_injective.eq_iff
    (a := (V : Set U)) (b := ∅)

theorem krullDim_over_le {V : LowerSet U} {n : ℕ} (hV : krullDim V ≤ n) :
    krullDim (over K V) ≤ (n + 1 : ℕ) :=
  krullDim_le_coe_iff.2 fun z =>
    (grade_le_grade_proj_add_one z.1).trans
      (Nat.add_le_add_right (krullDim_le_coe_iff.1 hV ⟨_, z.2⟩) 1)

theorem grade_add_one_le_krullDim_over {V : LowerSet U} (hxV : x ∈ V) (hx : x ∉ K) :
    ((grade ℕ x + 1 : ℕ) : WithBot ℕ∞) ≤ krullDim (over K V) :=
  grade_le_krullDim (⟨mkI K none x hx, hxV⟩ : over K V)

theorem copy_sup (α : Bool) (A B : LowerSet U) :
    copy K α (A ⊔ B) = copy K α A ⊔ copy K α B := by
  classical
  rw [← map_partialCylinderEndpoint, ← map_partialCylinderEndpoint,
    ← map_partialCylinderEndpoint, map_sup]

theorem copy_inf (α : Bool) (A B : LowerSet U) :
    copy K α (A ⊓ B) = copy K α A ⊓ copy K α B := by
  classical
  rw [← map_partialCylinderEndpoint, ← map_partialCylinderEndpoint,
    ← map_partialCylinderEndpoint, map_inf]

theorem copy_mono {A B : LowerSet U} (α : Bool) (h : A ≤ B) :
    copy K α A ≤ copy K α B := by
  classical
  rw [← map_partialCylinderEndpoint, ← map_partialCylinderEndpoint]
  exact map_mono _ h

@[simp] theorem copy_inj {A B : LowerSet U} (α : Bool) :
    copy K α A = copy K α B ↔ A = B := by
  classical
  rw [← map_partialCylinderEndpoint, ← map_partialCylinderEndpoint, map_inj]

@[simp] theorem copy_eq_bot_iff {A : LowerSet U} (α : Bool) :
    copy K α A = ⊥ ↔ A = ⊥ := by
  classical
  rw [← map_partialCylinderEndpoint, map_eq_bot_iff]

@[simp] theorem krullDim_copy (α : Bool) (V : LowerSet U) :
    krullDim (copy K α V) = krullDim V := by
  classical
  rw [← map_partialCylinderEndpoint, krullDim_map]

theorem copy_inf_over (α : Bool) (A B : LowerSet U) :
    copy K α A ⊓ over K B = copy K α (A ⊓ B) := by
  classical
  exact SetLike.ext fun z => by simp only [LowerSet.mem_inf_iff, mem_copy, mem_over]; tauto

theorem copy_inf_copy_not (β : Bool) (A B : LowerSet U) :
    copy K β A ⊓ copy K (!β) B = copy K β (A ⊓ B ⊓ K) := by
  classical
  refine SetLike.ext fun z => ?_
  simp only [LowerSet.mem_inf_iff, mem_copy]
  constructor
  · rintro ⟨⟨hA, hβ⟩, hB, hnβ⟩
    refine ⟨⟨⟨hA, hB⟩, ?_⟩, hβ⟩
    by_contra hz
    rw [endpoint_of_notMem β hz] at hβ
    rw [endpoint_of_notMem (!β) hz] at hnβ
    have h := hβ.trans hnβ.symm
    have h2 : (some β : ArrowElt) = some (!β) := congrArg (fun p => p.1.down) (Sum.inr.inj h)
    cases β <;> simp at h2
  · rintro ⟨⟨⟨hA, hB⟩, hz⟩, hβ⟩
    refine ⟨⟨hA, hβ⟩, hB, ?_⟩
    rw [endpoint_of_mem (!β) hz, ← endpoint_of_mem β hz, hβ]

theorem over_eq_copy_of_le {A : LowerSet U} (h : A ≤ K) (α : Bool) :
    over K A = copy K α A := by
  classical
  refine SetLike.ext fun z => ?_
  rw [mem_over, mem_copy]
  exact ⟨fun hz => ⟨hz, (endpoint_of_mem α (h hz)).trans (eq_mkK_of_proj_mem (h hz)).symm⟩,
    And.left⟩

theorem boundary_over_boundary {V : LowerSet U} (hg : U.IsGlobular V) (n : ℕ) (α : Bool) :
    (partialCylinder U K).boundary (over K V) n α =
      (partialCylinder U K).boundary (over K (U.boundary V n α)) n α := by
  have hgB := hg.boundary n α
  have hself : U.boundary (U.boundary V n α) n α = U.boundary V n α :=
    boundary_eq_self (krullDim_boundary_le V n α) α
  rcases n with _ | m
  · rw [boundary_over_zero, boundary_over_zero, hself]
  · rw [boundary_over_succ hg, boundary_over_succ hgB, hself,
      hg m (m + 1) (Nat.lt_succ_self m)]

theorem Iic_mkI_none (hx : x ∉ K) :
    LowerSet.Iic (mkI K none x hx) = over K (LowerSet.Iic x) :=
  SetLike.ext fun _ => ⟨fun h => proj_le_proj h, fun h => le_mkI_none_of_proj_le hx h⟩

theorem Iic_endpoint [DecidablePred (· ∈ K)] (β : Bool) (x : U) :
    LowerSet.Iic (partialCylinderEndpoint U K β x) = copy K β (LowerSet.Iic x) := by
  rw [← map_partialCylinderEndpoint, map_Iic]

theorem boundary_copy (β : Bool) (W : LowerSet U) (n : ℕ) (α : Bool) :
    (partialCylinder U K).boundary (copy K β W) n α = copy K β (U.boundary W n α) := by
  classical
  rw [← map_partialCylinderEndpoint, ← map_partialCylinderEndpoint, map_boundary]

theorem image_proj_copy (β : Bool) (W : LowerSet U) :
    partialCylinderProj U K '' (copy K β W : Set (partialCylinder U K)) = W := by
  classical
  rw [← map_partialCylinderEndpoint, coe_map, ← image_comp]
  ext w
  simp [partialCylinderProj_endpoint]

theorem image_proj_over (W : LowerSet U) :
    partialCylinderProj U K '' (over K W : Set (partialCylinder U K)) = W :=
  (surjective_partialCylinderProj U K).image_preimage _

theorem image_over_comp {W : OGP.{u}} (p : U → W) (B : LowerSet U) :
    (fun a => p (partialCylinderProj U K a)) '' (over K B : Set (partialCylinder U K)) =
      p '' B := by
  rw [← image_image, image_proj_over]

theorem image_copy_comp {W : OGP.{u}} (p : U → W) (β : Bool) (B : LowerSet U) :
    (fun a => p (partialCylinderProj U K a)) '' (copy K β B : Set (partialCylinder U K)) =
      p '' B := by
  rw [← image_image, image_proj_copy]

theorem eq_endpoint_or_eq_mkI_none [DecidablePred (· ∈ K)] (a : partialCylinder U K) :
    (∃ β x, a = partialCylinderEndpoint U K β x) ∨ ∃ x hx, a = mkI K none x hx := by
  rcases a with ⟨x, hx⟩ | ⟨⟨_ | β⟩, ⟨x, hx⟩⟩
  · exact Or.inl ⟨false, x, (endpoint_of_mem false hx).symm⟩
  · exact Or.inr ⟨x, hx, rfl⟩
  · exact Or.inl ⟨β, x, (endpoint_of_notMem β hx).symm⟩

end PartialCylinder

open PartialCylinder

theorem eq_endpoint_of_proj_mem {U : OGP.{u}} {K : LowerSet U} [DecidablePred (· ∈ K)]
    (z : partialCylinder U K) (h : partialCylinderProj U K z ∈ K) (β : Bool) :
    z = partialCylinderEndpoint U K β (partialCylinderProj U K z) := by
  rcases z with ⟨y, hy⟩ | ⟨i, ⟨y, hy⟩⟩
  · exact (endpoint_of_mem β hy).symm
  · exact (hy h).elim

theorem monotone_partialCylinderProj (U : OGP.{u}) (K : LowerSet U) :
    Monotone (partialCylinderProj U K) :=
  fun _ _ h => proj_le_proj h

instance functor_isFibered_partialCylinderProj (U : OGP.{u}) (K : LowerSet U) :
    (monotone_partialCylinderProj U K).functor.IsFibered := by
  refine (Monotone.functor_isFibered_iff _).2 fun a y hy => ?_
  by_cases hyK : y ∈ K
  · refine ⟨mkK K y hyK, ?_, rfl, fun z _ hz => ?_⟩
    · rcases a with ⟨x, hx⟩ | ⟨i, ⟨x, hx⟩⟩
      · exact hy
      · exact hy
    · rcases z with ⟨w, hw⟩ | ⟨i, ⟨w, hw⟩⟩
      · exact hz
      · exact (hw (K.lower hz hyK)).elim
  · rcases a with ⟨x, hx⟩ | ⟨⟨i⟩, ⟨x, hx⟩⟩
    · exact (hyK (K.lower hy hx)).elim
    · refine ⟨mkI K i y hyK, ⟨Or.inl rfl, hy⟩, rfl, fun z hza hz => ?_⟩
      rcases z with ⟨w, hw⟩ | ⟨j, ⟨w, hw⟩⟩
      · exact hz
      · exact ⟨hza.1, hz⟩

theorem isClosedMap_partialCylinderProj (U : OGP.{u}) (K : LowerSet U) :
    IsClosedMap (partialCylinderProj U K) :=
  IsUpperSet.isClosedMap_iff_fibration.2 fun a y hy => by
    obtain ⟨b, hba, rfl, -⟩ := Monotone.exists_lift (monotone_partialCylinderProj U K) hy
    exact ⟨b, hba, rfl⟩

theorem isMap_partialCylinderProj {U : OGP.{u}} (hU : IsMolecule U) (K : LowerSet U) :
    IsMap (partialCylinderProj U K) := by
  classical
  have hg : ∀ x : U, U.IsGlobular (.Iic x) := fun x =>
    (isRDC_of_isMolecule hU x).isGlobular
  have himg (a : partialCylinder U K) (n : ℕ) (α : Bool) :
      partialCylinderProj U K ''
          ((partialCylinder U K).boundary (.Iic a) n α : Set (partialCylinder U K)) =
        (U.boundary (.Iic (partialCylinderProj U K a)) n α : Set U) := by
    rcases eq_endpoint_or_eq_mkI_none a with ⟨β, x, rfl⟩ | ⟨x, hx, rfl⟩
    · rw [Iic_endpoint, boundary_copy, image_proj_copy, partialCylinderProj_endpoint]
    · rw [Iic_mkI_none, proj_mkI]
      rcases n with _ | n
      · rw [boundary_over_zero, image_proj_copy]
      · rw [boundary_over_succ (hg x), LowerSet.coe_sup, image_union, image_proj_copy,
          image_proj_over, ← LowerSet.coe_sup]
        exact congrArg SetLike.coe (sup_eq_left.2
          ((hg x).boundary_le_boundary (Nat.lt_succ_self n) (!α) α))
  refine ⟨isClosedMap_partialCylinderProj U K, fun a n α =>
    finalOn_of_fibration (isClosedMap_partialCylinderProj U K) (himg a n α) ?_⟩
  intro y hy z hz h
  rcases eq_endpoint_or_eq_mkI_none a with ⟨β, x, rfl⟩ | ⟨x, hx, rfl⟩
  · rw [Iic_endpoint, boundary_copy] at hy hz
    have hy' := (mem_copy.1 hy).2
    have hz' := (mem_copy.1 hz).2
    rw [← hy', ← hz', h]
  · rw [Iic_mkI_none] at hy hz ⊢
    set S := (partialCylinder U K).boundary (over K (.Iic x)) n α
    rcases y with ⟨y, hy'⟩ | ⟨⟨_ | β⟩, ⟨y, hy'⟩⟩ <;>
      rcases z with ⟨z, hz'⟩ | ⟨⟨_ | γ⟩, ⟨z, hz'⟩⟩ <;>
      have h : y = z := h <;> subst h
    · exact Relation.ReflTransGen.refl
    · exact (hz' hy').elim
    · exact (hz' hy').elim
    · exact (hy' hz').elim
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single ⟨⟨hy, le_rfl⟩, ⟨hz, le_rfl⟩, Or.inr ⟨Or.inr rfl, le_rfl⟩⟩
    · exact (hy' hz').elim
    · exact Relation.ReflTransGen.single ⟨⟨hy, le_rfl⟩, ⟨hz, le_rfl⟩, Or.inl ⟨Or.inr rfl, le_rfl⟩⟩
    · by_cases hβγ : β = γ
      · subst hβγ; exact Relation.ReflTransGen.refl
      · have hmid : mkI K none y hy' ∈ S := by
          have key : ∀ δ, mkI K (some δ) y hy' ∈ S → δ ≠ α → mkI K none y hy' ∈ S := by
            intro δ hδ hne
            rcases mem_copy_or_mem_over_of_mem_boundary_over hδ with h' | ⟨hn, h'⟩
            · exact (hne ((mkI_some_mem_copy hy').1 h').1).elim
            · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
              exact over_boundary_le_boundary_over (hg x) m α
                (mem_over.2 (mem_over.1 h'))
          by_cases hβ : β = α
          · exact key γ hz (fun h => hβγ (hβ.trans h.symm))
          · exact key β hy hβ
        exact Relation.ReflTransGen.tail
          (Relation.ReflTransGen.single
            ⟨⟨hy, le_rfl⟩, ⟨hmid, le_rfl⟩, Or.inl ⟨Or.inr rfl, le_rfl⟩⟩)
          ⟨⟨hmid, le_rfl⟩, ⟨hz, le_rfl⟩, Or.inr ⟨Or.inr rfl, le_rfl⟩⟩

def partialCylinderEmptyEquiv (U : OGP.{u}) :
    partialCylinder U ⊥ ≃o grayProduct (globe.{u} 1) U where
  toFun
    | Sum.inl x => False.elim x.2
    | Sum.inr (⟨some β⟩, x) => (SuspCarrier.pole β, x.1)
    | Sum.inr (⟨none⟩, x) => (SuspCarrier.susp PUnit.unit, x.1)
  invFun
    | (SuspCarrier.pole β, x) => Sum.inr (⟨some β⟩, ⟨x, id⟩)
    | (SuspCarrier.susp _, x) => Sum.inr (⟨none⟩, ⟨x, id⟩)
  left_inv a := by
    rcases a with ⟨x, hx⟩ | ⟨⟨_ | β⟩, ⟨x, hx⟩⟩ <;> first | exact False.elim hx | rfl
  right_inv p := by rcases p with ⟨β | ⟨⟩, x⟩ <;> rfl
  map_rel_iff' {a b} := by
    rcases a with ⟨x, hx⟩ | ⟨⟨_ | β⟩, ⟨x, hx⟩⟩
    · exact False.elim hx
    all_goals rcases b with ⟨y, hy⟩ | ⟨⟨_ | γ⟩, ⟨y, hy⟩⟩
    all_goals try exact False.elim hy
    · exact ⟨fun h => ⟨Or.inl rfl, h.2⟩, fun h => ⟨le_rfl, h.2⟩⟩
    · exact ⟨fun h => h.1.elim, fun h => by rcases h.1 with h' | h' <;> cases h'⟩
    · exact ⟨fun h => ⟨Or.inr rfl, h.2⟩, fun h => ⟨trivial, h.2⟩⟩
    · refine ⟨fun h => ⟨Or.inl (congrArg some h.1), h.2⟩, fun h => ⟨?_, h.2⟩⟩
      rcases h.1 with h' | h'
      · exact Option.some_inj.1 h'
      · cases h'

def partialCylinderEmptyIso (U : OGP.{u}) :
    partialCylinder U ⊥ ≅ grayProduct (globe.{u} 1) U :=
  isoMk (partialCylinderEmptyEquiv U) fun {a b} h => by
    rcases a with ⟨x, hx⟩ | ⟨⟨_ | γ⟩, ⟨x, hx⟩⟩
    · exact False.elim hx
    all_goals rcases b with ⟨y, hy⟩ | ⟨⟨_ | β⟩, ⟨y, hy⟩⟩
    all_goals try exact False.elim hy
    · have hyx := (covBy_mkI_none_mkI_none hy hx).1 h
      refine (grayProduct_orient_of_covBy_snd (P := globe.{u} 1)
        (SuspCarrier.susp PUnit.unit) hyx _).trans ?_
      change xor true (U.orient hyx) = !U.orient _
      exact (Bool.true_xor _).trans (congrArg (!·) (U.orient_congr rfl rfl hyx _))
    · obtain rfl := (covBy_mkI_some_mkI_none β hy hx).1 h
      have hc : (SuspCarrier.pole β : globe.{u} 1) ⋖ SuspCarrier.susp PUnit.unit :=
        SuspCarrier.pole_covBy_susp.2 (isMin_point _)
      exact grayProduct_orient_of_covBy_fst (P := globe.{u} 1) hc y _
    · exact absurd h (not_covBy_mkI_none_mkI_some _ hy hx)
    · obtain ⟨rfl, hyx⟩ := (covBy_mkI_some_mkI_some _ _ hy hx).1 h
      rw [orient_mkI_some β hx h hyx]
      refine (grayProduct_orient_of_covBy_snd (P := globe.{u} 1)
        (SuspCarrier.pole β) hyx _).trans ?_
      rw [SuspCarrier.grade_pole]
      exact Bool.false_xor (U.orient hyx)

namespace PartialCylinder

variable {U V : OGP.{u}} {K : LowerSet U} {L : LowerSet V}

def carrierMapOfMap (ι : V → U) (hι : ∀ x, ι x ∈ K ↔ x ∈ L) :
    PartialCylinderCarrier V L → PartialCylinderCarrier U K
  | Sum.inl x => Sum.inl ⟨ι x.1, (hι x.1).2 x.2⟩
  | Sum.inr p => Sum.inr (p.1, ⟨ι p.2.1, fun h => p.2.2 ((hι p.2.1).1 h)⟩)

theorem proj_carrierMapOfMap (K : LowerSet U) (L : LowerSet V) (f : V → U)
    (hf : ∀ x, f x ∈ K ↔ x ∈ L) (a : partialCylinder V L) :
    partialCylinderProj U K (carrierMapOfMap f hf a) = f (partialCylinderProj V L a) := by
  rcases a with x | p <;> rfl

def carrierEquivOfEquiv (ψ : U ≃ V) (hψ : ∀ x, ψ x ∈ L ↔ x ∈ K) :
    PartialCylinderCarrier U K ≃ PartialCylinderCarrier V L where
  toFun := carrierMapOfMap ψ hψ
  invFun := carrierMapOfMap ψ.symm fun y => by rw [← hψ, Equiv.apply_symm_apply]
  left_inv := by
    rintro (x | ⟨i, x⟩)
    · exact congrArg Sum.inl (Subtype.ext (ψ.symm_apply_apply x.1))
    · exact congrArg Sum.inr (Prod.ext rfl (Subtype.ext (ψ.symm_apply_apply x.1)))
  right_inv := by
    rintro (x | ⟨i, x⟩)
    · exact congrArg Sum.inl (Subtype.ext (ψ.apply_symm_apply x.1))
    · exact congrArg Sum.inr (Prod.ext rfl (Subtype.ext (ψ.apply_symm_apply x.1)))

def initialSegOfInclusion (K : LowerSet U) (L : LowerSet V) (ι : V ⟶ U) [IsInclusion ι]
    (hι : ∀ x, ι x ∈ K ↔ x ∈ L) : partialCylinder V L ≤i partialCylinder U K where
  toRelEmbedding :=
    (OrderEmbedding.ofMapLEIff (carrierMapOfMap ι hι) fun a b => by
      change PartialCylinderCarrier.le (carrierMapOfMap ι hι a) (carrierMapOfMap ι hι b) ↔ a ≤ b
      rcases a with ⟨x, hx⟩ | ⟨⟨i⟩, ⟨x, hx⟩⟩ <;> rcases b with ⟨y, hy⟩ | ⟨⟨j⟩, ⟨y, hy⟩⟩
      · exact IsInclusion.le_iff ι
      · exact IsInclusion.le_iff ι
      · exact Iff.rfl
      · exact and_congr Iff.rfl (IsInclusion.le_iff ι)).ltEmbedding
  mem_range_of_rel' {a y} h := by
    have hy := h.le
    rcases a with ⟨x, hx⟩ | ⟨⟨i⟩, ⟨x, hx⟩⟩ <;> rcases y with ⟨y, hy'⟩ | ⟨⟨j⟩, ⟨y, hy'⟩⟩
    · obtain ⟨t, -, rfl⟩ := (isMorphism ι).fibration hy
      exact ⟨Sum.inl ⟨t, (hι t).1 hy'⟩, rfl⟩
    · exact (PartialCylinderCarrier.not_inr_le_inl hy).elim
    · obtain ⟨t, -, rfl⟩ := (isMorphism ι).fibration hy
      exact ⟨Sum.inl ⟨t, (hι t).1 hy'⟩, rfl⟩
    · obtain ⟨t, -, rfl⟩ := (isMorphism ι).fibration hy.2
      exact ⟨Sum.inr (⟨j⟩, ⟨t, fun h => hy' ((hι t).2 h)⟩), rfl⟩

def embOfEmb (K : LowerSet U) (L : LowerSet V) (ι : V ⟶ U) [IsInclusion ι]
    (hι : ∀ x, ι x ∈ K ↔ x ∈ L) : partialCylinder V L ⟶ partialCylinder U K :=
  ConcreteCategory.ofHom ⟨carrierMapOfMap ι hι,
    IsMorphism.of_initialSeg (initialSegOfInclusion K L ι hι) fun {a b} h => by
      rcases a with ⟨x, hx⟩ | ⟨⟨_ | β⟩, ⟨x, hx⟩⟩ <;>
        rcases b with ⟨y, hy⟩ | ⟨⟨_ | γ⟩, ⟨y, hy⟩⟩
      · exact (isMorphism ι).orient_apply ((covBy_mkK_mkK hy hx).1 h)
      · exact (not_covBy_mkI_mkK (K := L) none hy hx h).elim
      · exact (not_covBy_mkI_mkK (K := L) (some γ) hy hx h).elim
      · exact (not_covBy_mkK_mkI_none (K := L) hy hx h).elim
      · exact congrArg (!·) ((isMorphism ι).orient_apply ((covBy_mkI_none_mkI_none hy hx).1 h))
      · rfl
      · exact (isMorphism ι).orient_apply ((covBy_mkK_mkI_some hy β hx).1 h)
      · exact (not_covBy_mkI_none_mkI_some (K := L) β hy hx h).elim
      · exact (isMorphism ι).orient_apply ((covBy_mkI_some_mkI_some γ β hy hx).1 h).2⟩

instance isInclusion_embOfEmb (K : LowerSet U) (L : LowerSet V) (ι : V ⟶ U) [IsInclusion ι]
    (hι : ∀ x, ι x ∈ K ↔ x ∈ L) : IsInclusion (embOfEmb K L ι hι) :=
  ⟨(initialSegOfInclusion K L ι hι).injective⟩

@[simp] theorem embOfEmb_apply (K : LowerSet U) (L : LowerSet V) (ι : V ⟶ U) [IsInclusion ι]
    (hι : ∀ x, ι x ∈ K ↔ x ∈ L) (a : partialCylinder V L) :
    embOfEmb K L ι hι a = carrierMapOfMap ι hι a := rfl

def isoOfIso (K : LowerSet U) (L : LowerSet V) (ψ : U ≅ V)
    (hψ : ∀ x, ψ.hom x ∈ L ↔ x ∈ K) :
    partialCylinder U K ≅ partialCylinder V L where
  hom := embOfEmb L K ψ.hom hψ
  inv := embOfEmb K L ψ.inv fun y => by rw [← hψ, Iso.inv_hom_id_apply]
  hom_inv_id := by ext a; exact (carrierEquivOfEquiv (orderIsoOfIso ψ).toEquiv hψ).left_inv a
  inv_hom_id := by ext a; exact (carrierEquivOfEquiv (orderIsoOfIso ψ).toEquiv hψ).right_inv a

@[simp] theorem isoOfIso_hom_apply (K : LowerSet U) (L : LowerSet V) (ψ : U ≅ V)
    (hψ : ∀ x, ψ.hom x ∈ L ↔ x ∈ K) (a : partialCylinder U K) :
    (isoOfIso K L ψ hψ).hom a = carrierMapOfMap ψ.hom hψ a := rfl

@[simp] theorem isoOfIso_inv_apply (K : LowerSet U) (L : LowerSet V) (ψ : U ≅ V)
    (hψ : ∀ x, ψ.hom x ∈ L ↔ x ∈ K) (a : partialCylinder V L) :
    (isoOfIso K L ψ hψ).inv a =
      carrierMapOfMap ψ.inv (fun y => by rw [← hψ, Iso.inv_hom_id_apply]) a := rfl

theorem map_embOfEmb_top (K : LowerSet U) (L : LowerSet V) (ι : V ⟶ U) [IsInclusion ι]
    (hι : ∀ x, ι x ∈ K ↔ x ∈ L) :
    map (embOfEmb K L ι hι) ⊤ = over K (map ι ⊤) := by
  refine SetLike.ext fun a => ?_
  simp only [mem_map, LowerSet.mem_top, true_and, mem_over, embOfEmb_apply]
  constructor
  · rintro ⟨b, rfl⟩; exact ⟨_, (proj_carrierMapOfMap K L ι hι b).symm⟩
  · rintro ⟨x, hx⟩
    rcases a with ⟨y, hy⟩ | ⟨i, ⟨y, hy⟩⟩
    · obtain rfl : ι x = y := hx; exact ⟨Sum.inl ⟨x, (hι x).1 hy⟩, rfl⟩
    · obtain rfl : ι x = y := hx; exact ⟨Sum.inr (i, ⟨x, fun h => hy ((hι x).2 h)⟩), rfl⟩

variable (K : LowerSet U) (L : LowerSet V) in
theorem carrierMapOfMap_endpoint [DecidablePred (· ∈ K)] [DecidablePred (· ∈ L)]
    (f : V → U) (hf : ∀ x, f x ∈ K ↔ x ∈ L) (α : Bool) (x : V) :
    carrierMapOfMap f hf (partialCylinderEndpoint V L α x) =
      partialCylinderEndpoint U K α (f x) := by
  by_cases hx : x ∈ L
  · rw [endpoint_of_mem α hx, endpoint_of_mem α ((hf x).2 hx)]; rfl
  · rw [endpoint_of_notMem α hx, endpoint_of_notMem α (fun h => hx ((hf x).1 h))]; rfl

variable (K : LowerSet U) in
theorem endpoint_ne_mkI_none [DecidablePred (· ∈ K)] (α : Bool) (x y : U) (hy : y ∉ K) :
    partialCylinderEndpoint U K α x ≠ mkI K none y hy := by
  by_cases hx : x ∈ K
  · rw [endpoint_of_mem α hx]; exact mkK_ne_mkI hx hy
  · rw [endpoint_of_notMem α hx, Ne, mkI_eq_mkI_iff]; simp

variable (K : LowerSet U) (L : LowerSet V) in
theorem carrierMapOfMap_eq_endpoint_iff [DecidablePred (· ∈ K)] [DecidablePred (· ∈ L)]
    (f : V ⟶ U) (hf : ∀ x, f x ∈ K ↔ x ∈ L) (β : Bool)
    (a : partialCylinder V L) (y : U) :
    carrierMapOfMap f hf a = partialCylinderEndpoint U K β y ↔
      ∃ x, a = partialCylinderEndpoint V L β x ∧ f x = y := by
  constructor
  · intro h
    have hp : f (partialCylinderProj V L a) = y := by
      have h' := proj_carrierMapOfMap K L f hf a
      rw [h, partialCylinderProj_endpoint] at h'
      exact h'.symm
    subst y
    refine ⟨partialCylinderProj V L a, ?_, rfl⟩
    rcases a with ⟨x, hx⟩ | ⟨⟨i⟩, ⟨x, hx⟩⟩
    · exact (endpoint_of_mem β hx).symm
    · have hfx : f x ∉ K := fun h' => hx ((hf x).1 h')
      change mkI K i (f x) hfx = partialCylinderEndpoint U K β (f x) at h
      change mkI L i x hx = partialCylinderEndpoint V L β x
      rw [endpoint_of_notMem β hfx] at h
      rw [endpoint_of_notMem β hx, (mkI_eq_mkI_iff hfx hfx).1 h |>.1]
  · rintro ⟨x, rfl, rfl⟩
    exact carrierMapOfMap_endpoint K L _ hf β x

end PartialCylinder

end Atoms.Molecule.OGP
