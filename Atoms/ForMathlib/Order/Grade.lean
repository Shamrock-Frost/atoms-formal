import Mathlib.Data.Fintype.Lattice
import Mathlib.Order.Atoms
import Mathlib.Order.Grade
import Mathlib.Order.SuccPred.InitialSeg
import Mathlib.Order.KrullDimension
import Mathlib.Order.UpperLower.CompleteLattice
import Mathlib.Order.UpperLower.Principal

namespace GradeOrder

variable {α : Type*} [Preorder α] [GradeOrder ℕ α]

instance isStronglyAtomic : IsStronglyAtomic α where
  exists_covBy_le_of_lt a b hab := by
    obtain ⟨c, ⟨hac, hcb⟩, hmin⟩ := (InvImage.wf (grade ℕ) wellFounded_lt).has_min
      {c | a < c ∧ c ≤ b} ⟨b, hab, le_rfl⟩
    exact ⟨c, ⟨hac, fun d had hdc => hmin d ⟨had, hdc.le.trans hcb⟩ (grade_strictMono hdc)⟩, hcb⟩

instance isStronglyCoatomic : IsStronglyCoatomic α where
  exists_le_covBy_of_lt a b hab := by
    obtain ⟨c, ⟨hac, hcb⟩, hmin⟩ :=
      (InvImage.wf (fun c => grade ℕ b - grade ℕ c) wellFounded_lt).has_min
        {c | a ≤ c ∧ c < b} ⟨a, le_rfl, hab⟩
    refine ⟨c, hac, hcb, fun d hcd hdb => hmin d ⟨hac.trans hcd.le, hdb⟩ ?_⟩
    exact Nat.sub_lt_sub_left (grade_strictMono (hcd.trans hdb)) (grade_strictMono hcd)

theorem exists_le_maximal {s : Set α} {n : ℕ} (hs : ∀ y ∈ s, grade ℕ y ≤ n) {x : α} (hx : x ∈ s) :
    ∃ z, x ≤ z ∧ Maximal (· ∈ s) z := by
  obtain ⟨z, ⟨hzs, hxz⟩, hmin⟩ := (InvImage.wf (fun z => n - grade ℕ z) wellFounded_lt).has_min
    {z | z ∈ s ∧ x ≤ z} ⟨x, hx, le_rfl⟩
  refine ⟨z, hxz, hzs, fun w hws hzw => ?_⟩
  by_contra hwz
  exact hmin w ⟨hws, hxz.trans hzw⟩ (Nat.sub_lt_sub_left
    ((grade_strictMono (lt_of_le_not_ge hzw hwz)).trans_le (hs w hws))
    (grade_strictMono (lt_of_le_not_ge hzw hwz)))

theorem eq_of_le_of_grade_le {β : Type*} [PartialOrder β] [GradeOrder ℕ β] {a b : β} (hab : a ≤ b)
    (h : grade ℕ b ≤ grade ℕ a) : a = b :=
  hab.eq_of_not_lt fun hlt => (grade_strictMono hlt).not_ge h

theorem covBy_of_le_of_grade_eq_add_one {β : Type*} [PartialOrder β] [GradeOrder ℕ β] {a b : β}
    (hab : a ≤ b) (h : grade ℕ b = grade ℕ a + 1) : a ⋖ b :=
  covBy_iff_lt_covBy_grade.2
    ⟨hab.lt_of_ne (by rintro rfl; omega), Nat.covBy_iff_add_one_eq.2 h.symm⟩

theorem covBy_and_covBy_of_mem_Ioo {β : Type*} [PartialOrder β] [GradeOrder ℕ β] {x y z : β}
    (hd : grade ℕ x = grade ℕ y + 2) (hz : z ∈ Set.Ioo y x) : y ⋖ z ∧ z ⋖ x := by
  have h₁ := _root_.grade_strictMono (𝕆 := ℕ) hz.1
  have h₂ := _root_.grade_strictMono (𝕆 := ℕ) hz.2
  exact ⟨covBy_of_le_of_grade_eq_add_one hz.1.le (by omega),
    covBy_of_le_of_grade_eq_add_one hz.2.le (by omega)⟩

end GradeOrder

theorem grade_eq_zero_iff {α : Type*} [Preorder α] [GradeMinOrder ℕ α] {a : α} :
    grade ℕ a = 0 ↔ IsMin a := by
  rw [← isMin_grade_iff (𝕆 := ℕ), isMin_iff_eq_bot, Nat.bot_eq_zero]

section InitialSeg

variable {α β γ : Type*} [PartialOrder α] [PartialOrder β] [PartialOrder γ] [GradeMinOrder ℕ α]
  [GradeMinOrder ℕ β] (g : γ → ℕ)

private theorem lt_of_initialSeg (e : α ≤i γ) (hg : ∀ a, g (e a) = grade ℕ a) {c c' : γ}
    (h : c < c') (hc' : c' ∈ Set.range e) : g c < g c' := by
  obtain ⟨a', rfl⟩ := hc'
  obtain ⟨a, rfl⟩ := e.mem_range_of_rel h
  rw [hg, hg]
  exact grade_strictMono (e.lt_iff_lt.1 h)

private theorem covBy_of_initialSeg (e : α ≤i γ) (hg : ∀ a, g (e a) = grade ℕ a) {c c' : γ}
    (h : c ⋖ c') (hc' : c' ∈ Set.range e) : g c ⋖ g c' := by
  obtain ⟨a', rfl⟩ := hc'
  obtain ⟨a, rfl⟩ := e.mem_range_of_rel h.lt
  rw [hg, hg]
  exact (e.apply_covBy_apply_iff.1 h).grade ℕ

private theorem isMin_of_initialSeg (e : α ≤i γ) (hg : ∀ a, g (e a) = grade ℕ a) {c : γ}
    (h : IsMin c) (hc : c ∈ Set.range e) : IsMin (g c) := by
  obtain ⟨a, rfl⟩ := hc
  rw [hg]
  exact (e.isMin_apply_iff.1 h).grade ℕ

abbrev GradeMinOrder.ofInitialSeg (e : α ≤i γ) (e' : β ≤i γ) (hg : ∀ a, g (e a) = grade ℕ a)
    (hg' : ∀ b, g (e' b) = grade ℕ b) (hcover : ∀ c, c ∈ Set.range e ∨ c ∈ Set.range e') :
    GradeMinOrder ℕ γ where
  grade := g
  grade_strictMono _ c' h :=
    (hcover c').elim (lt_of_initialSeg g e hg h) (lt_of_initialSeg g e' hg' h)
  covBy_grade _ c' h :=
    (hcover c').elim (covBy_of_initialSeg g e hg h) (covBy_of_initialSeg g e' hg' h)
  isMin_grade c h := (hcover c).elim (isMin_of_initialSeg g e hg h) (isMin_of_initialSeg g e' hg' h)

def _root_.WithTop.coeInitialSeg (α : Type*) [PartialOrder α] : α ≤i WithTop α where
  toRelEmbedding := (OrderEmbedding.ofMapLEIff ((↑) : α → WithTop α) fun _ _ =>
    WithTop.coe_le_coe).ltEmbedding
  mem_range_of_rel' _ _ h := WithTop.ne_top_iff_exists.1 h.ne_top

@[simp] theorem _root_.WithTop.coeInitialSeg_apply {α : Type*} [PartialOrder α] (a : α) :
    WithTop.coeInitialSeg α a = a :=
  rfl

end InitialSeg

instance PUnit.gradeMinOrder {𝕆 : Type*} [Preorder 𝕆] [OrderBot 𝕆] : GradeMinOrder 𝕆 PUnit where
  grade _ := ⊥
  grade_strictMono a b h := (h.ne (Subsingleton.elim a b)).elim
  covBy_grade a b h := (h.lt.ne (Subsingleton.elim a b)).elim
  isMin_grade _ _ := isMin_bot

instance PEmpty.gradeMinOrder {𝕆 : Type*} [Preorder 𝕆] : GradeMinOrder 𝕆 PEmpty where
  grade := PEmpty.elim
  grade_strictMono a := a.elim
  covBy_grade a := a.elim
  isMin_grade a := a.elim

namespace Prod

variable {α β : Type*} [PartialOrder α] [PartialOrder β] [GradeMinOrder ℕ α] [GradeMinOrder ℕ β]

instance gradeMinOrder : GradeMinOrder ℕ (α × β) where
  grade a := grade ℕ a.1 + grade ℕ a.2
  grade_strictMono a b h := by
    rcases Prod.lt_iff.1 h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Nat.add_lt_add_of_lt_of_le (grade_strictMono h₁) (grade_mono h₂)
    · exact Nat.add_lt_add_of_le_of_lt (grade_mono h₁) (grade_strictMono h₂)
  covBy_grade a b h := by
    rw [Nat.covBy_iff_add_one_eq]
    rcases Prod.covBy_iff.1 h with ⟨h₁, h₂⟩ | ⟨h₂, h₁⟩
    · rw [h₂, ← Nat.covBy_iff_add_one_eq.1 (h₁.grade ℕ)]
      omega
    · rw [h₁, ← Nat.covBy_iff_add_one_eq.1 (h₂.grade ℕ)]
      omega
  isMin_grade a h := by
    rw [Prod.isMin_iff] at h
    rw [grade_eq_zero_iff.2 h.1, grade_eq_zero_iff.2 h.2]
    exact isMin_bot

@[simp] theorem grade_eq_add (a : α × β) : grade ℕ a = grade ℕ a.1 + grade ℕ a.2 :=
  rfl

omit [GradeMinOrder ℕ β] in
theorem snd_covBy_snd_of_grade_eq {a b : α × β} (h : a ⋖ b) (hg : grade ℕ a.1 = grade ℕ b.1) :
    a.2 ⋖ b.2 :=
  ((Prod.covBy_iff.1 h).resolve_left fun h₁ => (grade_strictMono h₁.1.lt).ne hg).1

omit [GradeMinOrder ℕ β] in
theorem fst_covBy_fst_of_grade_ne {a b : α × β} (h : a ⋖ b) (hg : grade ℕ a.1 ≠ grade ℕ b.1) :
    a.1 ⋖ b.1 :=
  ((Prod.covBy_iff.1 h).resolve_right fun h₂ => hg (by rw [h₂.2])).1

end Prod

namespace WithBot

variable {α : Type*} [Preorder α] [GradeMinOrder ℕ α]

instance gradeMinOrder : GradeMinOrder ℕ (WithBot α) where
  grade := WithBot.recBotCoe 0 fun a => grade ℕ a + 1
  grade_strictMono a b h := by
    induction b using WithBot.recBotCoe with
    | bot => exact absurd h not_lt_bot
    | coe b =>
      induction a using WithBot.recBotCoe with
      | bot => exact Nat.succ_pos _
      | coe a => exact Nat.succ_lt_succ (grade_strictMono (coe_lt_coe.1 h))
  covBy_grade a b h := by
    induction b using WithBot.recBotCoe with
    | bot => exact absurd h.lt not_lt_bot
    | coe b =>
      induction a using WithBot.recBotCoe with
      | bot =>
        change 0 ⋖ grade ℕ b + 1
        rw [grade_eq_zero_iff.2 (bot_covBy_coe.1 h)]
        exact Nat.covBy_iff_add_one_eq.2 rfl
      | coe a =>
        change grade ℕ a + 1 ⋖ grade ℕ b + 1
        rw [Nat.covBy_iff_add_one_eq, ← Nat.covBy_iff_add_one_eq.1 ((coe_covBy_coe.1 h).grade ℕ)]
  isMin_grade a h := by
    induction a using WithBot.recBotCoe with
    | bot => exact isMin_bot
    | coe a => exact absurd (h bot_le) (not_coe_le_bot a)

@[simp] theorem grade_coe (a : α) : grade ℕ (a : WithBot α) = grade ℕ a + 1 :=
  rfl

end WithBot

section NeBot

variable {α : Type*} [PartialOrder α] [OrderBot α]

@[simp, norm_cast] theorem Subtype.coe_covBy_coe_ne_bot {a b : {x : α // x ≠ ⊥}} :
    (a : α) ⋖ b ↔ a ⋖ b := by
  have h : (Set.range (OrderEmbedding.subtype fun x : α => x ≠ ⊥)).OrdConnected := by
    rw [OrderEmbedding.coe_subtype, Subtype.range_coe_subtype]
    exact IsUpperSet.ordConnected fun _ _ hle h => ne_bot_of_le_ne_bot h hle
  exact Set.OrdConnected.apply_covBy_apply_iff (OrderEmbedding.subtype fun x : α => x ≠ ⊥) h

variable [GradeMinOrder ℕ α]

private theorem grade_pos_of_ne_bot {a : α} (h : a ≠ ⊥) : 0 < grade ℕ a := by
  simpa using grade_strictMono (𝕆 := ℕ) (bot_lt_iff_ne_bot.2 h)

instance Subtype.gradeMinOrderNeBot : GradeMinOrder ℕ {x : α // x ≠ ⊥} where
  grade a := grade ℕ (a : α) - 1
  grade_strictMono a b h := by
    have := grade_pos_of_ne_bot a.2
    have := grade_strictMono (𝕆 := ℕ) (Subtype.coe_lt_coe.2 h)
    dsimp only
    omega
  covBy_grade a b h := by
    have := grade_pos_of_ne_bot a.2
    have := Nat.covBy_iff_add_one_eq.1 ((Subtype.coe_covBy_coe_ne_bot.2 h).grade ℕ)
    rw [Nat.covBy_iff_add_one_eq]
    omega
  isMin_grade a h := by
    have hcov : ⊥ ⋖ (a : α) := ⟨bot_lt_iff_ne_bot.2 a.2, fun c hc hca =>
      h.not_lt (b := ⟨c, (bot_lt_iff_ne_bot.1 hc)⟩) hca⟩
    have := Nat.covBy_iff_add_one_eq.1 (hcov.grade ℕ)
    rw [grade_bot, Nat.bot_eq_zero] at this
    change IsMin (grade ℕ (a : α) - 1)
    rw [← this]
    exact isMin_bot

@[simp] theorem Subtype.grade_ne_bot (a : {x : α // x ≠ ⊥}) : grade ℕ a = grade ℕ (a : α) - 1 :=
  rfl

end NeBot

namespace Order

variable {α : Type*} [PartialOrder α] [GradeMinOrder ℕ α]

theorem height_eq_grade (a : α) : height a = grade ℕ a := by
  have := GradeOrder.wellFoundedLT (α := α) ℕ
  induction a using WellFoundedLT.induction with
  | _ a ih =>
    rw [height_eq_iSup_lt_height]
    refine le_antisymm (iSup₂_le fun b hb => ?_) ?_
    · rw [ih b hb]
      exact_mod_cast Nat.succ_le_of_lt (grade_strictMono hb)
    · by_cases hmin : IsMin a
      · simp [isMin_iff_eq_bot.1 (hmin.grade ℕ)]
      · obtain ⟨c, hc⟩ := not_isMin_iff.1 hmin
        obtain ⟨b, -, hb⟩ := exists_le_covBy_of_lt hc
        refine le_iSup₂_of_le b hb.lt ?_
        rw [ih b hb.lt, ← Nat.covBy_iff_add_one_eq.1 (hb.grade ℕ)]
        push_cast
        rfl

theorem exists_lt_grade_eq {a : α} {n : ℕ} (h : n < grade ℕ a) : ∃ b < a, grade ℕ b = n := by
  obtain ⟨b, hb, hbn⟩ := (coe_lt_height_iff (x := a) (by simp [height_eq_grade])).1
    (by simpa [height_eq_grade] using h)
  exact ⟨b, hb, by simpa [height_eq_grade] using hbn⟩

theorem krullDim_eq_iSup_grade : krullDim α = ⨆ a : α, ((grade ℕ a : ℕ∞) : WithBot ℕ∞) := by
  simp [krullDim_eq_iSup_height, height_eq_grade]

theorem krullDim_eq_map_sup_grade [Fintype α] :
    krullDim α = (Finset.univ.sup fun a : α => (grade ℕ a : WithBot ℕ)).map ((↑) : ℕ → ℕ∞) := by
  rw [krullDim_eq_iSup_grade, ← Finset.sup_univ_eq_iSup,
    Finset.apply_sup_eq_sup_comp (WithBot.map ((↑) : ℕ → ℕ∞))
      (WithBot.monotone_map_iff.2 Nat.mono_cast).map_sup rfl]
  rfl

theorem krullDim_le_coe_iff {n : ℕ} : krullDim α ≤ n ↔ ∀ a : α, grade ℕ a ≤ n := by
  rw [krullDim_eq_iSup_grade, iSup_le_iff]
  exact forall_congr' fun a => by exact_mod_cast Iff.rfl

theorem grade_le_krullDim (a : α) : (grade ℕ a : WithBot ℕ∞) ≤ krullDim α := by
  simpa [height_eq_grade] using height_le_krullDim a

theorem coe_lt_krullDim_iff {n : ℕ} : (n : WithBot ℕ∞) < krullDim α ↔ ∃ a : α, n < grade ℕ a := by
  simpa using (krullDim_le_coe_iff (α := α) (n := n)).not

theorem exists_grade_eq_of_krullDim_eq {n : ℕ} (h : krullDim α = n) : ∃ a : α, grade ℕ a = n := by
  have hle := krullDim_le_coe_iff.1 h.le
  cases n with
  | zero =>
    obtain ⟨a⟩ := krullDim_nonneg_iff.1 h.ge
    exact ⟨a, Nat.le_zero.1 (hle a)⟩
  | succ m =>
    obtain ⟨a, ha⟩ := coe_lt_krullDim_iff (n := m).1 (by rw [h]; exact_mod_cast m.lt_succ_self)
    exact ⟨a, le_antisymm (hle a) ha⟩

variable [Fintype α]

instance decidableKrullDimEqCoe (n : ℕ) : Decidable (krullDim α = n) :=
  decidable_of_iff ((Finset.univ.sup fun a : α => (grade ℕ a : WithBot ℕ)) = WithBot.some n) (by
    rw [krullDim_eq_map_sup_grade]
    cases Finset.univ.sup fun a : α => (grade ℕ a : WithBot ℕ) <;> simp)

instance decidableCoeLTKrullDim (n : ℕ) : Decidable ((n : WithBot ℕ∞) < krullDim α) :=
  decidable_of_iff (∃ a : α, n < grade ℕ a) coe_lt_krullDim_iff.symm

instance decidableZeroLTKrullDim : Decidable (0 < krullDim α) :=
  decidable_of_iff (((0 : ℕ) : WithBot ℕ∞) < krullDim α) (by rw [Nat.cast_zero])

instance decidableKrullDimLECoe (n : ℕ) : Decidable (krullDim α ≤ n) :=
  decidable_of_iff (∀ a : α, grade ℕ a ≤ n) krullDim_le_coe_iff.symm

instance decidableKrullDimEq {β : Type*} [PartialOrder β] [GradeMinOrder ℕ β] [Fintype β] :
    Decidable (krullDim α = krullDim β) :=
  decidable_of_iff ((Finset.univ.sup fun a : α => (grade ℕ a : WithBot ℕ)) =
      Finset.univ.sup fun b : β => (grade ℕ b : WithBot ℕ)) (by
    rw [krullDim_eq_map_sup_grade, krullDim_eq_map_sup_grade]
    exact (WithBot.map_injective Nat.cast_injective).eq_iff.symm)

end Order

namespace LowerSet

variable {𝕆 α : Type*} [Preorder 𝕆] [Preorder α]

@[simp] theorem coe_covBy_coe (U : LowerSet α) {a b : U} : (a : α) ⋖ b ↔ a ⋖ b :=
  Set.OrdConnected.apply_covBy_apply_iff (OrderEmbedding.subtype (· ∈ U))
    (by simpa using U.lower.ordConnected)

instance instGradeOrder [GradeOrder 𝕆 α] (U : LowerSet α) : GradeOrder 𝕆 ↥U :=
  GradeOrder.liftRight Subtype.val (Subtype.strictMono_coe _) fun _ _ h => (coe_covBy_coe U).2 h

instance instGradeMinOrder [GradeMinOrder 𝕆 α] (U : LowerSet α) : GradeMinOrder 𝕆 ↥U where
  isMin_grade a ha :=
    IsMin.grade 𝕆 (fun c hc => ha (b := ⟨c, U.lower hc a.2⟩) hc : IsMin (a : α))

@[simp] theorem grade_coe [GradeOrder 𝕆 α] (U : LowerSet α) (x : ↥U) :
    grade 𝕆 (x : α) = grade 𝕆 x :=
  rfl

@[simp] theorem krullDim_top : Order.krullDim ↥(⊤ : LowerSet α) = Order.krullDim α :=
  Order.krullDim_eq_of_orderIso OrderIso.Set.univ

theorem krullDim_mono : Monotone fun s : LowerSet α => Order.krullDim s :=
  fun _ _ h => Order.krullDim_le_of_strictMono (Set.inclusion h) fun _ _ => id

end LowerSet

namespace LowerSet

variable {α : Type*} [PartialOrder α] [GradeMinOrder ℕ α]

theorem krullDim_Iic (a : α) : Order.krullDim (Iic a) = grade ℕ a := by
  have h := Order.height_eq_krullDim_Iic a
  rw [Order.height_eq_grade] at h
  exact h.symm

theorem krullDim_Iic_of_isMin {a : α} (ha : IsMin a) : Order.krullDim (Iic a) = 0 := by
  rw [krullDim_Iic, isMin_iff_eq_bot.1 (ha.grade ℕ)]
  rfl

theorem krullDim_sup (s t : LowerSet α) :
    Order.krullDim ↥(s ⊔ t) = Order.krullDim s ⊔ Order.krullDim t := by
  simp only [Order.krullDim_eq_iSup_grade, ← grade_coe]
  have h (u : LowerSet α) := iSup_subtype'' (u : Set α) fun a => ((grade ℕ a : ℕ∞) : WithBot ℕ∞)
  simp only [SetLike.coe_sort_coe] at h
  rw [h, h, h, coe_sup, iSup_union]

end LowerSet

namespace Relation.Fibration

variable {α β : Type*} [PartialOrder α] [GradeMinOrder ℕ α] [PartialOrder β] [GradeMinOrder ℕ β]
  {f : α → β}

theorem grade_apply_le (hf : Relation.Fibration (· ≤ ·) (· ≤ ·) f) (x : α) :
    grade ℕ (f x) ≤ grade ℕ x := by
  have := GradeOrder.wellFoundedLT (α := α) ℕ
  induction x using WellFoundedLT.induction with
  | _ x ih =>
    by_cases hmin : IsMin (f x)
    · rw [isMin_iff_eq_bot.1 (hmin.grade ℕ)]
      exact bot_le
    obtain ⟨w, hw⟩ := not_isMin_iff.1 hmin
    obtain ⟨w', -, hw'⟩ := exists_le_covBy_of_lt hw
    obtain ⟨z, hzx, hzw⟩ := hf hw'.le
    have hzx' : z < x := hzx.lt_of_ne fun h => hw'.ne (by rw [← hzw, h])
    have h₁ := Nat.covBy_iff_add_one_eq.1 (hw'.grade ℕ)
    have h₂ := ih z hzx'
    have h₃ := grade_strictMono (𝕆 := ℕ) hzx'
    rw [hzw] at h₂
    omega

theorem grade_apply_lt_of_lt (hf : Relation.Fibration (· ≤ ·) (· ≤ ·) f) {x y : α} (hxy : x < y)
    (h : f x = f y) : grade ℕ (f y) < grade ℕ y := by
  rw [← h]
  exact (hf.grade_apply_le x).trans_lt (grade_strictMono hxy)

end Relation.Fibration
