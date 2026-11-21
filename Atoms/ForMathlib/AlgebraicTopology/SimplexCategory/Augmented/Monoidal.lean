import Mathlib.AlgebraicTopology.SimplexCategory.Augmented.Monoidal

open CategoryTheory MonoidalCategory Simplicial

namespace AugmentedSimplexCategory

def card : AugmentedSimplexCategory → ℕ
  | .star => 0
  | .of m => m.len + 1

def ofCard : ℕ → AugmentedSimplexCategory
  | 0 => .star
  | k + 1 => .of (.mk k)

theorem card_ofCard (k : ℕ) : card (ofCard k) = k := by
  cases k <;> rfl

theorem exists_card_eq (k : ℕ) : ∃ d : AugmentedSimplexCategory, card d = k :=
  ⟨ofCard k, card_ofCard k⟩

theorem card_injective {x y : AugmentedSimplexCategory} (h : card x = card y) : x = y := by
  cases x <;> cases y
  · exact congrArg WithInitial.of (SimplexCategory.ext (Nat.succ.inj h))
  · exact absurd h (Nat.succ_ne_zero _)
  · exact absurd h.symm (Nat.succ_ne_zero _)
  · rfl

theorem card_tensorObj (x y : AugmentedSimplexCategory) :
    card (x ⊗ y) = card x + card y := by
  cases x <;> cases y
  · change _ + 1 + 1 = _ + 1 + (_ + 1)
    omega
  · rfl
  · exact (Nat.zero_add _).symm
  · rfl

def toFun : ∀ {x y : AugmentedSimplexCategory}, (x ⟶ y) → Fin (card x) → Fin (card y)
  | .of _, .of _, f => (WithInitial.down f).toOrderHom
  | .star, _, _ => fun i ↦ i.elim0
  | .of _, .star, f => (WithInitial.false_of_to_star f).elim

theorem toFun_comp_apply {x y z : AugmentedSimplexCategory} (f : x ⟶ y) (g : y ⟶ z)
    (i : Fin (card x)) : toFun (f ≫ g) i = toFun g (toFun f i) := by
  cases x with
  | star => exact i.elim0
  | of x =>
    cases y with
    | star => exact (WithInitial.false_of_to_star f).elim
    | of y =>
      cases z with
      | star => exact (WithInitial.false_of_to_star g).elim
      | of z => rfl

theorem toFun_id (x : AugmentedSimplexCategory) (i : Fin (card x)) : toFun (𝟙 x) i = i := by
  cases x with
  | star => exact i.elim0
  | of x => rfl

theorem monotone_toFun {x y : AugmentedSimplexCategory} (f : x ⟶ y) :
    Monotone (toFun f) := by
  cases x with
  | star => exact fun i ↦ i.elim0
  | of x =>
    cases y with
    | star => exact (WithInitial.false_of_to_star f).elim
    | of y => exact (WithInitial.down f).toOrderHom.monotone

theorem toFun_injective {x y : AugmentedSimplexCategory} {f g : x ⟶ y}
    (h : toFun f = toFun g) : f = g := by
  cases x with
  | star => exact Subsingleton.elim _ _
  | of x =>
    cases y with
    | star => exact (WithInitial.false_of_to_star f).elim
    | of y => exact SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _ h)

theorem exists_toFun_eq {x y : AugmentedSimplexCategory} (h : Fin (card x) → Fin (card y))
    (hh : Monotone h) : ∃ f : x ⟶ y, toFun f = h := by
  cases x with
  | star => exact ⟨WithInitial.starInitial.to _, funext fun i ↦ i.elim0⟩
  | of x =>
    cases y with
    | star => exact (h ⟨0, Nat.succ_pos _⟩).elim0
    | of y => exact ⟨inclusion.map (SimplexCategory.Hom.mk ⟨h, hh⟩), rfl⟩

def toOrderHom {x y : AugmentedSimplexCategory} (f : x ⟶ y) : Fin (card x) →o Fin (card y) :=
  ⟨toFun f, monotone_toFun f⟩

@[simp] theorem toOrderHom_id (x : AugmentedSimplexCategory) : toOrderHom (𝟙 x) = OrderHom.id :=
  OrderHom.ext _ _ (funext (toFun_id x))

@[simp] theorem toOrderHom_comp {x y z : AugmentedSimplexCategory} (f : x ⟶ y) (g : y ⟶ z) :
    toOrderHom (f ≫ g) = (toOrderHom g).comp (toOrderHom f) :=
  OrderHom.ext _ _ (funext (toFun_comp_apply f g))

theorem val_toFun_eqToHom {x y : AugmentedSimplexCategory} (h : x = y) (i : Fin (card x)) :
    (toFun (eqToHom h) i).val = i.val := by
  subst h
  cases x with
  | star => exact i.elim0
  | of x => rfl

theorem val_toFun_inl (x y : AugmentedSimplexCategory) (i : Fin (card x)) :
    (toFun (inl x y) i).val = i.val := by
  cases x with
  | star => exact i.elim0
  | of x =>
    cases y with
    | star =>
      rfl
    | of y => exact congrArg Fin.val (inl'_eval x y i)

theorem val_toFun_inr (x y : AugmentedSimplexCategory) (i : Fin (card y)) :
    (toFun (inr x y) i).val = card x + i.val := by
  cases y with
  | star => exact i.elim0
  | of y =>
    cases x with
    | star =>
      exact (Nat.zero_add _).symm
    | of x => exact congrArg Fin.val (inr'_eval x y i)

theorem val_toFun_tensorHom_of_lt {x₁ y₁ x₂ y₂ : AugmentedSimplexCategory} (f : x₁ ⟶ y₁)
    (g : x₂ ⟶ y₂) (i : Fin (card (x₁ ⊗ x₂))) (hi : i.val < card x₁) :
    (toFun (f ⊗ₘ g) i).val = (toFun f ⟨i.val, hi⟩).val := by
  have hi' : toFun (inl x₁ x₂) ⟨i.val, hi⟩ = i := Fin.ext (val_toFun_inl x₁ x₂ ⟨i.val, hi⟩)
  rw [← val_toFun_inl y₁ y₂ (toFun f ⟨i.val, hi⟩), ← toFun_comp_apply, ← inl_comp_tensorHom,
    toFun_comp_apply, hi']

theorem val_toFun_tensorHom_of_le {x₁ y₁ x₂ y₂ : AugmentedSimplexCategory} (f : x₁ ⟶ y₁)
    (g : x₂ ⟶ y₂) (i : Fin (card (x₁ ⊗ x₂))) (hi : card x₁ ≤ i.val) :
    (toFun (f ⊗ₘ g) i).val = card y₁ +
      (toFun g ⟨i.val - card x₁, by have := card_tensorObj x₁ x₂; omega⟩).val := by
  have hi' : i = toFun (inr x₁ x₂) ⟨i.val - card x₁, by have := card_tensorObj x₁ x₂; omega⟩ :=
    Fin.ext (by
      simp only [val_toFun_inr]
      omega)
  conv_lhs => rw [hi', ← toFun_comp_apply, inr_comp_tensorHom, toFun_comp_apply, val_toFun_inr]

private lemma val_toFun_tensorHom_lt_of_lt {x₁ y₁ x₂ y₂ : AugmentedSimplexCategory}
    (f : x₁ ⟶ y₁) (g : x₂ ⟶ y₂) (i : Fin (card (x₁ ⊗ x₂))) (hi : i.val < card x₁) :
    (toFun (f ⊗ₘ g) i).val < card y₁ := by
  rw [val_toFun_tensorHom_of_lt f g i hi]
  exact Fin.isLt _

private lemma card_le_of_eqToHom_comp_tensorHom_eq {n x y a b a' b' : AugmentedSimplexCategory}
    (h : a ⊗ b = n) (h' : a' ⊗ b' = n) (f : a ⟶ x) (g : b ⟶ y) (f' : a' ⟶ x) (g' : b' ⟶ y)
    (he : eqToHom h.symm ≫ (f ⊗ₘ g) = eqToHom h'.symm ≫ (f' ⊗ₘ g')) : card a ≤ card a' := by
  by_contra hlt
  have hn := card_tensorObj a' b'
  rw [h'] at hn
  have hn' := card_tensorObj a b
  rw [h] at hn'
  let i : Fin (card n) := ⟨card a', by omega⟩
  have hi : i.val = card a' := rfl
  have he' := congrArg Fin.val (congrFun (congrArg toFun he) i)
  rw [toFun_comp_apply, toFun_comp_apply] at he'
  have h₁ := val_toFun_tensorHom_lt_of_lt f g (toFun (eqToHom h.symm) i)
    (by rw [val_toFun_eqToHom]; omega)
  have h₂ := val_toFun_tensorHom_of_le f' g' (toFun (eqToHom h'.symm) i)
    (by rw [val_toFun_eqToHom, hi])
  omega

private lemma injective_eqToHom_comp_tensorHom (n x y : AugmentedSimplexCategory) :
    Function.Injective (fun p : Σ s : {s : AugmentedSimplexCategory × AugmentedSimplexCategory //
        s.1 ⊗ s.2 = n}, (s.1.1 ⟶ x) × (s.1.2 ⟶ y) ↦ eqToHom p.1.2.symm ≫ (p.2.1 ⊗ₘ p.2.2)) := by
  rintro ⟨⟨⟨a, b⟩, h⟩, f, g⟩ ⟨⟨⟨a', b'⟩, h'⟩, f', g'⟩ he
  dsimp only at h h' he
  have ha : card a = card a' := le_antisymm
    (card_le_of_eqToHom_comp_tensorHom_eq h h' f g f' g' he)
    (card_le_of_eqToHom_comp_tensorHom_eq h' h f' g' f g he.symm)
  obtain rfl := card_injective ha
  obtain rfl : b = b' := card_injective (by
    have h₁ := card_tensorObj a b
    have h₂ := card_tensorObj a b'
    rw [h] at h₁
    rw [h'] at h₂
    omega)
  have he' : f ⊗ₘ g = f' ⊗ₘ g' := (cancel_epi _).1 he
  obtain rfl : f = f' := toFun_injective (funext fun j ↦ Fin.ext (by
    have hj : j.val < card (a ⊗ b) := by
      rw [card_tensorObj]
      exact Nat.lt_of_lt_of_le j.isLt (Nat.le_add_right _ _)
    have := congrArg Fin.val (congrFun (congrArg toFun he') ⟨j.val, hj⟩)
    rwa [val_toFun_tensorHom_of_lt _ _ _ j.isLt, val_toFun_tensorHom_of_lt _ _ _ j.isLt] at this))
  obtain rfl : g = g' := toFun_injective (funext fun j ↦ Fin.ext (by
    have hj : card a + j.val < card (a ⊗ b) := by
      rw [card_tensorObj]
      exact Nat.add_lt_add_left j.isLt _
    have := congrArg Fin.val (congrFun (congrArg toFun he') ⟨card a + j.val, hj⟩)
    rw [val_toFun_tensorHom_of_le _ _ _ (Nat.le_add_right _ _),
      val_toFun_tensorHom_of_le _ _ _ (Nat.le_add_right _ _)] at this
    simpa only [Nat.add_sub_cancel_left, Nat.add_left_cancel_iff] using this))
  rfl

private lemma surjective_eqToHom_comp_tensorHom (n x y : AugmentedSimplexCategory) :
    Function.Surjective (fun p : Σ s : {s : AugmentedSimplexCategory × AugmentedSimplexCategory //
        s.1 ⊗ s.2 = n}, (s.1.1 ⟶ x) × (s.1.2 ⟶ y) ↦ eqToHom p.1.2.symm ≫ (p.2.1 ⊗ₘ p.2.2)) := by
  intro φ
  have hxy := card_tensorObj x y
  let P : ℕ → Prop := fun k ↦ card n ≤ k ∨ ∃ hk : k < card n, card x ≤ (toFun φ ⟨k, hk⟩).val
  have hP : ∃ k, P k := ⟨card n, Or.inl le_rfl⟩
  classical
  let k := Nat.find hP
  have hkn : k ≤ card n := Nat.find_min' hP (Or.inl le_rfl)
  have hlt : ∀ i : Fin (card n), i.val < k → (toFun φ i).val < card x := fun i hi ↦ by
    have := Nat.find_min hP hi
    simp only [P, not_or, not_exists, not_le] at this
    exact this.2 i.isLt
  have hge : ∀ i : Fin (card n), k ≤ i.val → card x ≤ (toFun φ i).val := fun i hi ↦ by
    rcases Nat.find_spec hP with h | ⟨hk, h⟩
    · exact absurd i.isLt (by omega)
    · exact h.trans (monotone_toFun φ (Fin.mk_le_mk.2 hi))
  have hab : ofCard k ⊗ ofCard (card n - k) = n :=
    card_injective (by rw [card_tensorObj, card_ofCard, card_ofCard]; omega)
  obtain ⟨f, hf⟩ := exists_toFun_eq (x := ofCard k) (y := x)
    (fun i ↦ ⟨(toFun φ ⟨i.val, by have := i.isLt.trans_eq (card_ofCard k); omega⟩).val,
      hlt _ (i.isLt.trans_eq (card_ofCard k))⟩)
    (fun i j hij ↦ Fin.mk_le_mk.2 (monotone_toFun φ (Fin.mk_le_mk.2 hij)))
  obtain ⟨g, hg⟩ := exists_toFun_eq (x := ofCard (card n - k)) (y := y)
    (fun i ↦ ⟨(toFun φ ⟨k + i.val, by
        have := i.isLt.trans_eq (card_ofCard _); omega⟩).val - card x, by
      have := (toFun φ ⟨k + i.val, by have := i.isLt.trans_eq (card_ofCard _); omega⟩).isLt
      have := hge ⟨k + i.val, by have := i.isLt.trans_eq (card_ofCard _); omega⟩
        (Nat.le_add_right _ _)
      omega⟩)
    (fun i j hij ↦ Fin.mk_le_mk.2 (Nat.sub_le_sub_right (monotone_toFun φ
      (Fin.mk_le_mk.2 (Nat.add_le_add_left (Fin.mk_le_mk.1 hij) _))) _))
  refine ⟨⟨⟨(ofCard k, ofCard (card n - k)), hab⟩, f, g⟩, toFun_injective (funext fun i ↦ ?_)⟩
  apply Fin.ext
  dsimp only
  rw [toFun_comp_apply]
  by_cases hi : i.val < k
  · rw [val_toFun_tensorHom_of_lt _ _ _ (by rw [val_toFun_eqToHom, card_ofCard]; exact hi), hf]
    simp only [val_toFun_eqToHom]
  · rw [val_toFun_tensorHom_of_le _ _ _ (by rw [val_toFun_eqToHom, card_ofCard]; omega), hg]
    have := hge i (by omega)
    simp only [val_toFun_eqToHom, card_ofCard]
    have hi' : (⟨k + (i.val - k), by omega⟩ : Fin (card n)) = i := Fin.ext (by
      simp only
      omega)
    rw [hi']
    omega

theorem bijective_eqToHom_comp_tensorHom (n x y : AugmentedSimplexCategory) :
    Function.Bijective (fun p : Σ s : {s : AugmentedSimplexCategory × AugmentedSimplexCategory //
        s.1 ⊗ s.2 = n}, (s.1.1 ⟶ x) × (s.1.2 ⟶ y) ↦ eqToHom p.1.2.symm ≫ (p.2.1 ⊗ₘ p.2.2)) :=
  ⟨injective_eqToHom_comp_tensorHom n x y, surjective_eqToHom_comp_tensorHom n x y⟩

section FirstVertex

scoped notation "𝟘" => (WithInitial.of ⦋0⦌ : AugmentedSimplexCategory)

theorem card_zero_tensorObj (y : AugmentedSimplexCategory) : card (𝟘 ⊗ y) = 1 + card y := by
  rw [card_tensorObj]
  rfl

theorem val_toFun_inr_zero (y : AugmentedSimplexCategory) (i : Fin (card y)) :
    (toFun (inr 𝟘 y) i).val = i.val + 1 := by
  rw [val_toFun_inr, Nat.add_comm]
  rfl

theorem injective_toFun_inr_zero (y : AugmentedSimplexCategory) :
    Function.Injective (toFun (inr 𝟘 y)) := fun i j hij => by
  have h₁ := val_toFun_inr_zero y i
  have h₂ := val_toFun_inr_zero y j
  rw [hij] at h₁
  exact Fin.ext (by omega)

theorem val_toFun_whiskerLeft_of_eq_zero {y y' : AugmentedSimplexCategory} (f : y ⟶ y')
    (i : Fin (card (𝟘 ⊗ y))) (hi : i.val = 0) : (toFun (𝟘 ◁ f) i).val = 0 := by
  rw [← id_tensorHom, val_toFun_tensorHom_of_lt (𝟙 𝟘) f i (by rw [hi]; exact Nat.one_pos),
    toFun_id]
  exact hi

theorem val_toFun_whiskerLeft_of_ne_zero {y y' : AugmentedSimplexCategory} (f : y ⟶ y')
    (i : Fin (card (𝟘 ⊗ y))) (hi : i.val ≠ 0) :
    (toFun (𝟘 ◁ f) i).val = (toFun f ⟨i.val - 1, by
      have h₁ := i.isLt; have h₂ := card_tensorObj 𝟘 y; have h₃ : card 𝟘 = 1 := rfl
      omega⟩).val + 1 := by
  rw [← id_tensorHom, val_toFun_tensorHom_of_le (𝟙 𝟘) f i (Nat.one_le_iff_ne_zero.2 hi),
    Nat.add_comm]
  rfl

theorem injective_toFun_whiskerLeft_zero {b c : AugmentedSimplexCategory} (f : b ⟶ c)
    (hf : Function.Injective (toFun f)) : Function.Injective (toFun (𝟘 ◁ f)) := fun i j hij => by
  have hv := congrArg Fin.val hij
  refine Fin.ext ?_
  by_cases hi : i.val = 0 <;> by_cases hj : j.val = 0
  · rw [hi, hj]
  · rw [val_toFun_whiskerLeft_of_eq_zero _ _ hi, val_toFun_whiskerLeft_of_ne_zero _ _ hj] at hv
    omega
  · rw [val_toFun_whiskerLeft_of_ne_zero _ _ hi, val_toFun_whiskerLeft_of_eq_zero _ _ hj] at hv
    omega
  · rw [val_toFun_whiskerLeft_of_ne_zero _ _ hi, val_toFun_whiskerLeft_of_ne_zero _ _ hj] at hv
    have := congrArg Fin.val (hf (Fin.ext (Nat.add_right_cancel hv)))
    simp only at this
    omega

end FirstVertex

@[reassoc] theorem inl'_comp_tensorHomOf {x₁ y₁ x₂ y₂ : SimplexCategory} (f₁ : x₁ ⟶ y₁)
    (f₂ : x₂ ⟶ y₂) : inl' x₁ x₂ ≫ tensorHomOf f₁ f₂ = f₁ ≫ inl' y₁ y₂ :=
  inl_comp_tensorHom (x₁ := .of x₁) (y₁ := .of y₁) (x₂ := .of x₂) (y₂ := .of y₂) f₁ f₂

@[reassoc] theorem inr'_comp_tensorHomOf {x₁ y₁ x₂ y₂ : SimplexCategory} (f₁ : x₁ ⟶ y₁)
    (f₂ : x₂ ⟶ y₂) : inr' x₁ x₂ ≫ tensorHomOf f₁ f₂ = f₂ ≫ inr' y₁ y₂ :=
  inr_comp_tensorHom (x₁ := .of x₁) (y₁ := .of y₁) (x₂ := .of x₂) (y₂ := .of y₂) f₁ f₂

theorem inl'_eq_δ_last (n : ℕ) : inl' ⦋n⦌ ⦋0⦌ = SimplexCategory.δ (Fin.last (n + 1)) := by
  ext i
  simp [inl'_eval, SimplexCategory.δ, Fin.succAbove_last]

theorem inl'_comp_σ_last (n : ℕ) :
    (inl' ⦋n⦌ ⦋0⦌ : ⦋n⦌ ⟶ ⦋n + 1⦌) ≫ SimplexCategory.σ (Fin.last n) = 𝟙 ⦋n⦌ := by
  rw [inl'_eq_δ_last, ← Fin.succ_last, SimplexCategory.δ_comp_σ_succ]

theorem inr'_comp_σ_last (n : ℕ) :
    inr' ⦋n + 1⦌ ⦋0⦌ ≫ SimplexCategory.σ (Fin.last (n + 1)) = inr' ⦋n⦌ ⦋0⦌ := by
  ext i
  fin_cases i
  simp [inr'_eval, SimplexCategory.σ, Fin.predAbove, Fin.lt_def]

@[reassoc] theorem tensorHomOf_comp_tensorHomOf {x₁ y₁ z₁ x₂ y₂ z₂ : SimplexCategory}
    (f₁ : x₁ ⟶ y₁) (f₂ : x₂ ⟶ y₂) (g₁ : y₁ ⟶ z₁) (g₂ : y₂ ⟶ z₂) :
    tensorHomOf f₁ f₂ ≫ tensorHomOf g₁ g₂ = tensorHomOf (f₁ ≫ g₁) (f₂ ≫ g₂) :=
  tensorHom_comp_tensorHom (x₁ := .of x₁) (y₁ := .of y₁) (z₁ := .of z₁) (x₂ := .of x₂)
    (y₂ := .of y₂) (z₂ := .of z₂) f₁ f₂ g₁ g₂

def ordinalSum : SimplexCategory × SimplexCategory ⥤ SimplexCategory where
  obj p := tensorObjOf p.1 p.2
  map f := tensorHomOf f.1 f.2
  map_id p := tensor_id (.of p.1) (.of p.2)
  map_comp f g := (tensorHomOf_comp_tensorHomOf f.1 f.2 g.1 g.2).symm

end AugmentedSimplexCategory
