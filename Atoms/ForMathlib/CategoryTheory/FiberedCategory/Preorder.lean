import Atoms.ForMathlib.Order.Grade
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.FiberedCategory.Fibered
import Mathlib.Order.Cover
import Mathlib.Order.WithBot

open CategoryTheory

namespace Monotone

variable {α β : Type*} [Preorder α] [Preorder β] {f : α → β} (hf : Monotone f)

theorem functor_isHomLift_iff {R S : β} {a b : α} (g : R ⟶ S) (φ : a ⟶ b) :
    hf.functor.IsHomLift g φ ↔ f a = R ∧ f b = S :=
  ⟨fun _ => ⟨IsHomLift.domain_eq hf.functor g φ, IsHomLift.codomain_eq hf.functor g φ⟩,
    fun ⟨ha, hb⟩ => IsHomLift.of_fac hf.functor g φ ha hb (Subsingleton.elim _ _)⟩

theorem functor_isFibered_iff : hf.functor.IsFibered ↔
    ∀ x y, y ≤ f x → ∃ y' ≤ x, f y' = y ∧ ∀ z ≤ x, f z ≤ y → z ≤ y' := by
  constructor
  · intro _ x y hy
    let g : y ⟶ hf.functor.obj x := homOfLE hy
    obtain ⟨b, φ, hφ⟩ := Functor.IsPreFibered.exists_isCartesian' (p := hf.functor) g
    have hb : f b = y := IsHomLift.domain_eq hf.functor g φ
    refine ⟨b, leOfHom φ, hb, fun z hz hzy => ?_⟩
    let f' : hf.functor.obj z ⟶ hf.functor.obj x := homOfLE (hzy.trans hy)
    have : hf.functor.IsHomLift f' (homOfLE hz) := (functor_isHomLift_iff hf _ _).2 ⟨rfl, rfl⟩
    obtain ⟨χ, -, -⟩ := Functor.IsStronglyCartesian.universal_property hf.functor g φ
      (homOfLE hzy : hf.functor.obj z ⟶ y) f' (Subsingleton.elim _ _) (homOfLE hz)
    exact leOfHom χ
  · intro h
    refine Functor.IsFibered.of_exists_isStronglyCartesian fun x R g => ?_
    obtain ⟨y', hy'x, hfy', hmax⟩ := h x R (leOfHom g)
    have : hf.functor.IsHomLift g (homOfLE hy'x) := (functor_isHomLift_iff hf _ _).2 ⟨hfy', rfl⟩
    refine ⟨y', homOfLE hy'x, ⟨fun g' φ' _ => ?_⟩⟩
    refine ⟨homOfLE (hmax _ (leOfHom φ') (leOfHom g')),
      ⟨(functor_isHomLift_iff hf _ _).2 ⟨rfl, hfy'⟩, Subsingleton.elim _ _⟩,
      fun _ _ => Subsingleton.elim _ _⟩

instance decidableFunctorIsFibered [Fintype α] [Fintype β] [DecidableLE α] [DecidableLE β]
    [DecidableEq β] : Decidable hf.functor.IsFibered :=
  decidable_of_iff _ (functor_isFibered_iff hf).symm

theorem exists_lift [hf.functor.IsFibered] {x : α} {y : β} (hy : y ≤ f x) :
    ∃ y' ≤ x, f y' = y ∧ ∀ z ≤ x, f z ≤ y → z ≤ y' :=
  (functor_isFibered_iff hf).1 inferInstance x y hy

theorem functor_isFibered_id : (monotone_id (α := α)).functor.IsFibered :=
  (functor_isFibered_iff _).2 fun _ y hy => ⟨y, hy, rfl, fun _ _ h => h⟩

theorem functor_isFibered_comp {γ : Type*} [Preorder γ] {g : β → γ} (hg : Monotone g)
    [hf.functor.IsFibered] [hg.functor.IsFibered] : (hg.comp hf).functor.IsFibered := by
  refine (functor_isFibered_iff _).2 fun x y hy => ?_
  obtain ⟨y₁, hy₁le, hy₁eq, hy₁max⟩ := exists_lift hg hy
  obtain ⟨y₂, hy₂le, hy₂eq, hy₂max⟩ := exists_lift hf hy₁le
  refine ⟨y₂, hy₂le, by rw [Function.comp_apply, hy₂eq, hy₁eq], fun z hz hgz => ?_⟩
  exact hy₂max z hz (hy₁max (f z) (hf hz) hgz)

theorem fibration_of_functor_isFibered [hf.functor.IsFibered] :
    Relation.Fibration (· ≤ ·) (· ≤ ·) f := fun _ _ hy =>
  let ⟨y', hy', hfy', _⟩ := exists_lift hf hy
  ⟨y', hy', hfy'⟩

theorem exists_greatest_fibre [hf.functor.IsFibered] {t : α} (ht : ∀ z, z ≤ t) {y : β}
    (hy : y ≤ f t) : ∃ x, f x = y ∧ ∀ z, f z = y → z ≤ x := by
  obtain ⟨x, -, hx, hmax⟩ := exists_lift hf hy
  exact ⟨x, hx, fun z hz => hmax z (ht z) hz.le⟩

theorem apply_eq_of_minimal_upper_bound [hf.functor.IsFibered] {x x' z : α} (hx : x ≤ z)
    (hx' : x' ≤ z) (hmin : ∀ z', x ≤ z' → x' ≤ z' → z' ≤ z → z' = z) (h : f x' = f x) :
    f z = f x := by
  obtain ⟨z', hz'z, hz'eq, hz'max⟩ := exists_lift hf (hf hx)
  rw [← hmin z' (hz'max x hx le_rfl) (hz'max x' hx' h.le) hz'z, hz'eq]

theorem apply_covBy_apply {α β : Type*} [PartialOrder α] [PartialOrder β] {f : α → β}
    (hf : Monotone f) [hf.functor.IsFibered] {y₁ y : α} (hcov : y₁ ⋖ y) (hne : f y₁ ≠ f y) :
    f y₁ ⋖ f y := by
  refine ⟨lt_of_le_of_ne (hf hcov.le) hne, fun c h₁ h₂ => ?_⟩
  obtain ⟨s, hsy, hsc, hsmax⟩ := exists_lift hf h₂.le
  have hs₁ : s ≠ y₁ := fun e => h₁.ne (by rw [← hsc, e])
  have hs₂ : s ≠ y := fun e => h₂.ne (by rw [← hsc, e])
  exact hcov.2 (lt_of_le_of_ne (hsmax y₁ hcov.le h₁.le) (Ne.symm hs₁)) (lt_of_le_of_ne hsy hs₂)

theorem withBotMap_functor_isFibered [hf.functor.IsFibered] :
    (WithBot.monotone_map_iff.2 hf).functor.IsFibered := by
  refine (functor_isFibered_iff _).2 fun a w h => ?_
  induction w using WithBot.recBotCoe with
  | bot =>
    refine ⟨⊥, bot_le, rfl, fun c _ hc => ?_⟩
    induction c using WithBot.recBotCoe with
    | bot => exact le_rfl
    | coe t => exact absurd hc (WithBot.not_coe_le_bot (f t))
  | coe v =>
    induction a using WithBot.recBotCoe with
    | bot => exact absurd h (by simp)
    | coe x =>
      rw [WithBot.map_coe, WithBot.coe_le_coe] at h
      obtain ⟨y, hyx, hyv, hymax⟩ := exists_lift hf h
      refine ⟨y, WithBot.coe_le_coe.2 hyx, by rw [WithBot.map_coe, hyv], fun c hc hcv => ?_⟩
      induction c using WithBot.recBotCoe with
      | bot => exact bot_le
      | coe t =>
        rw [WithBot.map_coe, WithBot.coe_le_coe] at hcv
        exact WithBot.coe_le_coe.2 (hymax t (WithBot.coe_le_coe.1 hc) hcv)

theorem functor_isFibered_of_comp {γ : Type*} [Preorder γ] (e : β ↪o γ)
    (h : (e.monotone.comp hf).functor.IsFibered) : hf.functor.IsFibered := by
  refine (functor_isFibered_iff hf).2 fun x y hy => ?_
  obtain ⟨y', hy'x, hy', hmax⟩ := exists_lift (e.monotone.comp hf) (e.monotone hy)
  exact ⟨y', hy'x, e.injective hy', fun z hz hzy => hmax z hz (e.monotone hzy)⟩

end Monotone

namespace Monotone

variable {α β : Type*} [PartialOrder α] [GradeMinOrder ℕ α] [PartialOrder β] [GradeMinOrder ℕ β]
  {f : α → β} (hf : Monotone f) [hf.functor.IsFibered]
include hf

theorem grade_apply_eq_of_covBy {x x' : α} (hx : grade ℕ (f x) = grade ℕ x) (hcov : x' ⋖ x) :
    grade ℕ (f x') = grade ℕ x' := by
  have hle := (fibration_of_functor_isFibered hf).grade_apply_le x'
  have hx' := Nat.covBy_iff_add_one_eq.1 (hcov.grade ℕ)
  have hne : f x' ≠ f x := fun h => by
    rw [h] at hle
    omega
  have := Nat.covBy_iff_add_one_eq.1 ((apply_covBy_apply hf hcov hne).grade ℕ)
  omega

theorem grade_apply_eq_of_isTop {t : α} (ht : IsTop t) (hd : grade ℕ (f t) = grade ℕ t) (x : α) :
    grade ℕ (f x) = grade ℕ x := by
  obtain ⟨m, hm⟩ : ∃ m, grade ℕ t - grade ℕ x = m := ⟨_, rfl⟩
  induction m using Nat.strong_induction_on generalizing x with
  | _ m ih =>
    rcases (ht x).eq_or_lt with rfl | hlt
    · exact hd
    · obtain ⟨z, hxz, hzt⟩ := exists_covBy_le_of_lt hlt
      have h₁ := Nat.covBy_iff_add_one_eq.1 (hxz.grade ℕ)
      have h₂ := grade_mono (𝕆 := ℕ) hzt
      exact grade_apply_eq_of_covBy hf (ih _ (by omega) z rfl) hxz

theorem injective_of_grade_apply_eq {t : α} (ht : IsTop t) (hd : ∀ x, grade ℕ (f x) = grade ℕ x) :
    Function.Injective f := by
  intro x x' h
  obtain ⟨s, hs, hmax⟩ := exists_greatest_fibre hf ht (hf (ht x))
  have he (z : α) (hz : f z = f x) : z = s :=
    GradeOrder.eq_of_le_of_grade_le (hmax z hz) (by rw [← hd s, ← hd z, hs, hz])
  exact (he x rfl).trans (he x' h.symm).symm

end Monotone
