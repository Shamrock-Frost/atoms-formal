import Atoms.ForMathlib.AlgebraicTopology.SimplexCategory.Augmented.ExtraDegeneracy
import Atoms.ForMathlib.AlgebraicTopology.SimplexCategory.Augmented.Injective

open CategoryTheory MonoidalCategory Opposite Simplicial Limits

namespace AugmentedSimplexCategory

universe w

private lemma toFun_comp {x y z : AugmentedSimplexCategory} (f : x ⟶ y) (g : y ⟶ z) :
    toFun (f ≫ g) = toFun g ∘ toFun f :=
  funext (toFun_comp_apply f g)

private lemma hom_ext_val {x y : AugmentedSimplexCategory} {f g : x ⟶ y}
    (h : ∀ i, (toFun f i).val = (toFun g i).val) : f = g :=
  toFun_injective (funext fun i => Fin.ext (h i))

private lemma mono_of_injective {x y : AugmentedSimplexCategory} (f : x ⟶ y)
    (hf : Function.Injective (toFun f)) : Mono f :=
  ⟨fun g h e => toFun_injective (funext fun i => hf (by
    rw [← toFun_comp_apply, ← toFun_comp_apply, e]))⟩

private lemma strictMono_toFun {x y : AugmentedSimplexCategory} (f : x ⟶ y)
    (hf : Function.Injective (toFun f)) : StrictMono (toFun f) :=
  (monotone_toFun f).strictMono_of_injective hf

private lemma exists_comp_eq_of_injective {b c d : AugmentedSimplexCategory} (m : d ⟶ c)
    (hm : Function.Injective (toFun m)) (g : b ⟶ c) (hg : ∀ i, ∃ j, toFun m j = toFun g i) :
    ∃ k : b ⟶ d, k ≫ m = g := by
  choose k hk using hg
  have hmono : Monotone k := fun i i' hii' =>
    (strictMono_toFun m hm).le_iff_le.1 (by rw [hk, hk]; exact monotone_toFun g hii')
  obtain ⟨k', hk'⟩ := exists_toFun_eq k hmono
  refine ⟨k', toFun_injective (funext fun i => ?_)⟩
  rw [toFun_comp_apply, hk', hk]

private lemma exists_injective_range {y : AugmentedSimplexCategory} (S : Finset (Fin (card y))) :
    ∃ (d : AugmentedSimplexCategory) (m : d ⟶ y), Function.Injective (toFun m) ∧
      ∀ j, j ∈ S ↔ ∃ i, toFun m i = j := by
  obtain ⟨d, hd⟩ : ∃ d, card d = S.card := ⟨ofCard _, card_ofCard _⟩
  obtain ⟨m, hm⟩ := exists_toFun_eq (x := d) (y := y) (S.orderEmbOfFin hd.symm)
    (S.orderEmbOfFin hd.symm).monotone
  refine ⟨d, m, by rw [hm]; exact (S.orderEmbOfFin hd.symm).injective, fun j => ?_⟩
  rw [hm, ← Finset.mem_coe, ← S.range_orderEmbOfFin hd.symm, Set.mem_range]

private lemma exists_surjective_injective_factorization {b c : AugmentedSimplexCategory}
    (g : b ⟶ c) : ∃ (d : AugmentedSimplexCategory) (e : b ⟶ d) (m : d ⟶ c),
      Function.Surjective (toFun e) ∧ Function.Injective (toFun m) ∧ e ≫ m = g := by
  classical
  obtain ⟨d, m, hminj, hm⟩ := exists_injective_range (Finset.univ.image (toFun g))
  obtain ⟨e, he⟩ := exists_comp_eq_of_injective m hminj g fun i =>
    (hm _).1 (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  refine ⟨d, e, m, fun j => ?_, hminj, he⟩
  obtain ⟨i, -, hi⟩ := Finset.mem_image.1 ((hm (toFun m j)).2 ⟨j, rfl⟩)
  exact ⟨i, hminj (by rw [← toFun_comp_apply, he, hi])⟩

private lemma exists_comp_eq_id {b c : AugmentedSimplexCategory} (e : b ⟶ c)
    (α : Fin (card c) → Fin (card b)) (hα : ∀ y, toFun e (α y) = y) :
    ∃ s : c ⟶ b, s ≫ e = 𝟙 c ∧ toFun s = α := by
  have hmono : Monotone α := fun y y' hyy' => by
    by_contra h
    have := monotone_toFun e (le_of_lt (lt_of_not_ge h))
    rw [hα, hα] at this
    have hyy : y = y' := le_antisymm hyy' this
    subst hyy
    exact h le_rfl
  obtain ⟨s, hs⟩ := exists_toFun_eq α hmono
  exact ⟨s, toFun_injective (funext fun y => by rw [toFun_comp_apply, hs, hα, toFun_id]), hs⟩

private lemma exists_section {b c : AugmentedSimplexCategory} (e : b ⟶ c)
    (he : Function.Surjective (toFun e)) (i : Fin (card b)) :
    ∃ s : c ⟶ b, s ≫ e = 𝟙 c ∧ toFun s (toFun e i) = i := by
  classical
  obtain ⟨s, hs, hsα⟩ := exists_comp_eq_id e
    (fun y => if y = toFun e i then i else Classical.choose (he y)) (fun y => by
      by_cases hy : y = toFun e i
      · rw [if_pos hy, hy]
      · rw [if_neg hy]
        exact Classical.choose_spec (he y))
  refine ⟨s, hs, ?_⟩
  rw [hsα]
  exact if_pos rfl

private lemma eq_id_of_surjective {b : AugmentedSimplexCategory} (f : b ⟶ b)
    (hf : Function.Surjective (toFun f)) : f = 𝟙 b :=
  eq_id_of_injective f (Finite.injective_iff_surjective.2 hf)

private lemma val_toFun_iso_hom {x y : AugmentedSimplexCategory} (e : x ≅ y) (i : Fin (card x)) :
    (toFun e.hom i).val = i.val := by
  have hl : ∀ j, toFun e.inv (toFun e.hom j) = j := fun j => by
    rw [← toFun_comp_apply, e.hom_inv_id, toFun_id]
  have hr : ∀ j, toFun e.hom (toFun e.inv j) = j := fun j => by
    rw [← toFun_comp_apply, e.inv_hom_id, toFun_id]
  have hc : card x = card y := by
    simpa using Fintype.card_congr (Equiv.mk (toFun e.hom) (toFun e.inv) hl hr)
  exact val_toFun_of_injective_of_card_eq e.hom (injective_toFun_of_isIso e.hom) hc i

private def mu (y : AugmentedSimplexCategory) : 𝟘 ⊗ (𝟘 ⊗ y) ⟶ 𝟘 ⊗ y :=
  (α_ 𝟘 𝟘 y).inv ≫ zeroMul ▷ y

theorem val_toFun_associator_inv_comp_whiskerRight_zeroMul (y : AugmentedSimplexCategory)
    (i : Fin (card (𝟘 ⊗ (𝟘 ⊗ y)))) :
    (toFun ((α_ 𝟘 𝟘 y).inv ≫ zeroMul ▷ y) i).val = i.val - 1 := by
  rw [toFun_comp_apply, ← tensorHom_id]
  have hi : (toFun (α_ 𝟘 𝟘 y).inv i).val = i.val := val_toFun_iso_hom (α_ 𝟘 𝟘 y).symm i
  by_cases h : i.val < 2
  · rw [val_toFun_tensorHom_of_lt zeroMul (𝟙 y) _ (by rw [hi]; exact h)]
    have : (toFun zeroMul ⟨(toFun (α_ 𝟘 𝟘 y).inv i).val, by rw [hi]; exact h⟩).val < 1 :=
      Fin.isLt _
    omega
  · rw [val_toFun_tensorHom_of_le zeroMul (𝟙 y) _ (by rw [hi]; exact le_of_not_gt h), toFun_id]
    simp only [hi]
    change 1 + (i.val - 2) = i.val - 1
    omega

private lemma val_toFun_mu (y : AugmentedSimplexCategory) (i : Fin (card (𝟘 ⊗ (𝟘 ⊗ y)))) :
    (toFun (mu y) i).val = i.val - 1 :=
  val_toFun_associator_inv_comp_whiskerRight_zeroMul y i

private lemma inr_comp_mu (c : AugmentedSimplexCategory) : inr 𝟘 (𝟘 ⊗ c) ≫ mu c = 𝟙 _ :=
  hom_ext_val fun i => by
    rw [toFun_comp_apply, val_toFun_mu, val_toFun_inr_zero, toFun_id]
    omega

private lemma whiskerLeft_inr_comp_mu (c : AugmentedSimplexCategory) :
    𝟘 ◁ inr 𝟘 c ≫ mu c = 𝟙 _ :=
  hom_ext_val fun i => by
    rw [toFun_comp_apply, val_toFun_mu, toFun_id]
    by_cases h : i.val = 0
    · rw [val_toFun_whiskerLeft_of_eq_zero _ _ h, h]
    · rw [val_toFun_whiskerLeft_of_ne_zero _ _ h, val_toFun_inr_zero]
      dsimp only
      omega

private lemma whiskerLeft_whiskerLeft_comp_mu {c c' : AugmentedSimplexCategory} (σ : c ⟶ c') :
    𝟘 ◁ (𝟘 ◁ σ) ≫ mu c' = mu c ≫ 𝟘 ◁ σ :=
  hom_ext_val fun i => by
    rw [toFun_comp_apply, toFun_comp_apply, val_toFun_mu]
    by_cases h : i.val = 0
    · rw [val_toFun_whiskerLeft_of_eq_zero _ _ h, val_toFun_whiskerLeft_of_eq_zero]
      rw [val_toFun_mu, h]
    · rw [val_toFun_whiskerLeft_of_ne_zero _ _ h, Nat.add_sub_cancel]
      congr 2
      exact Fin.ext (by rw [val_toFun_mu])

private lemma val_toFun_of_inr_comp_eq_id {c : AugmentedSimplexCategory} (ρ : 𝟘 ⊗ c ⟶ c)
    (hρ : inr 𝟘 c ≫ ρ = 𝟙 c) (k : Fin (card (𝟘 ⊗ c))) : (toFun ρ k).val = k.val - 1 := by
  have hinr : ∀ j, toFun ρ (toFun (inr 𝟘 c) j) = j := fun j => by
    rw [← toFun_comp_apply, hρ, toFun_id]
  by_cases hk : k.val = 0
  · have hc : 0 < card c := by
      have := (toFun ρ k).isLt
      omega
    have h₁ : toFun (inr 𝟘 c) ⟨0, hc⟩ = ⟨1, by rw [card_zero_tensorObj]; omega⟩ :=
      Fin.ext (val_toFun_inr_zero c _)
    have h₂ := monotone_toFun ρ (show k ≤ ⟨1, by rw [card_zero_tensorObj]; omega⟩ from
      Fin.le_iff_val_le_val.2 (by simp only; omega))
    rw [← h₁, hinr] at h₂
    have := Fin.le_iff_val_le_val.1 h₂
    simp only at this
    omega
  · have h₁ : toFun (inr 𝟘 c) ⟨k.val - 1, by
        have h₁ := k.isLt; have h₂ := card_zero_tensorObj c; omega⟩ = k :=
      Fin.ext (by rw [val_toFun_inr_zero]; dsimp only; omega)
    rw [← h₁, hinr, val_toFun_inr_zero]
    dsimp only
    omega

private lemma whiskerLeft_comp_eq_mu_comp {c : AugmentedSimplexCategory} (ρ : 𝟘 ⊗ c ⟶ c)
    (hρ : inr 𝟘 c ≫ ρ = 𝟙 c) : 𝟘 ◁ ρ ≫ ρ = mu c ≫ ρ :=
  hom_ext_val fun i => by
    rw [toFun_comp_apply, toFun_comp_apply, val_toFun_of_inr_comp_eq_id ρ hρ,
      val_toFun_of_inr_comp_eq_id ρ hρ, val_toFun_mu]
    by_cases h : i.val = 0
    · rw [val_toFun_whiskerLeft_of_eq_zero _ _ h, h]
    · rw [val_toFun_whiskerLeft_of_ne_zero _ _ h, val_toFun_of_inr_comp_eq_id ρ hρ]
      dsimp only
      omega

private lemma exists_eq_whiskerLeft {b c : AugmentedSimplexCategory} (f : 𝟘 ⊗ b ⟶ 𝟘 ⊗ c)
    (hf : Function.Injective (toFun f))
    (h₀ : (toFun f ⟨0, by rw [card_zero_tensorObj]; omega⟩).val = 0) :
    ∃ f₂ : b ⟶ c, f = 𝟘 ◁ f₂ := by
  have hpos : ∀ j, (toFun f (toFun (inr 𝟘 b) j)).val ≠ 0 := fun j h =>
    by simpa [val_toFun_inr_zero] using congrArg Fin.val (hf (Fin.ext (h.trans h₀.symm)))
  obtain ⟨f₂, hf₂⟩ := exists_toFun_eq (x := b) (y := c)
    (fun j => ⟨(toFun f (toFun (inr 𝟘 b) j)).val - 1, by
      have h₁ := (toFun f (toFun (inr 𝟘 b) j)).isLt; have h₂ := card_zero_tensorObj c
      have h₃ := hpos j; omega⟩)
    (fun j j' hjj' => Fin.mk_le_mk.2 (Nat.sub_le_sub_right (Fin.le_iff_val_le_val.1
      (monotone_toFun f (monotone_toFun _ hjj'))) 1))
  refine ⟨f₂, hom_ext_val fun i => ?_⟩
  by_cases h : i.val = 0
  · rw [val_toFun_whiskerLeft_of_eq_zero _ _ h]
    have hi : i = ⟨0, by rw [card_zero_tensorObj]; omega⟩ := Fin.ext h
    rw [hi]
    exact h₀
  · rw [val_toFun_whiskerLeft_of_ne_zero _ _ h, hf₂]
    have hi : toFun (inr 𝟘 b) ⟨i.val - 1, by
        have h₁ := i.isLt; have h₂ := card_zero_tensorObj b; omega⟩ = i :=
      Fin.ext (by rw [val_toFun_inr_zero]; dsimp only; omega)
    dsimp only
    rw [hi]
    have hne : toFun f i ≠ toFun f ⟨0, by rw [card_zero_tensorObj]; omega⟩ := fun he =>
      h (by rw [hf he])
    have : (toFun f i).val ≠ 0 := fun h' => hne (Fin.ext (by rw [h', h₀]))
    omega

private lemma exists_comp_inr_eq {b c : AugmentedSimplexCategory} (φ : b ⟶ 𝟘 ⊗ c)
    (hφ : ∀ i, (toFun φ i).val ≠ 0) : ∃ ψ : b ⟶ c, ψ ≫ inr 𝟘 c = φ :=
  exists_comp_eq_of_injective (inr 𝟘 c) (injective_toFun_inr_zero c) φ (fun i =>
    ⟨⟨(toFun φ i).val - 1, by
      have h₁ := (toFun φ i).isLt; have h₂ := card_zero_tensorObj c; have := hφ i; omega⟩,
      Fin.ext (by rw [val_toFun_inr_zero]; have := hφ i; dsimp only; omega)⟩)

private lemma exists_comp_whiskerLeft_eq {b c e : AugmentedSimplexCategory} (φ : b ⟶ 𝟘 ⊗ c)
    (n : e ⟶ c) (hn : Function.Injective (toFun n))
    (hrange : ∀ i, (toFun φ i).val ≠ 0 → ∃ l, (toFun n l).val + 1 = (toFun φ i).val) :
    ∃ κ : b ⟶ 𝟘 ⊗ e, κ ≫ 𝟘 ◁ n = φ :=
  exists_comp_eq_of_injective (𝟘 ◁ n) (injective_toFun_whiskerLeft_zero n hn) φ (fun i => by
    by_cases hi : (toFun φ i).val = 0
    · exact ⟨⟨0, by rw [card_zero_tensorObj]; omega⟩,
        Fin.ext (by rw [val_toFun_whiskerLeft_of_eq_zero _ _ rfl, hi])⟩
    · obtain ⟨l, hl⟩ := hrange i hi
      refine ⟨⟨l.val + 1, by have := l.isLt; rw [card_zero_tensorObj]; omega⟩, Fin.ext ?_⟩
      rw [val_toFun_whiskerLeft_of_ne_zero _ _ (Nat.succ_ne_zero _), ← hl]
      rfl)

private lemma exists_val_toFun_eq_of_comp_whiskerLeft {b c d : AugmentedSimplexCategory}
    (ψ : b ⟶ 𝟘 ⊗ d) (m : d ⟶ c) (i : Fin (card b)) (hi : (toFun (ψ ≫ 𝟘 ◁ m) i).val ≠ 0) :
    ∃ l, (toFun m l).val + 1 = (toFun (ψ ≫ 𝟘 ◁ m) i).val := by
  rw [toFun_comp_apply] at hi ⊢
  by_cases h : (toFun ψ i).val = 0
  · exact absurd (val_toFun_whiskerLeft_of_eq_zero _ _ h) hi
  · exact ⟨_, (val_toFun_whiskerLeft_of_ne_zero _ _ h).symm⟩

section Nondegenerate

variable {P : AugmentedSimplexCategoryᵒᵖ ⥤ Type w}

private def IsNondeg (P : AugmentedSimplexCategoryᵒᵖ ⥤ Type w) {y : AugmentedSimplexCategory}
    (x : P.obj (op y)) : Prop :=
  ∀ (c : AugmentedSimplexCategory) (f : y ⟶ c) (z : P.obj (op c)), P.map f.op z = x →
    card y ≤ card c

private lemma card_le_card_of_surjective {x y : AugmentedSimplexCategory} (f : x ⟶ y)
    (hf : Function.Surjective (toFun f)) : card y ≤ card x := by
  simpa using Fintype.card_le_of_surjective _ hf

private lemma card_le_card_of_injective {x y : AugmentedSimplexCategory} (f : x ⟶ y)
    (hf : Function.Injective (toFun f)) : card x ≤ card y := by
  simpa using Fintype.card_le_of_injective _ hf

private lemma bijective_of_surjective_of_card_le {x y : AugmentedSimplexCategory} (f : x ⟶ y)
    (hf : Function.Surjective (toFun f)) (h : card x ≤ card y) : Function.Bijective (toFun f) :=
  (Fintype.bijective_iff_surjective_and_card _).2 ⟨hf, by
    simpa using le_antisymm h (card_le_card_of_surjective f hf)⟩

private lemma bijective_of_injective_of_card_le {x y : AugmentedSimplexCategory} (f : x ⟶ y)
    (hf : Function.Injective (toFun f)) (h : card y ≤ card x) : Function.Bijective (toFun f) :=
  (Fintype.bijective_iff_injective_and_card _).2 ⟨hf, by
    simpa using le_antisymm (card_le_card_of_injective f hf) h⟩

private lemma injective_of_isNondeg {d d' : AugmentedSimplexCategory} {r : P.obj (op d)}
    (hr : IsNondeg P r) (g : d ⟶ d') (r' : P.obj (op d')) (h : P.map g.op r' = r) :
    Function.Injective (toFun g) := by
  obtain ⟨c, e, m, he, hm, rfl⟩ := exists_surjective_injective_factorization g
  have hc := hr c e (P.map m.op r') (by rw [← h, op_comp, P.map_comp_apply])
  rw [toFun_comp]
  exact hm.comp (bijective_of_surjective_of_card_le e he hc).1

private lemma exists_isNondeg (P : AugmentedSimplexCategoryᵒᵖ ⥤ Type w)
    {y : AugmentedSimplexCategory} (x : P.obj (op y)) :
    ∃ (d : AugmentedSimplexCategory) (ρ : y ⟶ d) (r : P.obj (op d)),
      Function.Surjective (toFun ρ) ∧ IsNondeg P r ∧ P.map ρ.op r = x := by
  suffices H : ∀ (n : ℕ) (y : AugmentedSimplexCategory) (x : P.obj (op y)), card y = n →
      ∃ (d : AugmentedSimplexCategory) (ρ : y ⟶ d) (r : P.obj (op d)),
        Function.Surjective (toFun ρ) ∧ IsNondeg P r ∧ P.map ρ.op r = x from H _ y x rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro y x h
    by_cases hx : IsNondeg P x
    · exact ⟨y, 𝟙 y, x, fun i => ⟨i, toFun_id y i⟩, hx, by simp⟩
    · simp only [IsNondeg, not_forall, not_le] at hx
      obtain ⟨c, f, z, hz, hc⟩ := hx
      obtain ⟨c', e, m, he, hm, rfl⟩ := exists_surjective_injective_factorization f
      obtain ⟨d, ρ, r, hρ, hr, hrx⟩ := ih (card c')
        (h ▸ lt_of_le_of_lt (card_le_card_of_injective m hm) hc) c' (P.map m.op z) rfl
      refine ⟨d, e ≫ ρ, r, ?_, hr, ?_⟩
      · rw [toFun_comp]
        exact hρ.comp he
      · rw [op_comp, P.map_comp_apply, hrx, ← hz, op_comp, P.map_comp_apply]

private lemma eq_of_isNondeg {y d d' : AugmentedSimplexCategory} {ρ : y ⟶ d} {ρ' : y ⟶ d'}
    {r : P.obj (op d)} {r' : P.obj (op d')} (hρ : Function.Surjective (toFun ρ))
    (hρ' : Function.Surjective (toFun ρ')) (hr : IsNondeg P r) (hr' : IsNondeg P r')
    (h : P.map ρ.op r = P.map ρ'.op r') :
    ∃ e : d = d', ρ ≫ eqToHom e = ρ' ∧ r = P.map (eqToHom e).op r' := by
  have key : ∀ (s : d ⟶ y), s ≫ ρ = 𝟙 d → P.map (s ≫ ρ').op r' = r := fun s hs => by
    rw [op_comp, P.map_comp_apply, ← h, ← P.map_comp_apply, ← op_comp, hs, op_id, P.map_id,
      types_id_apply]
  obtain ⟨s₀, hs₀⟩ := exists_comp_eq_id_of_surjective ρ hρ
  obtain ⟨t₀, ht₀⟩ := exists_comp_eq_id_of_surjective ρ' hρ'
  have hcard : card d = card d' := le_antisymm
    (card_le_card_of_injective _ (injective_of_isNondeg hr _ r' (key s₀ hs₀)))
    (card_le_card_of_injective _ (injective_of_isNondeg hr' _ r (by
      rw [op_comp, P.map_comp_apply, h, ← P.map_comp_apply, ← op_comp, ht₀, op_id, P.map_id,
        types_id_apply])))
  obtain rfl := card_injective hcard
  have hid : ∀ (s : d ⟶ y), s ≫ ρ = 𝟙 d → s ≫ ρ' = 𝟙 d := fun s hs =>
    eq_id_of_surjective _ (bijective_of_injective_of_card_le _
      (injective_of_isNondeg hr _ r' (key s hs)) le_rfl).2
  refine ⟨rfl, ?_, ?_⟩
  · rw [eqToHom_refl, Category.comp_id]
    refine toFun_injective (funext fun i => ?_)
    obtain ⟨s, hs, hsi⟩ := exists_section ρ hρ i
    have := congrArg (fun f => toFun f (toFun ρ i)) (hid s hs)
    simp only [toFun_comp_apply, hsi, toFun_id] at this
    exact this.symm
  · rw [eqToHom_refl, op_id, P.map_id, types_id_apply, ← key s₀ hs₀, hid s₀ hs₀, op_id,
      P.map_id, types_id_apply]

end Nondegenerate

section Boundary

variable {P Q : AugmentedSimplexCategoryᵒᵖ ⥤ Type w}

private lemma exists_boundary_hom {a : AugmentedSimplexCategory} {I : Type*}
    (dom : I → AugmentedSimplexCategory) (ι : ∀ i, dom i ⟶ a) (w : ∀ i, P.obj (op (dom i)))
    (hcover : ∀ (b : AugmentedSimplexCategory) (φ : b ⟶ a), ¬ Function.Surjective (toFun φ) →
      ∃ (i : I) (ψ : b ⟶ dom i), ψ ≫ ι i = φ)
    (hcompat : ∀ (i j : I) (b : AugmentedSimplexCategory) (ψ : b ⟶ dom i) (ψ' : b ⟶ dom j),
      ψ ≫ ι i = ψ' ≫ ι j → P.map ψ.op (w i) = P.map ψ'.op (w j)) :
    ∃ β : (boundary.{w} a).toFunctor ⟶ P, ∀ (i : I) (b : AugmentedSimplexCategory)
      (ψ : b ⟶ dom i) (φ : b ⟶ a) (h : ULift.up φ ∈ (boundary.{w} a).obj (op b)), ψ ≫ ι i = φ →
      β.app (op b) ⟨⟨φ⟩, h⟩ = P.map ψ.op (w i) := by
  choose i ψ hψ using hcover
  refine ⟨{ app b := ↾fun f => P.map (ψ b.unop f.1.down f.2).op (w (i b.unop f.1.down f.2))
            naturality b b' g := ?_ }, fun j b ψ' φ h hφ => ?_⟩
  · ext f
    have := hcompat _ _ _ (ψ b'.unop _ ((boundary a).toFunctor.map g f).2)
      (g.unop ≫ ψ b.unop f.1.down f.2) ((hψ _ _ _).trans ((congrArg (fun t => g.unop ≫ t)
        (hψ b.unop f.1.down f.2)).symm.trans (Category.assoc _ _ _).symm))
    dsimp
    rw [this, op_comp, Quiver.Hom.op_unop, P.map_comp_apply]
  · exact hcompat _ _ _ _ _ ((hψ _ _ _).trans hφ.symm)

private lemma exists_lift_of_boundary (p : P ⟶ Q) {a : AugmentedSimplexCategory}
    (hp : HasLiftingProperty (boundary a).ι p) (β : (boundary a).toFunctor ⟶ P)
    (q : Q.obj (op a))
    (hβ : ∀ (b : AugmentedSimplexCategoryᵒᵖ) (f : (boundary a).toFunctor.obj b),
      p.app b (β.app b f) = Q.map f.1.down.op q) :
    ∃ v : P.obj (op a), p.app _ v = q ∧ ∀ (b : AugmentedSimplexCategoryᵒᵖ)
      (f : (boundary a).toFunctor.obj b), P.map f.1.down.op v = β.app b f := by
  have sq : CommSq β (boundary a).ι p (uliftYonedaEquiv.symm q) := ⟨by
    ext b f
    exact hβ b f⟩
  refine ⟨uliftYonedaEquiv sq.lift, ?_, fun b f => ?_⟩
  · rw [← uliftYonedaEquiv_comp, sq.fac_right, Equiv.apply_symm_apply]
  · rw [uliftYonedaEquiv_naturality, uliftYonedaEquiv_comp, Quiver.Hom.unop_op,
      uliftYonedaEquiv_uliftYoneda_map]
    exact congrArg (fun g : (boundary a).toFunctor ⟶ P => g.app b f) sq.fac_left

end Boundary

section Elementwise

variable {P : AugmentedSimplexCategoryᵒᵖ ⥤ Type w} (h : ExtraDegeneracy P)

private lemma map_inr_app {y : AugmentedSimplexCategory} (x : P.obj (op y)) :
    P.map (inr 𝟘 y).op (h.h.app (op y) x) = x := by
  have := ConcreteCategory.congr_hom (h.app_comp_map_inr y) x
  simp only [types_id_apply] at this
  exact this

private lemma app_map {y y' : AugmentedSimplexCategory} (f : y ⟶ y') (x : P.obj (op y')) :
    h.h.app (op y) (P.map f.op x) = P.map (𝟘 ◁ f).op (h.h.app (op y') x) := by
  have := ConcreteCategory.congr_hom (h.map_comp_app f) x
  simp only [types_comp_apply] at this
  exact this

private lemma app_app {y : AugmentedSimplexCategory} (x : P.obj (op y)) :
    h.h.app (op (𝟘 ⊗ y)) (h.h.app (op y) x) = P.map (mu y).op (h.h.app (op y) x) := by
  exact ConcreteCategory.congr_hom (h.app_comp_app y) x

end Elementwise

section Extension

variable {P Q : AugmentedSimplexCategoryᵒᵖ ⥤ Type w} (p : P ⟶ Q) (hQ : ExtraDegeneracy Q)
  (P' : Subfunctor P) (h' : ExtraDegeneracy P'.toFunctor)

private structure Spec {y : AugmentedSimplexCategory}
    (H : ∀ b : AugmentedSimplexCategory, card b < card y → P.obj (op b) → P.obj (op (𝟘 ⊗ b)))
    (x : P.obj (op y)) (v : P.obj (op (𝟘 ⊗ y))) : Prop where
  counit : P.map (inr 𝟘 y).op v = x
  face : ∀ (b : AugmentedSimplexCategory) (f : b ⟶ y) (hb : card b < card y),
    Function.Injective (toFun f) → P.map (𝟘 ◁ f).op v = H b hb (P.map f.op x)
  degen : ∀ (c : AugmentedSimplexCategory) (σ : y ⟶ c) (hc : card c < card y)
    (z : P.obj (op c)), P.map σ.op z = x → v = P.map (𝟘 ◁ σ).op (H c hc z)
  comult : ∀ (c : AugmentedSimplexCategory) (hc : card c < card y) (z : P.obj (op c))
    (e : y = 𝟘 ⊗ c), x = P.map (eqToHom e).op (H c hc z) →
      v = P.map (eqToHom (congrArg (𝟘 ⊗ ·) e)).op (P.map (mu c).op (H c hc z))
  sub : ∀ x' : P'.toFunctor.obj (op y), x'.1 = x → v = (h'.h.app (op y) x').1
  over : p.app _ v = hQ.h.app _ (p.app _ x)

variable {p hQ P' h'}

private lemma map_whiskerLeft_eq {H : ∀ b : AugmentedSimplexCategory, P.obj (op b) →
      P.obj (op (𝟘 ⊗ b))} {b c : AugmentedSimplexCategory}
    (hb : ∀ x, Spec p hQ P' h' (fun b' _ => H b') x (H b x))
    (hc : ∀ x, Spec p hQ P' h' (fun b' _ => H b') x (H c x)) (g : b ⟶ c) (z : P.obj (op c)) :
    P.map (𝟘 ◁ g).op (H c z) = H b (P.map g.op z) := by
  obtain ⟨d, e, m, he, hm, rfl⟩ := exists_surjective_injective_factorization g
  rw [MonoidalCategory.whiskerLeft_comp, op_comp, P.map_comp_apply, op_comp, P.map_comp_apply]
  have h₁ : P.map (𝟘 ◁ m).op (H c z) = H d (P.map m.op z) := by
    rcases lt_or_eq_of_le (card_le_card_of_injective m hm) with hlt | heq
    · exact (hc z).face d m hlt hm
    · obtain rfl := card_injective heq
      rw [eq_id_of_surjective m (bijective_of_injective_of_card_le m hm le_rfl).2,
        MonoidalCategory.whiskerLeft_id, op_id, P.map_id, op_id, P.map_id]
      rfl
  rw [h₁]
  rcases lt_or_eq_of_le (card_le_card_of_surjective e he) with hlt | heq
  · exact ((hb _).degen d e hlt _ rfl).symm
  · obtain rfl := card_injective heq
    rw [eq_id_of_surjective e he, MonoidalCategory.whiskerLeft_id, op_id, P.map_id, op_id,
      P.map_id]
    rfl

variable (p) in
private lemma nonempty_obj (hp : ∀ a, HasLiftingProperty (boundary a).ι p) (hQ : ExtraDegeneracy Q)
    {y : AugmentedSimplexCategory} (x : P.obj (op y)) : Nonempty (P.obj (op (𝟘 ⊗ y))) := by
  rcases Nat.eq_zero_or_pos (card y) with hy | hy
  · have hcov : ∀ (b : AugmentedSimplexCategory) (φ : b ⟶ 𝟘 ⊗ y),
        ¬ Function.Surjective (toFun φ) → ∃ ψ : b ⟶ y, ψ ≫ inr 𝟘 y = φ := fun b φ hφ =>
      exists_comp_eq_of_injective (inr 𝟘 y) (injective_toFun_inr_zero y) φ (fun i => by
        exfalso
        refine hφ fun j => ⟨i, ?_⟩
        have h₁ := j.isLt; have h₂ := (toFun φ i).isLt; have h₃ := card_zero_tensorObj y
        exact Fin.ext (by omega))
    have := mono_of_injective (inr 𝟘 y) (injective_toFun_inr_zero y)
    obtain ⟨β, hβ⟩ := exists_boundary_hom (P := P) (a := 𝟘 ⊗ y) (I := Unit) (fun _ => y)
      (fun _ => inr 𝟘 y) (fun _ => x)
      (fun b φ hφ => ⟨(), hcov b φ hφ⟩)
      (fun _ _ b ψ ψ' h => by rw [(cancel_mono _).1 h])
    obtain ⟨v, -, -⟩ := exists_lift_of_boundary p (hp _) β (hQ.h.app _ (p.app _ x))
      (fun b f => by
        obtain ⟨ψ, hψ⟩ := hcov _ f.1.down f.2
        obtain ⟨⟨f⟩, hf⟩ := f
        subst hψ
        have h₁ := ConcreteCategory.congr_hom (hQ.app_comp_map_inr y) (p.app _ x)
        simp only [types_id_apply] at h₁
        rw [hβ () _ ψ _ hf rfl, NatTrans.naturality_apply]
        exact (congrArg (Q.map ψ.op) h₁.symm).trans (Q.map_comp_apply _ _ _).symm)
    exact ⟨v⟩
  · obtain ⟨s, -⟩ := exists_toFun_eq (x := 𝟘 ⊗ y) (y := y)
      (fun i => ⟨i.val - 1, by have h₁ := i.isLt; have h₂ := card_zero_tensorObj y; omega⟩)
      (fun i j hij => Fin.mk_le_mk.2 (Nat.sub_le_sub_right (Fin.le_iff_val_le_val.1 hij) 1))
    exact ⟨P.map s.op x⟩

private lemma card_le_of_isNondeg {y : AugmentedSimplexCategory} {x : P.obj (op y)}
    {d : AugmentedSimplexCategory}
    {ρ : y ⟶ d} {r : P.obj (op d)} (hρ : Function.Surjective (toFun ρ)) (hr : IsNondeg P r)
    (hρr : P.map ρ.op r = x) {c : AugmentedSimplexCategory} (σ : y ⟶ c) (z : P.obj (op c))
    (hz : P.map σ.op z = x) : card d ≤ card c := by
  obtain ⟨s, hs⟩ := exists_comp_eq_id_of_surjective ρ hρ
  refine hr c (s ≫ σ) z ?_
  rw [op_comp, P.map_comp_apply, hz, ← hρr, ← P.map_comp_apply, ← op_comp, hs, op_id, P.map_id,
    types_id_apply]

section Lower

variable {H : ∀ b : AugmentedSimplexCategory, P.obj (op b) → P.obj (op (𝟘 ⊗ b))}
  {y : AugmentedSimplexCategory}

private lemma map_whiskerLeft_eq_of_lt
    (ih : ∀ b, card b < card y → ∀ x, Spec p hQ P' h' (fun b' _ => H b') x (H b x))
    {b c : AugmentedSimplexCategory} (hb : card b < card y)
    (hc : card c < card y) (g : b ⟶ c) (z : P.obj (op c)) :
    P.map (𝟘 ◁ g).op (H c z) = H b (P.map g.op z) :=
  map_whiskerLeft_eq (ih b hb) (ih c hc) g z

private lemma map_whiskerLeft_eq_of_isNondeg
    (ih : ∀ b, card b < card y → ∀ x, Spec p hQ P' h' (fun b' _ => H b') x (H b x))
    {x : P.obj (op y)} {d : AugmentedSimplexCategory}
    {ρ : y ⟶ d} {r : P.obj (op d)} (hρ : Function.Surjective (toFun ρ)) (hr : IsNondeg P r)
    (hρr : P.map ρ.op r = x) {c : AugmentedSimplexCategory} (σ : y ⟶ c) (hc : card c < card y)
    (z : P.obj (op c)) (hz : P.map σ.op z = x) :
    P.map (𝟘 ◁ σ).op (H c z) = P.map (𝟘 ◁ ρ).op (H d r) := by
  obtain ⟨dz, ρz, rz, hρz, hrz, rfl⟩ := exists_isNondeg P z
  have hdz : card dz < card y := lt_of_le_of_lt (card_le_card_of_surjective ρz hρz) hc
  obtain ⟨d₂, e, m, he, hm, hem⟩ := exists_surjective_injective_factorization (σ ≫ ρz)
  have hd₂ : card d₂ < card y := lt_of_le_of_lt (card_le_card_of_injective m hm) hdz
  obtain ⟨d₃, ρ₂, r₂, hρ₂, hr₂, hr₂m⟩ := exists_isNondeg P (P.map m.op rz)
  have hd₃ : card d₃ < card y := lt_of_le_of_lt (card_le_card_of_surjective ρ₂ hρ₂) hd₂
  have hx : P.map (e ≫ ρ₂).op r₂ = x := by
    rw [op_comp, P.map_comp_apply, hr₂m, ← P.map_comp_apply, ← op_comp, hem, op_comp,
      P.map_comp_apply, hz]
  obtain ⟨rfl, hρe, rfl⟩ := eq_of_isNondeg hρ (by rw [toFun_comp]; exact hρ₂.comp he) hr hr₂
    (hρr.trans hx.symm)
  rw [eqToHom_refl, Category.comp_id] at hρe
  rw [eqToHom_refl, op_id, P.map_id, types_id_apply, hρe,
    ← map_whiskerLeft_eq_of_lt ih hc hdz, ← P.map_comp_apply, ← op_comp,
    ← MonoidalCategory.whiskerLeft_comp, ← hem, MonoidalCategory.whiskerLeft_comp, op_comp,
    P.map_comp_apply, map_whiskerLeft_eq_of_lt ih hd₂ hdz, ← hr₂m,
    ← map_whiskerLeft_eq_of_lt ih hd₂ hd₃, ← P.map_comp_apply, ← op_comp,
    ← MonoidalCategory.whiskerLeft_comp]

private lemma map_whiskerLeft_eq_map_mu
    (ih : ∀ b, card b < card y → ∀ x, Spec p hQ P' h' (fun b' _ => H b') x (H b x))
    {c : AugmentedSimplexCategory} (hy : y = 𝟘 ⊗ c)
    (z : P.obj (op c)) {c₀ : AugmentedSimplexCategory} (σ₀ : y ⟶ c₀) (hc₀ : card c₀ < card y)
    (z₀ : P.obj (op c₀)) (hz₀ : P.map σ₀.op z₀ = P.map (eqToHom hy).op (H c z)) :
    P.map (𝟘 ◁ σ₀).op (H c₀ z₀) =
      P.map (eqToHom (congrArg (𝟘 ⊗ ·) hy)).op (P.map (mu c).op (H c z)) := by
  subst hy
  rw [eqToHom_refl, op_id, P.map_id, types_id_apply] at hz₀
  rw [eqToHom_refl, op_id, P.map_id, types_id_apply]
  have hc : card c < card (𝟘 ⊗ c) := by rw [card_zero_tensorObj]; omega
  obtain ⟨d, ρ, r, hρ, hr, hρr⟩ := exists_isNondeg P (H c z)
  rw [map_whiskerLeft_eq_of_isNondeg ih hρ hr hρr σ₀ hc₀ z₀ hz₀]
  by_cases hz : IsNondeg P z
  · have hz' : P.map (inr 𝟘 c ≫ ρ).op r = z := by
      rw [op_comp, P.map_comp_apply, hρr]
      exact (ih c hc z).counit
    have hinj := injective_of_isNondeg hz (inr 𝟘 c ≫ ρ) r hz'
    have hcd := card_le_card_of_injective _ hinj
    have hdc₀ := card_le_of_isNondeg hρ hr hρr σ₀ z₀ hz₀
    obtain rfl := card_injective (show card d = card c by
      have := card_zero_tensorObj c; omega)
    have hid := eq_id_of_surjective (inr 𝟘 d ≫ ρ)
      (bijective_of_injective_of_card_le _ hinj le_rfl).2
    rw [hid, op_id, P.map_id, types_id_apply] at hz'
    subst hz'
    rw [← hρr, ← P.map_comp_apply, ← op_comp, ← P.map_comp_apply, ← op_comp,
      whiskerLeft_comp_eq_mu_comp ρ hid]
  · simp only [IsNondeg, not_forall, not_le] at hz
    obtain ⟨c'', σ', z'', hz'', hc''⟩ := hz
    have hc''y : card (𝟘 ⊗ c'') < card (𝟘 ⊗ c) := by
      rw [card_zero_tensorObj, card_zero_tensorObj]; omega
    have hx' : P.map (𝟘 ◁ σ').op (H c'' z'') = H c z := by
      rw [map_whiskerLeft_eq_of_lt ih hc (lt_trans hc'' hc), hz'']
    rw [← map_whiskerLeft_eq_of_isNondeg ih hρ hr hρr (𝟘 ◁ σ') hc''y (H c'' z'') hx']
    have hmu := (ih (𝟘 ⊗ c'') hc''y (H c'' z'')).comult c''
      (by rw [card_zero_tensorObj]; omega) z'' rfl (by rw [eqToHom_refl, op_id, P.map_id]; rfl)
    rw [eqToHom_refl, op_id, P.map_id, types_id_apply] at hmu
    rw [hmu, ← P.map_comp_apply, ← op_comp, whiskerLeft_whiskerLeft_comp_mu, op_comp,
      P.map_comp_apply, hx']

private lemma val_map {b c : AugmentedSimplexCategory} (g : b ⟶ c)
    (x' : P'.toFunctor.obj (op c)) : (P'.toFunctor.map g.op x').1 = P.map g.op x'.1 :=
  rfl

private lemma spec_of_sub
    (ih : ∀ b, card b < card y → ∀ x, Spec p hQ P' h' (fun b' _ => H b') x (H b x))
    (hh' : h'.h ≫ (decalage _).map (P'.ι ≫ p) = P'.ι ≫ p ≫ hQ.h)
    (x' : P'.toFunctor.obj (op y)) :
    Spec p hQ P' h' (fun b _ => H b) x'.1 (h'.h.app (op y) x').1 where
  counit := congrArg Subtype.val (map_inr_app h' x')
  face b f hb _ :=
    (congrArg Subtype.val (app_map h' f x')).symm.trans
      ((ih b hb _).sub (P'.toFunctor.map f.op x') rfl).symm
  degen c σ hc z hz := by
    obtain ⟨d, e, m, he, hm, rfl⟩ := exists_surjective_injective_factorization σ
    obtain ⟨s, hs⟩ := exists_comp_eq_id_of_surjective e he
    have hd : card d < card y := lt_of_le_of_lt (card_le_card_of_injective m hm) hc
    have hu : (P'.toFunctor.map s.op x').1 = P.map m.op z := by
      rw [val_map, ← hz, op_comp, P.map_comp_apply, ← P.map_comp_apply, ← op_comp, hs, op_id,
        P.map_id, types_id_apply]
    have hx' : P'.toFunctor.map e.op (P'.toFunctor.map s.op x') = x' :=
      Subtype.ext (by rw [val_map, hu, ← P.map_comp_apply, ← op_comp, hz])
    rw [MonoidalCategory.whiskerLeft_comp, op_comp, P.map_comp_apply,
      map_whiskerLeft_eq_of_lt ih hd hc, ← hu]
    exact (congrArg (fun t => (h'.h.app (op y) t).1) hx'.symm).trans
      ((congrArg Subtype.val (app_map h' e _)).trans
        (congrArg _ ((ih d hd _).sub _ rfl).symm))
  comult c hc z e hx := by
    subst e
    rw [eqToHom_refl, op_id, P.map_id, types_id_apply] at hx
    rw [eqToHom_refl, op_id, P.map_id, types_id_apply]
    have hz : (P'.toFunctor.map (inr 𝟘 c).op x').1 = z := by
      rw [val_map, hx]
      exact (ih c hc z).counit
    have h₁ := (ih c hc z).sub _ hz
    have hx' : h'.h.app (op c) (P'.toFunctor.map (inr 𝟘 c).op x') = x' :=
      Subtype.ext (hx.trans h₁).symm
    exact (congrArg (fun t => (h'.h.app (op (𝟘 ⊗ c)) t).1) hx'.symm).trans
      ((congrArg Subtype.val (app_app h' _)).trans (congrArg _ h₁.symm))
  sub x'' hx'' := by rw [Subtype.ext hx'']
  over := by
    have := ConcreteCategory.congr_hom (NatTrans.congr_app hh' (op y)) x'
    exact this

private lemma spec_of_degen
    (ih : ∀ b, card b < card y → ∀ x, Spec p hQ P' h' (fun b' _ => H b') x (H b x))
    {x : P.obj (op y)} (hx : ¬ ∃ x' : P'.toFunctor.obj (op y), x'.1 = x)
    {c₀ : AugmentedSimplexCategory} (σ₀ : y ⟶ c₀) (hc₀ : card c₀ < card y)
    (z₀ : P.obj (op c₀)) (hz₀ : P.map σ₀.op z₀ = x) :
    Spec p hQ P' h' (fun b _ => H b) x (P.map (𝟘 ◁ σ₀).op (H c₀ z₀)) where
  counit := by
    rw [← P.map_comp_apply, ← op_comp, ← id_tensorHom, inr_comp_tensorHom, op_comp,
      P.map_comp_apply, (ih c₀ hc₀ z₀).counit, hz₀]
  face b f hb _ := by
    rw [← P.map_comp_apply, ← op_comp, ← MonoidalCategory.whiskerLeft_comp,
      map_whiskerLeft_eq_of_lt ih hb hc₀, op_comp, P.map_comp_apply, hz₀]
  degen c σ hc z hz := by
    obtain ⟨d, ρ, r, hρ, hr, hρr⟩ := exists_isNondeg P x
    rw [map_whiskerLeft_eq_of_isNondeg ih hρ hr hρr σ₀ hc₀ z₀ hz₀,
      map_whiskerLeft_eq_of_isNondeg ih hρ hr hρr σ hc z hz]
  comult c _ z e hxe := map_whiskerLeft_eq_map_mu ih e z σ₀ hc₀ z₀ (hz₀.trans hxe)
  sub x' hx' := absurd ⟨x', hx'⟩ hx
  over := by
    rw [NatTrans.naturality_apply, (ih c₀ hc₀ z₀).over]
    rw [← app_map hQ, ← NatTrans.naturality_apply, hz₀]

private lemma spec_of_comult
    (ih : ∀ b, card b < card y → ∀ x, Spec p hQ P' h' (fun b' _ => H b') x (H b x))
    {c₀ : AugmentedSimplexCategory} (hy : y = 𝟘 ⊗ c₀)
    (hc₀ : card c₀ < card y) (z₀ : P.obj (op c₀))
    (hP : ¬ ∃ x' : P'.toFunctor.obj (op y), x'.1 = P.map (eqToHom hy).op (H c₀ z₀))
    (hS : ¬ ∃ (c : AugmentedSimplexCategory) (σ : y ⟶ c) (_ : card c < card y)
      (z : P.obj (op c)), P.map σ.op z = P.map (eqToHom hy).op (H c₀ z₀)) :
    Spec p hQ P' h' (fun b _ => H b) (P.map (eqToHom hy).op (H c₀ z₀))
      (P.map (eqToHom (congrArg (𝟘 ⊗ ·) hy)).op (P.map (mu c₀).op (H c₀ z₀))) := by
  subst hy
  simp only [eqToHom_refl, op_id, P.map_id, types_id_apply] at hP hS ⊢
  refine
    { counit := by
        rw [← P.map_comp_apply, ← op_comp, inr_comp_mu, op_id, P.map_id, types_id_apply]
      face := fun b f hb hf => ?_
      degen := fun c σ hc z hz => absurd ⟨c, σ, hc, z, hz⟩ hS
      comult := fun c hc z e hxe => ?_
      sub := fun x' hx' => absurd ⟨x', hx'⟩ hP
      over := by rw [NatTrans.naturality_apply, (ih c₀ hc₀ z₀).over, app_app hQ] }
  · by_cases h₀ : ∃ i, (toFun f i).val = 0
    · obtain ⟨i, hi⟩ := h₀
      have hb₀ : 0 < card b := Fin.pos i
      obtain ⟨b₂, hb₂⟩ : ∃ b₂, card b₂ = card b - 1 := ⟨ofCard _, card_ofCard _⟩
      obtain rfl : b = 𝟘 ⊗ b₂ := card_injective (by rw [card_zero_tensorObj]; omega)
      have hf₀ : (toFun f ⟨0, by rw [card_zero_tensorObj]; omega⟩).val = 0 := by
        have := Fin.le_iff_val_le_val.1 (monotone_toFun f
          (show (⟨0, by rw [card_zero_tensorObj]; omega⟩ : Fin (card (𝟘 ⊗ b₂))) ≤ i from
            Fin.le_iff_val_le_val.2 (Nat.zero_le _)))
        omega
      obtain ⟨f₂, rfl⟩ := exists_eq_whiskerLeft f hf hf₀
      have hb₂y : card b₂ < card (𝟘 ⊗ c₀) := by have := card_zero_tensorObj b₂; omega
      have hmu := (ih (𝟘 ⊗ b₂) hb (H b₂ (P.map f₂.op z₀))).comult b₂
        (by rw [card_zero_tensorObj]; omega) _ rfl
        (by rw [eqToHom_refl, op_id, P.map_id]; rfl)
      rw [eqToHom_refl, op_id, P.map_id, types_id_apply] at hmu
      rw [← P.map_comp_apply, ← op_comp, whiskerLeft_whiskerLeft_comp_mu, op_comp,
        P.map_comp_apply, map_whiskerLeft_eq_of_lt ih hb₂y hc₀, hmu]
    · simp only [not_exists] at h₀
      obtain ⟨f', rfl⟩ := exists_comp_eq_of_injective (inr 𝟘 c₀) (injective_toFun_inr_zero c₀) f
        (fun i => ⟨⟨(toFun f i).val - 1, by
          have h₁ := (toFun f i).isLt; have h₂ := card_zero_tensorObj c₀; have := h₀ i
          omega⟩, Fin.ext (by rw [val_toFun_inr_zero]; have := h₀ i; dsimp only; omega)⟩)
      rw [← P.map_comp_apply, ← op_comp, MonoidalCategory.whiskerLeft_comp, Category.assoc,
        whiskerLeft_inr_comp_mu, Category.comp_id, map_whiskerLeft_eq_of_lt ih hb hc₀, op_comp,
        P.map_comp_apply, (ih c₀ hc₀ z₀).counit]
  · obtain rfl : c₀ = c := card_injective (by
      have h₁ := congrArg card e; rw [card_zero_tensorObj, card_zero_tensorObj] at h₁; omega)
    rw [eqToHom_refl, op_id, P.map_id, types_id_apply] at hxe
    rw [eqToHom_refl, op_id, P.map_id, types_id_apply]
    have hz : z₀ = z := by rw [← (ih c₀ hc₀ z₀).counit, hxe, (ih c₀ hc₀ z).counit]
    rw [hz]

private lemma map_eq_map_of_comp_whiskerLeft_eq
    (ih : ∀ b, card b < card y → ∀ x, Spec p hQ P' h' (fun b' _ => H b') x (H b x))
    (x : P.obj (op y)) {d e : AugmentedSimplexCategory}
    (m : d ⟶ y) (hm : Function.Injective (toFun m)) (hd : card d < card y) (n : e ⟶ y)
    (hn : Function.Injective (toFun n)) (hnm : ∀ k, ∃ l, toFun m l = toFun n k)
    {b : AugmentedSimplexCategory} (ψ : b ⟶ 𝟘 ⊗ d) (κ : b ⟶ 𝟘 ⊗ e)
    (h : ψ ≫ 𝟘 ◁ m = κ ≫ 𝟘 ◁ n) :
    P.map ψ.op (H d (P.map m.op x)) = P.map κ.op (H e (P.map n.op x)) := by
  obtain ⟨ν, hν⟩ := exists_comp_eq_of_injective m hm n hnm
  have hνinj : Function.Injective (toFun ν) := fun i j hij =>
    hn (by rw [← hν, toFun_comp_apply, toFun_comp_apply, hij])
  have he : card e < card y := lt_of_le_of_lt (card_le_card_of_injective ν hνinj) hd
  have := mono_of_injective (𝟘 ◁ m) (injective_toFun_whiskerLeft_zero m hm)
  have hψ : ψ = κ ≫ 𝟘 ◁ ν := (cancel_mono (𝟘 ◁ m)).1 (by
    rw [h, Category.assoc, ← MonoidalCategory.whiskerLeft_comp, hν])
  rw [hψ, op_comp, P.map_comp_apply, map_whiskerLeft_eq_of_lt ih he hd, ← P.map_comp_apply,
    ← op_comp, hν]

private lemma exists_spec_of_filler
    (ih : ∀ b, card b < card y → ∀ x, Spec p hQ P' h' (fun b' _ => H b') x (H b x))
    (hp : ∀ a, HasLiftingProperty (boundary a).ι p)
    (x : P.obj (op y)) (hP : ¬ ∃ x' : P'.toFunctor.obj (op y), x'.1 = x)
    (hS : ¬ ∃ (c : AugmentedSimplexCategory) (σ : y ⟶ c) (_ : card c < card y)
      (z : P.obj (op c)), P.map σ.op z = x)
    (hC : ¬ ∃ (c : AugmentedSimplexCategory) (_ : card c < card y) (z : P.obj (op c))
      (e : y = 𝟘 ⊗ c), x = P.map (eqToHom e).op (H c z)) :
    ∃ v, Spec p hQ P' h' (fun b _ => H b) x v := by
  classical
  let I := Option {q : Σ d : AugmentedSimplexCategory, d ⟶ y //
    Function.Injective (toFun q.2) ∧ card q.1 < card y}
  let dom : I → AugmentedSimplexCategory := fun i => Option.elim i y (fun q => 𝟘 ⊗ q.1.1)
  let ι : ∀ i, dom i ⟶ 𝟘 ⊗ y := fun i => match i with
    | none => inr 𝟘 y
    | some q => 𝟘 ◁ q.1.2
  let w : ∀ i, P.obj (op (dom i)) := fun i => match i with
    | none => x
    | some q => H q.1.1 (P.map q.1.2.op x)
  have hinr := mono_of_injective (inr 𝟘 y) (injective_toFun_inr_zero y)
  have hcover : ∀ (b : AugmentedSimplexCategory) (φ : b ⟶ 𝟘 ⊗ y),
      ¬ Function.Surjective (toFun φ) → ∃ (i : I) (ψ : b ⟶ dom i), ψ ≫ ι i = φ := by
    intro b φ hφ
    by_cases h₀ : ∃ i, (toFun φ i).val = 0
    · obtain ⟨d, m, hm, hmS⟩ := exists_injective_range
        (Finset.univ.filter fun j : Fin (card y) => ∃ i, (toFun φ i).val = j.val + 1)
      have hd : card d < card y := by
        rcases lt_or_eq_of_le (card_le_card_of_injective m hm) with h | h
        · exact h
        · exfalso
          refine hφ fun k => ?_
          by_cases hk : k.val = 0
          · obtain ⟨i, hi⟩ := h₀
            exact ⟨i, Fin.ext (hi.trans hk.symm)⟩
          · obtain ⟨l, hl⟩ := (bijective_of_injective_of_card_le m hm h.ge).2
              ⟨k.val - 1, by have h₁ := k.isLt; have h₂ := card_zero_tensorObj y; omega⟩
            obtain ⟨i, hi⟩ := (Finset.mem_filter.1 ((hmS _).2 ⟨l, hl⟩)).2
            exact ⟨i, Fin.ext (by rw [hi]; dsimp only; omega)⟩
      obtain ⟨ψ, hψ⟩ := exists_comp_whiskerLeft_eq φ m hm (fun i hi => by
        obtain ⟨l, hl⟩ := (hmS ⟨(toFun φ i).val - 1, by
          have h₁ := (toFun φ i).isLt; have h₂ := card_zero_tensorObj y; omega⟩).1
          (Finset.mem_filter.2 ⟨Finset.mem_univ _, i, by dsimp only; omega⟩)
        exact ⟨l, by rw [hl]; dsimp only; omega⟩)
      exact ⟨some ⟨⟨d, m⟩, hm, hd⟩, ψ, hψ⟩
    · simp only [not_exists] at h₀
      obtain ⟨ψ, hψ⟩ := exists_comp_inr_eq φ h₀
      exact ⟨none, ψ, hψ⟩
  have hns : ∀ {d : AugmentedSimplexCategory} (m : d ⟶ y) (_ : card d < card y)
      {b : AugmentedSimplexCategory} (ψ : b ⟶ y) (ψ' : b ⟶ 𝟘 ⊗ d),
      ψ ≫ inr 𝟘 y = ψ' ≫ 𝟘 ◁ m → P.map ψ.op x = P.map ψ'.op (H d (P.map m.op x)) := by
    intro d m hd b ψ ψ' h
    obtain ⟨ψ'', rfl⟩ := exists_comp_inr_eq ψ' (fun i hi => by
      have := congrArg (fun f => (toFun f i).val) h
      simp only [toFun_comp_apply, val_toFun_inr_zero] at this
      rw [val_toFun_whiskerLeft_of_eq_zero _ _ hi] at this
      omega)
    have hψ : ψ = ψ'' ≫ m := (cancel_mono (inr 𝟘 y)).1 (by
      rw [h, Category.assoc, Category.assoc, ← id_tensorHom, inr_comp_tensorHom])
    rw [hψ, op_comp, P.map_comp_apply, op_comp, P.map_comp_apply, (ih d hd _).counit]
  have hss : ∀ {d d' : AugmentedSimplexCategory} (m : d ⟶ y) (_ : Function.Injective (toFun m))
      (_ : card d < card y) (m' : d' ⟶ y) (_ : Function.Injective (toFun m'))
      (_ : card d' < card y) {b : AugmentedSimplexCategory} (ψ : b ⟶ 𝟘 ⊗ d)
      (ψ' : b ⟶ 𝟘 ⊗ d'), ψ ≫ 𝟘 ◁ m = ψ' ≫ 𝟘 ◁ m' →
      P.map ψ.op (H d (P.map m.op x)) = P.map ψ'.op (H d' (P.map m'.op x)) := by
    intro d d' m hm hd m' hm' hd' b ψ ψ' h
    obtain ⟨e, n, hn, hnS⟩ := exists_injective_range
      (Finset.univ.filter fun j : Fin (card y) => ∃ i, (toFun (ψ ≫ 𝟘 ◁ m) i).val = j.val + 1)
    have hrange : ∀ {d'' : AugmentedSimplexCategory} (m'' : d'' ⟶ y)
        (ψ'' : b ⟶ 𝟘 ⊗ d''), ψ ≫ 𝟘 ◁ m = ψ'' ≫ 𝟘 ◁ m'' → ∀ k, ∃ l, toFun m'' l = toFun n k := by
      intro d'' m'' ψ'' h'' k
      obtain ⟨i, hi⟩ := (Finset.mem_filter.1 ((hnS _).2 ⟨k, rfl⟩)).2
      rw [h''] at hi
      obtain ⟨l, hl⟩ := exists_val_toFun_eq_of_comp_whiskerLeft ψ'' m'' i (by omega)
      exact ⟨l, Fin.ext (by omega)⟩
    obtain ⟨κ, hκ⟩ := exists_comp_whiskerLeft_eq (ψ ≫ 𝟘 ◁ m) n hn (fun i hi => by
      obtain ⟨l, hl⟩ := (hnS ⟨(toFun (ψ ≫ 𝟘 ◁ m) i).val - 1, by
        have h₁ := (toFun (ψ ≫ 𝟘 ◁ m) i).isLt; have h₂ := card_zero_tensorObj y; omega⟩).1
        (Finset.mem_filter.2 ⟨Finset.mem_univ _, i, by dsimp only; omega⟩)
      exact ⟨l, by rw [hl]; dsimp only; omega⟩)
    rw [map_eq_map_of_comp_whiskerLeft_eq ih x m hm hd n hn (hrange m ψ rfl) ψ κ hκ.symm,
      map_eq_map_of_comp_whiskerLeft_eq ih x m' hm' hd' n hn (hrange m' ψ' h) ψ' κ
        (hκ.trans h).symm]
  have hcompat : ∀ (i j : I) (b : AugmentedSimplexCategory) (ψ : b ⟶ dom i) (ψ' : b ⟶ dom j),
      ψ ≫ ι i = ψ' ≫ ι j → P.map ψ.op (w i) = P.map ψ'.op (w j) := by
    rintro (_ | ⟨⟨d, m⟩, hm, hd⟩) (_ | ⟨⟨d', m'⟩, hm', hd'⟩) b ψ ψ' h
    · rw [(cancel_mono (inr 𝟘 y)).1 h]
    · exact hns m' hd' ψ ψ' h
    · exact (hns m hd ψ' ψ h.symm).symm
    · exact hss m hm hd m' hm' hd' ψ ψ' h
  obtain ⟨β, hβ⟩ := exists_boundary_hom dom ι w hcover hcompat
  obtain ⟨v, hv₁, hv₂⟩ := exists_lift_of_boundary p (hp _) β (hQ.h.app _ (p.app _ x))
    (fun b f => by
      obtain ⟨i, ψ, hψ⟩ := hcover _ f.1.down f.2
      obtain ⟨⟨f⟩, hf⟩ := f
      rw [hβ i _ ψ f hf hψ, NatTrans.naturality_apply, ← hψ, op_comp]
      refine (congrArg (Q.map ψ.op) ?_).trans (Q.map_comp_apply _ _ _).symm
      rcases i with _ | ⟨⟨d, m⟩, hm, hd⟩
      · exact (map_inr_app hQ _).symm
      · exact ((ih d hd _).over.trans (congrArg _ (NatTrans.naturality_apply p _ x))).trans
          (app_map hQ m _))
  have hface : ∀ (b : AugmentedSimplexCategory) (f : b ⟶ 𝟘 ⊗ y), card b < card (𝟘 ⊗ y) →
      ULift.up f ∈ (boundary.{w} (𝟘 ⊗ y)).obj (op b) := fun b f hb hf =>
    absurd (card_le_card_of_surjective f hf) (not_le.2 hb)
  refine ⟨v,
    { counit := ?_
      face := ?_
      degen := fun c σ hc z hz => absurd ⟨c, σ, hc, z, hz⟩ hS
      comult := fun c hc z e hxe => absurd ⟨c, hc, z, e, hxe⟩ hC
      sub := fun x' hx' => absurd ⟨x', hx'⟩ hP
      over := hv₁ }⟩
  · have hnot : ULift.up (inr 𝟘 y) ∈ (boundary.{w} (𝟘 ⊗ y)).obj (op y) := fun hs => by
      obtain ⟨i, hi⟩ := hs ⟨0, by rw [card_zero_tensorObj]; omega⟩
      have := val_toFun_inr_zero y i
      rw [hi] at this
      dsimp only at this
      omega
    rw [hv₂ (op y) ⟨⟨inr 𝟘 y⟩, hnot⟩, hβ none y (𝟙 y) _ hnot (Category.id_comp _)]
    exact ConcreteCategory.congr_hom (P.map_id (op y)) x
  · intro b f hb hf
    have hb' : card (𝟘 ⊗ b) < card (𝟘 ⊗ y) := by
      rw [card_zero_tensorObj, card_zero_tensorObj]; omega
    rw [hv₂ (op (𝟘 ⊗ b)) ⟨⟨𝟘 ◁ f⟩, hface _ _ hb'⟩]
    exact (hβ (some ⟨⟨b, f⟩, hf, hb⟩) (𝟘 ⊗ b) (𝟙 _) (𝟘 ◁ f) (hface _ _ hb')
      (Category.id_comp _)).trans (ConcreteCategory.congr_hom (P.map_id (op (𝟘 ⊗ b))) _)

end Lower

variable (p hQ P' h') in
private noncomputable def ext (hp : ∀ a, HasLiftingProperty (boundary a).ι p) :
    ∀ y : AugmentedSimplexCategory, P.obj (op y) → P.obj (op (𝟘 ⊗ y)) :=
  (measure card).wf.fix fun _ H x =>
    @Classical.epsilon _ (nonempty_obj p hp hQ x) (Spec p hQ P' h' H x)

private lemma exists_spec (hp : ∀ a, HasLiftingProperty (boundary a).ι p)
    (hh' : h'.h ≫ (decalage _).map (P'.ι ≫ p) = P'.ι ≫ p ≫ hQ.h)
    {H : ∀ b : AugmentedSimplexCategory, P.obj (op b) → P.obj (op (𝟘 ⊗ b))}
    {y : AugmentedSimplexCategory}
    (ih : ∀ b, card b < card y → ∀ x, Spec p hQ P' h' (fun b' _ => H b') x (H b x))
    (x : P.obj (op y)) : ∃ v, Spec p hQ P' h' (fun b _ => H b) x v := by
  by_cases hP : ∃ x' : P'.toFunctor.obj (op y), x'.1 = x
  · obtain ⟨x', rfl⟩ := hP
    exact ⟨_, spec_of_sub ih hh' x'⟩
  by_cases hS : ∃ (c : AugmentedSimplexCategory) (σ : y ⟶ c) (_ : card c < card y)
      (z : P.obj (op c)), P.map σ.op z = x
  · obtain ⟨c, σ, hc, z, hz⟩ := hS
    exact ⟨_, spec_of_degen ih hP σ hc z hz⟩
  by_cases hC : ∃ (c : AugmentedSimplexCategory) (_ : card c < card y) (z : P.obj (op c))
      (e : y = 𝟘 ⊗ c), x = P.map (eqToHom e).op (H c z)
  · obtain ⟨c, hc, z, e, rfl⟩ := hC
    exact ⟨_, spec_of_comult ih e hc z hP hS⟩
  exact exists_spec_of_filler ih hp x hP hS hC

private lemma spec_ext (hp : ∀ a, HasLiftingProperty (boundary a).ι p)
    (hh' : h'.h ≫ (decalage _).map (P'.ι ≫ p) = P'.ι ≫ p ≫ hQ.h) (y : AugmentedSimplexCategory)
    (x : P.obj (op y)) :
    Spec p hQ P' h' (fun b _ => ext p hQ P' h' hp b) x (ext p hQ P' h' hp y x) := by
  suffices H : ∀ (n : ℕ) (y : AugmentedSimplexCategory), card y = n → ∀ x : P.obj (op y),
      Spec p hQ P' h' (fun b _ => ext p hQ P' h' hp b) x (ext p hQ P' h' hp y x) from
    H _ y rfl x
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro y hy x
    have hfix : ext p hQ P' h' hp y x = @Classical.epsilon _ (nonempty_obj p hp hQ x)
        (Spec p hQ P' h' (fun b _ => ext p hQ P' h' hp b) x) := by
      rw [ext, WellFounded.fix_eq]
      rfl
    rw [hfix]
    exact Classical.epsilon_spec (exists_spec hp hh' (fun b hb => ih _ (hy ▸ hb) b rfl) x)

theorem ExtraDegeneracy.exists_extension (p : P ⟶ Q)
    (hp : ∀ a, HasLiftingProperty (boundary a).ι p) (hQ : ExtraDegeneracy Q)
    (P' : Subfunctor P) (h' : ExtraDegeneracy P'.toFunctor)
    (hh' : h'.h ≫ (decalage _).map (P'.ι ≫ p) = P'.ι ≫ p ≫ hQ.h) :
    ∃ h : ExtraDegeneracy P,
      P'.ι ≫ h.h = h'.h ≫ (decalage _).map P'.ι ∧ h.h ≫ (decalage _).map p = p ≫ hQ.h := by
  have hs := spec_ext hp hh'
  let H := ext p hQ P' h' hp
  have hnat : ∀ {b c : AugmentedSimplexCategory} (g : b ⟶ c) (z : P.obj (op c)),
      P.map (𝟘 ◁ g).op (H c z) = H b (P.map g.op z) := fun g z =>
    map_whiskerLeft_eq (hs _) (hs _) g z
  let h : P ⟶ (decalage _).obj P :=
    { app y := ↾H y.unop
      naturality y y' g := by
        ext z
        exact (hnat g.unop z).symm }
  refine ⟨⟨h, ?_, ?_⟩, ?_, ?_⟩
  · ext y x
    exact (hs y.unop x).counit
  · ext y x
    have := (hs (𝟘 ⊗ y.unop) (H y.unop x)).comult y.unop
      (by rw [card_zero_tensorObj]; omega) x rfl (by rw [eqToHom_refl, op_id, P.map_id]; rfl)
    rw [eqToHom_refl, op_id, P.map_id] at this
    exact this.symm
  · ext y x
    exact (hs y.unop x.1).sub x rfl
  · ext y x
    exact (hs y.unop x).over

end Extension

end AugmentedSimplexCategory
