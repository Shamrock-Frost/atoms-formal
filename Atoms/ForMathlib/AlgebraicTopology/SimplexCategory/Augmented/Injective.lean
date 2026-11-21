import Atoms.ForMathlib.AlgebraicTopology.SimplexCategory.Augmented.Monoidal

open CategoryTheory

namespace AugmentedSimplexCategory

theorem eq_id_of_injective {c : AugmentedSimplexCategory} (θ : c ⟶ c)
    (hθ : Function.Injective (toFun θ)) : θ = 𝟙 c := by
  have hid : Function.Injective (toFun (𝟙 c)) := fun i j h => by
    rwa [toFun_id, toFun_id] at h
  refine toFun_injective ((((monotone_toFun θ).strictMono_of_injective hθ).range_inj
    ((monotone_toFun (𝟙 c)).strictMono_of_injective hid)).1 ?_)
  rw [(Finite.injective_iff_surjective.1 hθ).range_eq]
  exact (Set.eq_univ_of_forall fun i => Set.mem_range.2 ⟨i, toFun_id c i⟩).symm

theorem val_toFun_of_injective_of_card_eq {c d : AugmentedSimplexCategory} (θ : c ⟶ d)
    (hθ : Function.Injective (toFun θ)) (h : card c = card d) (i : Fin (card c)) :
    (toFun θ i).val = i.val := by
  obtain rfl := card_injective h
  rw [eq_id_of_injective θ hθ, toFun_id]

theorem injective_toFun_of_isIso {c d : AugmentedSimplexCategory} (θ : c ⟶ d) [IsIso θ] :
    Function.Injective (toFun θ) := fun i j h => by
  have h' := congrArg (toFun (inv θ)) h
  rwa [← toFun_comp_apply, ← toFun_comp_apply, IsIso.hom_inv_id, toFun_id, toFun_id] at h'

theorem surjective_toFun_of_isIso {c d : AugmentedSimplexCategory} (θ : c ⟶ d) [IsIso θ] :
    Function.Surjective (toFun θ) := fun j =>
  ⟨toFun (inv θ) j, by rw [← toFun_comp_apply, IsIso.inv_hom_id, toFun_id]⟩

theorem not_injective_toFun_of_card_lt {c d : AugmentedSimplexCategory} (θ : c ⟶ d)
    (h : card d < card c) : ¬ Function.Injective (toFun θ) := fun hθ => by
  have := Fintype.card_le_of_injective _ hθ
  simp only [Fintype.card_fin] at this
  omega

theorem exists_comp_eq_id_of_surjective {c d : AugmentedSimplexCategory} (π : c ⟶ d)
    (hπ : Function.Surjective (toFun π)) : ∃ ι : d ⟶ c, ι ≫ π = 𝟙 d := by
  classical
  let s : Fin (card d) → Fin (card c) := fun j =>
    (Finset.univ.filter fun i => toFun π i = j).min' (by
      obtain ⟨i, hi⟩ := hπ j
      exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩)
  have hs : ∀ j, toFun π (s j) = j := fun j => by
    have h := Finset.min'_mem (Finset.univ.filter fun i => toFun π i = j) (by
      obtain ⟨i, hi⟩ := hπ j
      exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩)
    exact (Finset.mem_filter.1 h).2
  obtain ⟨ι, hι⟩ := exists_toFun_eq s fun j j' hjj' => by
    by_contra hlt
    rw [not_le] at hlt
    have h₁ := monotone_toFun π hlt.le
    rw [hs, hs] at h₁
    obtain rfl := le_antisymm hjj' h₁
    exact lt_irrefl _ hlt
  refine ⟨ι, toFun_injective (funext fun j => ?_)⟩
  rw [toFun_comp_apply, hι, hs, toFun_id]

theorem exists_injective_image_eq (a : AugmentedSimplexCategory)
    (τ : Finset (Fin (card a))) :
    ∃ (d : AugmentedSimplexCategory) (ε : d ⟶ a), Function.Injective (toFun ε) ∧
      Finset.univ.image (toFun ε) = τ := by
  obtain ⟨d, hd⟩ := exists_card_eq τ.card
  obtain ⟨ε, hε⟩ := exists_toFun_eq (x := d) (y := a) (τ.orderEmbOfFin hd.symm)
    (τ.orderEmbOfFin hd.symm).monotone
  refine ⟨d, ε, hε ▸ (τ.orderEmbOfFin hd.symm).injective, ?_⟩
  rw [hε, ← Finset.coe_inj, Finset.coe_image, Finset.coe_univ, Set.image_univ,
    Finset.range_orderEmbOfFin]

theorem exists_comp_eq_injective {c a : AugmentedSimplexCategory} (ι : c ⟶ a) :
    ∃ (d : AugmentedSimplexCategory) (π : c ⟶ d) (ε : d ⟶ a), π ≫ ε = ι ∧
      Function.Injective (toFun ε) ∧
      Finset.univ.image (toFun ε) = Finset.univ.image (toFun ι) := by
  obtain ⟨d, ε, hε, him⟩ := exists_injective_image_eq a (Finset.univ.image (toFun ι))
  have hmem : ∀ i, ∃ j, toFun ε j = toFun ι i := fun i => by
    have : toFun ι i ∈ Finset.univ.image (toFun ε) := by
      rw [him]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
    obtain ⟨j, -, hj⟩ := Finset.mem_image.1 this
    exact ⟨j, hj⟩
  have hsm : StrictMono (toFun ε) := (monotone_toFun ε).strictMono_of_injective hε
  choose π hπ using hmem
  obtain ⟨π', hπ'⟩ := exists_toFun_eq (x := c) (y := d) π fun i i' hii' =>
    hsm.le_iff_le.1 ((hπ i).trans_le ((monotone_toFun ι hii').trans_eq (hπ i').symm))
  refine ⟨d, π', ε, toFun_injective (funext fun i => ?_), hε, him⟩
  rw [toFun_comp_apply, hπ', hπ]

theorem eq_of_injective_of_image_eq {d d' a : AugmentedSimplexCategory} (ε : d ⟶ a)
    (ε' : d' ⟶ a) (hε : Function.Injective (toFun ε)) (hε' : Function.Injective (toFun ε'))
    (h : Finset.univ.image (toFun ε) = Finset.univ.image (toFun ε')) :
    ∃ e : d = d', ε = eqToHom e ≫ ε' := by
  have hc : card d = card d' := by
    have h₁ := Finset.card_image_of_injective Finset.univ hε
    have h₂ := Finset.card_image_of_injective Finset.univ hε'
    rw [h, h₂, Finset.card_univ, Finset.card_univ, Fintype.card_fin, Fintype.card_fin] at h₁
    exact h₁.symm
  obtain rfl := card_injective hc
  refine ⟨rfl, ?_⟩
  rw [eqToHom_refl, Category.id_comp]
  refine toFun_injective ((((monotone_toFun ε).strictMono_of_injective hε).range_inj
    ((monotone_toFun ε').strictMono_of_injective hε')).1 ?_)
  rw [← Set.image_univ, ← Set.image_univ, ← Finset.coe_univ, ← Finset.coe_image,
    ← Finset.coe_image, h]

end AugmentedSimplexCategory
