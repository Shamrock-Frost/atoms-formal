import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.CartesianEdge

open CategoryTheory Limits Simplicial HomotopicalAlgebra MorphismProperty MonoidalCategory

universe u

namespace SSet

section Attach

variable {Y Z : SSet.{u}} (ι : Y ⟶ Z) {A : Z.Subcomplex} {C : Y.Subcomplex}

private noncomputable def restrictMap (hA : A.preimage ι = C) : (C : SSet.{u}) ⟶ (A : SSet.{u}) :=
  Subcomplex.lift (C.ι ≫ ι) (by
    rw [Subcomplex.range_comp, Subcomplex.image_le_iff, hA]
    rintro k _ ⟨y, rfl⟩
    exact y.2)

@[reassoc]
private lemma restrictMap_ι (hA : A.preimage ι = C) : restrictMap ι hA ≫ A.ι = C.ι ≫ ι :=
  Subcomplex.lift_ι _ _

private lemma isPushout_restrictMap [Mono ι] (hA : A.preimage ι = C) :
    IsPushout (restrictMap ι hA) C.ι (Subcomplex.homOfLE le_sup_left)
      (Subcomplex.lift ι (le_sup_right : Subcomplex.range ι ≤ A ⊔ Subcomplex.range ι)) :=
  IsPushout.of_forall_isPushout_app fun k ↦ by
    have hm : Mono (ι.app k) := (NatTrans.mono_iff_mono_app _).1 inferInstance k
    have hmA : Mono (A.ι.app k) := (NatTrans.mono_iff_mono_app _).1 inferInstance k
    have hmS : Mono ((A ⊔ Subcomplex.range ι).ι.app k) :=
      (NatTrans.mono_iff_mono_app _).1 inferInstance k
    refine Types.isPushout_of_isPullback_of_mono (k := (A ⊔ Subcomplex.range ι).ι.app k)
      (r' := A.ι.app k) (b' := ι.app k) ?_ rfl rfl ?_
      (fun x y _ _ h ↦ (mono_iff_injective _).1 hm h)
    · refine (Types.isPullback_iff _ _ _ _).2 ⟨congr_app (restrictMap_ι ι hA) k,
        fun x y h ↦ Subtype.ext h.2, fun x₂ x₃ h ↦ ?_⟩
      have hx : x₃ ∈ C.obj k := by
        rw [← hA]
        exact (congrArg (· ∈ A.obj k) h).mp x₂.2
      exact ⟨⟨x₃, hx⟩, Subtype.ext h.symm, rfl⟩
    · refine Set.eq_univ_of_forall fun x ↦ ?_
      obtain hx | ⟨y, hy⟩ := x.2
      · exact Or.inl ⟨⟨x.1, hx⟩, rfl⟩
      · exact Or.inr ⟨y, Subtype.ext hy⟩

private lemma exists_extension [Mono ι] (hA : A.preimage ι = C) {E B : SSet.{u}} {q : E ⟶ B}
    (a : (A : SSet.{u}) ⟶ E) (b : Z ⟶ B)
    (w : a ≫ q = A.ι ≫ b) (l : Y ⟶ E) (hl₁ : C.ι ≫ l = restrictMap ι hA ≫ a)
    (hl₂ : l ≫ q = ι ≫ b) :
    ∃ a' : ((A ⊔ Subcomplex.range ι : Z.Subcomplex) : SSet.{u}) ⟶ E,
      Subcomplex.homOfLE le_sup_left ≫ a' = a ∧ a' ≫ q = (A ⊔ Subcomplex.range ι).ι ≫ b := by
  have h := isPushout_restrictMap ι hA
  refine ⟨h.desc a l hl₁.symm, h.inl_desc _ _ _, h.hom_ext ?_ ?_⟩
  · rw [h.inl_desc_assoc, w]
    rfl
  · rw [h.inr_desc_assoc, hl₂, Subcomplex.lift_ι_assoc]

end Attach

section Walk

variable {m : ℕ}

private def walkFun (k : Fin (m + 1)) (w : Fin (m + 2)) : Fin 2 × Fin (m + 1) :=
  (⟨if w.val ≤ k.val then 0 else 1, by split_ifs <;> omega⟩,
    ⟨if w.val ≤ k.val then w.val else w.val - 1, by split_ifs <;> omega⟩)

private lemma walkFun_fst (k : Fin (m + 1)) (w : Fin (m + 2)) :
    ((walkFun k w).1 : ℕ) = if w.val ≤ k.val then 0 else 1 := rfl

private lemma walkFun_snd (k : Fin (m + 1)) (w : Fin (m + 2)) :
    ((walkFun k w).2 : ℕ) = if w.val ≤ k.val then w.val else w.val - 1 := rfl

private def walk (k : Fin (m + 1)) : Fin (m + 2) →o Fin 2 × Fin (m + 1) where
  toFun := walkFun k
  monotone' v w h := by
    have h' : v.val ≤ w.val := h
    refine Prod.mk_le_mk.2 ⟨?_, ?_⟩ <;> rw [Fin.le_iff_val_le_val] <;> dsimp only <;>
      split_ifs <;> omega

private def prismSimplex (k : Fin (m + 1)) : (Δ[1] ⊗ Δ[m] : SSet.{u}) _⦋m + 1⦌ :=
  prodStdSimplex.objEquiv.symm (walk k)

private lemma prismSimplex_mem_nonDegenerate (k : Fin (m + 1)) :
    prismSimplex.{u} k ∈ (Δ[1] ⊗ Δ[m] : SSet.{u}).nonDegenerate _ := by
  rw [prodStdSimplex.nonDegenerate_iff_injective_objEquiv, prismSimplex, Equiv.apply_symm_apply]
  intro v w h
  have h₁ : ((walkFun k v).1 : ℕ) = (walkFun k w).1 := congrArg (fun x ↦ (x.1 : ℕ)) h
  have h₂ : ((walkFun k v).2 : ℕ) = (walkFun k w).2 := congrArg (fun x ↦ (x.2 : ℕ)) h
  rw [walkFun_fst, walkFun_fst] at h₁
  rw [walkFun_snd, walkFun_snd] at h₂
  ext
  split_ifs at h₁ h₂ <;> omega

private instance (p q : ℕ) : (Δ[p] ⊗ Δ[q] : SSet.{u}).Nonsingular :=
  Nonsingular.of_mono (prodStdSimplex.isoNerve p q).hom

private noncomputable def prismMap (k : Fin (m + 1)) : Δ[m + 1] ⟶ (Δ[1] ⊗ Δ[m] : SSet.{u}) :=
  yonedaEquiv.symm (prismSimplex k)

private instance (k : Fin (m + 1)) : Mono (prismMap.{u} k) :=
  Nonsingular.mono' _ (prismSimplex_mem_nonDegenerate k)

private noncomputable def prismFiltration (m k : ℕ) : (Δ[1] ⊗ Δ[m] : SSet.{u}).Subcomplex :=
  (Λ[1, 1] : (Δ[1] : SSet.{u}).Subcomplex).unionProd ∂Δ[m] ⊔
    ⨆ (j : Fin (m + 1)) (_ : j.val < k), Subcomplex.range (prismMap.{u} j)

private lemma mem_prismFiltration_iff (k : ℕ) {d : ℕ} (x : (Δ[1] ⊗ Δ[m] : SSet.{u}) _⦋d⦌) :
    x ∈ (prismFiltration.{u} m k).obj _ ↔ ((∃ v, ∀ t, x.2 t ≠ v) ∨ ∀ t, x.1 t = 1) ∨
      ∃ j : Fin (m + 1), j.val < k ∧ ∃ y, (prismMap.{u} j).app _ y = x := by
  have h1 (s : (Δ[1] : SSet.{u}) _⦋d⦌) : s ∈ (Λ[1, 1] : (Δ[1] : SSet.{u}).Subcomplex).obj _ ↔
      ∀ t, s t = 1 := by
    rw [mem_horn_iff_notMem_range]
    refine ⟨fun ⟨j, hj, hj'⟩ t ↦ ?_, fun h ↦ ⟨0, by decide, fun ⟨t, ht⟩ ↦ ?_⟩⟩
    · obtain rfl : j = 0 := by
        fin_cases j
        · rfl
        · exact absurd rfl hj
      exact Fin.eq_one_of_ne_zero _ fun h ↦ hj' ⟨t, h⟩
    · rw [h t] at ht
      exact absurd ht (by decide)
  simp only [prismFiltration, Subfunctor.max_obj, Subfunctor.iSup_obj, Set.mem_union,
    Set.mem_iUnion, Subfunctor.range_obj, Set.mem_range, exists_prop]
  refine or_congr_left ((Subcomplex.mem_unionProd_iff _ _ x).trans (or_congr ?_ (h1 _)))
  rw [mem_boundary_iff_notMem_range]
  simp only [Set.mem_range, not_exists]

private lemma prismMap_app_fst {d : ℕ} (k : Fin (m + 1)) (y : (Δ[m + 1] : SSet.{u}) _⦋d⦌)
    (t : Fin (d + 1)) : (((prismMap.{u} k).app _ y).1 t : ℕ) = if (y t).val ≤ k.val then 0 else 1 :=
  rfl

private lemma prismMap_app_snd {d : ℕ} (k : Fin (m + 1)) (y : (Δ[m + 1] : SSet.{u}) _⦋d⦌)
    (t : Fin (d + 1)) : (((prismMap.{u} k).app _ y).2 t : ℕ) =
      if (y t).val ≤ k.val then (y t).val else (y t).val - 1 :=
  rfl

private lemma preimage_prismFiltration (k : Fin (m + 1)) :
    (prismFiltration.{u} m k.val).preimage (prismMap k) = Λ[m + 1, k.succ] := by
  ext ⟨⟨d⟩⟩ y
  rw [Subcomplex.preimage_obj, Set.mem_preimage, mem_prismFiltration_iff, mem_horn_iff_notMem_range]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have hc' (v : ℕ) (hv : v < m + 2) (hk : v ≠ k.val + 1) : ∃ t, (y t).val = v := by
      obtain ⟨t, ht⟩ := hc ⟨v, hv⟩ (fun h ↦ hk (congrArg Fin.val h))
      exact ⟨t, congrArg Fin.val ht⟩
    rcases h with (⟨v, hv⟩ | h) | ⟨j, hj, z, hz⟩
    · by_cases hvk : v.val ≤ k.val
      · obtain ⟨t, ht⟩ := hc' v.val (by omega) (by omega)
        refine hv t (Fin.ext ?_)
        rw [prismMap_app_snd]
        split_ifs <;> omega
      · obtain ⟨t, ht⟩ := hc' (v.val + 1) (by omega) (by omega)
        refine hv t (Fin.ext ?_)
        rw [prismMap_app_snd]
        split_ifs <;> omega
    · obtain ⟨t, ht⟩ := hc' 0 (by omega) (by omega)
      have h₁ := congrArg Fin.val (h t)
      rw [prismMap_app_fst] at h₁
      split_ifs at h₁ <;> first | omega | exact absurd h₁ (by decide)
    · obtain ⟨t, ht⟩ := hc' k.val (by omega) (by omega)
      have h₁ := prismMap_app_fst j z t
      have h₂ := prismMap_app_snd j z t
      rw [hz, prismMap_app_fst] at h₁
      rw [hz, prismMap_app_snd] at h₂
      have : j.val < k.val := hj
      split_ifs at h₁ h₂ <;> omega
  · rintro ⟨v, hv, hvy⟩
    have hv' : v.val ≠ k.val + 1 := fun h ↦ hv (Fin.ext h)
    have hvy' (t) : (y t).val ≠ v.val := fun h ↦ hvy ⟨t, Fin.ext h⟩
    by_cases h₁ : v.val < k.val
    · refine Or.inl (Or.inl ⟨⟨v.val, by omega⟩, fun t h ↦ hvy' t ?_⟩)
      have h₂ := congrArg Fin.val h
      rw [prismMap_app_snd] at h₂
      dsimp only at h₂
      split_ifs at h₂ <;> omega
    by_cases h₂ : k.val + 1 < v.val
    · refine Or.inl (Or.inl ⟨⟨v.val - 1, by omega⟩, fun t h ↦ hvy' t ?_⟩)
      have h₃ := congrArg Fin.val h
      rw [prismMap_app_snd] at h₃
      dsimp only at h₃
      split_ifs at h₃ <;> omega
    obtain hk | hk := Nat.eq_zero_or_pos k.val
    · refine Or.inl (Or.inr fun t ↦ Fin.ext ?_)
      rw [prismMap_app_fst]
      have := hvy' t
      split_ifs <;> first | rfl | omega
    · refine Or.inr ⟨⟨k.val - 1, by omega⟩, by dsimp only; omega, y,
        prodStdSimplex.objEquiv.injective (OrderHom.ext _ _ (funext fun t ↦ ?_))⟩
      have := hvy' t
      refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
      · refine (prismMap_app_fst _ y t).trans (Eq.trans ?_ (prismMap_app_fst k y t).symm)
        dsimp only
        split_ifs <;> omega
      · refine (prismMap_app_snd _ y t).trans (Eq.trans ?_ (prismMap_app_snd k y t).symm)
        dsimp only
        split_ifs <;> omega

private lemma prismFiltration_zero : prismFiltration.{u} m 0 =
    (Λ[1, 1] : (Δ[1] : SSet.{u}).Subcomplex).unionProd ∂Δ[m] :=
  le_antisymm (sup_le le_rfl (iSup₂_le fun _ h ↦ absurd h (Nat.not_lt_zero _))) le_sup_left

private lemma prismFiltration_succ (k : ℕ) (hk : k < m + 1) : prismFiltration.{u} m (k + 1) =
    prismFiltration m k ⊔ Subcomplex.range (prismMap ⟨k, hk⟩) := by
  let R (j : Fin (m + 1)) := Subcomplex.range (prismMap.{u} j)
  refine le_antisymm (sup_le (le_sup_left.trans le_sup_left) (iSup₂_le fun j hj ↦ ?_))
    (sup_le (sup_le le_sup_left (iSup₂_le fun j hj ↦ ?_)) ?_)
  · obtain hj | hj := Nat.lt_succ_iff_lt_or_eq.1 hj
    · exact (le_iSup₂ (f := fun j (_ : j.val < k) ↦ R j) j hj).trans
        (le_sup_right.trans le_sup_left)
    · obtain rfl : j = ⟨k, hk⟩ := Fin.ext hj
      exact le_sup_right
  · exact (le_iSup₂ (f := fun j (_ : j.val < k + 1) ↦ R j) j (by omega)).trans le_sup_right
  · exact (le_iSup₂ (f := fun j (_ : j.val < k + 1) ↦ R j) ⟨k, hk⟩ (by dsimp only; omega)).trans
      le_sup_right

private lemma prismFiltration_eq_top : prismFiltration.{u} m (m + 1) = ⊤ := by
  refine top_le_iff.1 fun ⟨⟨d⟩⟩ x _ ↦ (mem_prismFiltration_iff _ x).2 ?_
  by_cases h : ∀ t, x.1 t = 1
  · exact Or.inl (Or.inr h)
  push Not at h
  obtain ⟨t₁, ht₁⟩ := h
  have h₀ (t) : x.1 t ≠ 1 ↔ (x.1 t).val = 0 := by
    have := (x.1 t).isLt
    rw [Ne, Fin.ext_iff, Fin.val_one]
    omega
  have hx₁ {t t' : Fin (d + 1)} (h : t ≤ t') : (x.1 t).val ≤ (x.1 t').val :=
    Fin.le_iff_val_le_val.1 (stdSimplex.monotone_apply x.1 h)
  have hx₂ {t t' : Fin (d + 1)} (h : t ≤ t') : (x.2 t).val ≤ (x.2 t').val :=
    Fin.le_iff_val_le_val.1 (stdSimplex.monotone_apply x.2 h)
  let T := Finset.univ.filter (fun t ↦ (x.1 t).val = 0)
  have hT : T.Nonempty := ⟨t₁, Finset.mem_filter.2 ⟨Finset.mem_univ _, (h₀ t₁).1 ht₁⟩⟩
  obtain ⟨t₀, ht₀T, ht₀max⟩ : ∃ t₀ ∈ T, ∀ t ∈ T, t ≤ t₀ :=
    ⟨T.max' hT, T.max'_mem hT, fun t ht ↦ T.le_max' t ht⟩
  have ht₀ : (x.1 t₀).val = 0 := (Finset.mem_filter.1 ht₀T).2
  have hle (t) (ht : (x.1 t).val = 0) : t ≤ t₀ :=
    ht₀max t (Finset.mem_filter.2 ⟨Finset.mem_univ _, ht⟩)
  have hlt (t) (ht : (x.1 t).val ≠ 0) : t₀ < t := by
    by_contra h
    have := hx₁ (not_lt.1 h)
    omega
  let k := x.2 t₀
  let z : Fin (d + 1) → Fin (m + 2) := fun t ↦
    if (x.1 t).val = 0 then (x.2 t).castSucc else (x.2 t).succ
  have hz (t) : (z t).val = if (x.1 t).val = 0 then (x.2 t).val else (x.2 t).val + 1 := by
    simp only [z]
    split_ifs <;> rfl
  have hzm : Monotone z := fun t t' htt' ↦ by
    have h₁ := hx₁ htt'
    have h₂ := hx₂ htt'
    have := (x.1 t').isLt
    rw [Fin.le_iff_val_le_val, hz, hz]
    split_ifs <;> omega
  refine Or.inr ⟨k, k.isLt, stdSimplex.objMk ⟨z, hzm⟩,
    prodStdSimplex.objEquiv.injective (OrderHom.ext _ _ (funext fun t ↦ ?_))⟩
  have := (x.1 t).isLt
  have hk₁ : (x.1 t).val = 0 → (x.2 t).val ≤ k.val := fun h ↦ hx₂ (hle t h)
  have hk₂ : (x.1 t).val ≠ 0 → k.val ≤ (x.2 t).val := fun h ↦ hx₂ (hlt t h).le
  refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
  · refine (prismMap_app_fst _ _ t).trans (?_ : _ = (x.1 t).val)
    rw [stdSimplex.objMk_apply, OrderHom.coe_mk, hz]
    split_ifs <;> omega
  · refine (prismMap_app_snd _ _ t).trans (?_ : _ = (x.2 t).val)
    rw [stdSimplex.objMk_apply, OrderHom.coe_mk, hz]
    split_ifs <;> omega

end Walk

noncomputable def prismLastEdge (n : ℕ) :
    Δ[1] ⟶ ((Λ[1, 1] : (Δ[1] : SSet.{u}).Subcomplex).unionProd (∂Δ[n + 1]) : SSet.{u}) :=
  Subcomplex.lift (CartesianMonoidalCategory.lift (𝟙 _)
    (stdSimplex.map (SimplexCategory.const ⦋1⦌ ⦋n + 1⦌ (Fin.last _)))) (by
      rw [Subcomplex.range_eq_ofSimplex, Subcomplex.ofSimplex_le_iff]
      refine (Subcomplex.mem_unionProd_iff _ _ _).2 (Or.inl ?_)
      rw [mem_boundary_iff_notMem_range]
      exact ⟨0, fun ⟨t, ht⟩ ↦ (Fin.last_pos : 0 < Fin.last (n + 1)).ne' ht⟩)

section Filtration

variable {E B : SSet.{u}} (q : E ⟶ B) [InnerFibration q] {n : ℕ}
  (a : ((Λ[1, 1] : (Δ[1] : SSet.{u}).Subcomplex).unionProd (∂Δ[n + 1]) : SSet.{u}) ⟶ E)
  (b : Δ[1] ⊗ Δ[n + 1] ⟶ B)

private lemma restrictMap_horn_edge :
    ((restrictMap (prismMap.{u} ⟨n + 1, by omega⟩) (preimage_prismFiltration _)).app _
      (horn.edge (n + 2) (Fin.last (n + 2)) (Fin.last (n + 1)).castSucc (Fin.last (n + 2))
        (Fin.le_last _) (by simp))).val = (yonedaEquiv (prismLastEdge.{u} n)).val := by
  refine prodStdSimplex.objEquiv.injective (OrderHom.ext _ _ (funext fun t ↦ ?_))
  fin_cases t <;> refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
  · exact (walkFun_fst _ (Fin.last (n + 1)).castSucc).trans (if_pos le_rfl)
  · exact (walkFun_snd _ (Fin.last (n + 1)).castSucc).trans (if_pos le_rfl)
  · exact (walkFun_fst _ (Fin.last (n + 2))).trans (if_neg (by simp))
  · exact (walkFun_snd _ (Fin.last (n + 2))).trans ((if_neg (by simp)).trans rfl)

private lemma exists_extension_prismFiltration (w : a ≫ q = Subcomplex.ι _ ≫ b)
    (hf : IsCartesianEdge q (prismLastEdge n ≫ a)) (k : ℕ) (hk : k ≤ n + 2) :
    ∃ a' : (prismFiltration.{u} (n + 1) k : SSet.{u}) ⟶ E,
      Subcomplex.homOfLE le_sup_left ≫ a' = a ∧ a' ≫ q = Subcomplex.ι _ ≫ b := by
  induction k with
  | zero =>
    refine ⟨Subcomplex.homOfLE prismFiltration_zero.le ≫ a, ?_, ?_⟩
    · exact (Subcomplex.homOfLE_comp_assoc _ _ a).trans (Category.id_comp a)
    · rw [Category.assoc, w, ← Category.assoc, Subcomplex.homOfLE_ι]
  | succ k ih =>
    obtain ⟨a', ha', wa'⟩ := ih (by omega)
    let K : Fin (n + 2) := ⟨k, by omega⟩
    have hA := preimage_prismFiltration.{u} K
    have hl : ∃ l : Δ[n + 2] ⟶ E, Λ[n + 2, K.succ].ι ≫ l = restrictMap _ hA ≫ a' ∧
        l ≫ q = prismMap K ≫ b := by
      have sq : CommSq (restrictMap _ hA ≫ a') Λ[n + 2, K.succ].ι q (prismMap K ≫ b) :=
        ⟨by rw [Category.assoc, wa', restrictMap_ι_assoc]⟩
      suffices sq.HasLift from ⟨sq.lift, sq.fac_left, sq.fac_right⟩
      by_cases hkn : k ≤ n
      · exact (mem_innerFibrations q _ (horn_ι_mem_innerHornInclusions (Fin.succ_pos K)
          (Fin.lt_def.2 (by simp [K]; omega)))).sq_hasLift sq
      · obtain rfl : k = n + 1 := by omega
        refine (isCartesianEdge_iff_hasLift_horn q _).1 hf n _ _ sq ?_
        rw [yonedaEquiv_comp, ← ha']
        exact congrArg (a'.app _) (Subtype.ext restrictMap_horn_edge)
    obtain ⟨l, hl₁, hl₂⟩ := hl
    obtain ⟨a'', ha'', wa''⟩ := exists_extension _ hA a' b wa' l hl₁ hl₂
    refine ⟨Subcomplex.homOfLE (prismFiltration_succ k (by omega)).le ≫ a'', ?_, ?_⟩
    · rw [← ha', ← ha'']
      exact (Subcomplex.homOfLE_comp_assoc _ _ _).trans (Subcomplex.homOfLE_comp_assoc _ _ _).symm
    · rw [Category.assoc, wa'', ← Category.assoc, Subcomplex.homOfLE_ι]

end Filtration

theorem IsCartesianEdge.hasLift_unionProd {X S : SSet.{u}} (p : X ⟶ S)
    [InnerFibration p] {f : Δ[1] ⟶ X} (hf : IsCartesianEdge p f) (n : ℕ)
    (a : ((Λ[1, 1] : (Δ[1] : SSet.{u}).Subcomplex).unionProd (∂Δ[n + 1]) : SSet.{u}) ⟶ X)
    (b : Δ[1] ⊗ Δ[n + 1] ⟶ S) (sq : CommSq a (Λ[1, 1].unionProd ∂Δ[n + 1]).ι p b)
    (ha : prismLastEdge n ≫ a = f) : sq.HasLift := by
  obtain ⟨a', ha', wa'⟩ := exists_extension_prismFiltration p a b sq.w (ha ▸ hf) (n + 2) le_rfl
  have ht := prismFiltration_eq_top.{u} (m := n + 1)
  refine ⟨⟨⟨(Subcomplex.topIso _).inv ≫ Subcomplex.homOfLE ht.ge ≫ a', ?_, ?_⟩⟩⟩
  · rw [← ha', ← Category.assoc, ← Category.assoc]
    congr 1
  · rw [Category.assoc, Category.assoc, wa', ← Category.assoc (Subcomplex.homOfLE _),
      Subcomplex.homOfLE_ι, ← Category.assoc, Subcomplex.topIso_inv_ι, Category.id_comp]

section Retraction

variable (n : ℕ)

private def retractionFun : Fin 2 × Fin (n + 3) →o Fin (n + 3) where
  toFun x := ⟨if x.1.val = 1 ∧ x.2.val = n + 1 then n + 2 else x.2.val, by split_ifs <;> omega⟩
  monotone' x y h := by
    have h₁ : x.1.val ≤ y.1.val := h.1
    have h₂ : x.2.val ≤ y.2.val := h.2
    have := x.1.isLt
    have := y.1.isLt
    have := y.2.isLt
    rw [Fin.le_iff_val_le_val]
    dsimp only
    split_ifs <;> omega

private noncomputable def retraction : Δ[1] ⊗ Δ[n + 2] ⟶ (Δ[n + 2] : SSet.{u}) :=
  (prodStdSimplex.isoNerve 1 (n + 2)).hom ≫
    nerveMap (ULift.orderIso.symm.monotone.comp ((retractionFun n).monotone.comp
      ULift.orderIso.monotone)).functor ≫ (stdSimplex.isoNerve (n + 2)).inv

private lemma retraction_app_val {d : ℕ} (x : (Δ[1] ⊗ Δ[n + 2] : SSet.{u}) _⦋d⦌)
    (t : Fin (d + 1)) : (((retraction.{u} n).app _ x) t).val =
      if (x.1 t).val = 1 ∧ (x.2 t).val = n + 1 then n + 2 else (x.2 t).val :=
  rfl

private noncomputable def retractionSection : Δ[n + 2] ⟶ (Δ[1] ⊗ Δ[n + 2] : SSet.{u}) :=
  CartesianMonoidalCategory.lift (stdSimplex.map (SimplexCategory.const _ ⦋1⦌ 0)) (𝟙 _)

private lemma retractionSection_retraction :
    retractionSection.{u} n ≫ retraction n = 𝟙 _ :=
  yonedaEquiv.injective (stdSimplex.ext _ _ fun t ↦ Fin.ext (by
    rw [yonedaEquiv_comp, retraction_app_val]
    have h : ((yonedaEquiv (retractionSection.{u} n)).1 t).val = 0 := rfl
    rw [h, if_neg (by simp)]
    rfl))

private noncomputable def retractionSectionHorn :
    (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) ⟶
      ((Λ[1, 1] : (Δ[1] : SSet.{u}).Subcomplex).unionProd Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) :=
  Subcomplex.lift (Subcomplex.ι _ ≫ retractionSection n) (by
    rintro ⟨⟨d⟩⟩ _ ⟨y, rfl⟩
    exact (Subcomplex.mem_unionProd_iff _ _ _).2 (Or.inl y.2))

@[reassoc]
private lemma retractionSectionHorn_ι :
    retractionSectionHorn.{u} n ≫ Subcomplex.ι _ = Subcomplex.ι _ ≫ retractionSection n :=
  Subcomplex.lift_ι _ _

private noncomputable def retractionHorn :
    ((Λ[1, 1] : (Δ[1] : SSet.{u}).Subcomplex).unionProd Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) ⟶
      (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) :=
  Subcomplex.lift (Subcomplex.ι _ ≫ retraction n) (by
    rintro ⟨⟨d⟩⟩ _ ⟨⟨x, hx⟩, rfl⟩
    rw [mem_horn_iff_notMem_range]
    rcases (Subcomplex.mem_unionProd_iff _ _ x).1 hx with hx | hx
    · obtain ⟨v, hv, hvx⟩ := (mem_horn_iff_notMem_range _ _).1 hx
      have hv' : v.val ≠ n + 2 := fun h ↦ hv (Fin.ext h)
      by_cases hv₁ : v.val = n + 1
      · refine ⟨v, hv, fun ⟨t, ht⟩ ↦ hvx ⟨t, Fin.ext ?_⟩⟩
        have h : ((retraction n).app _ x t).val = v.val := congrArg Fin.val ht
        rw [retraction_app_val] at h
        split_ifs at h <;> omega
      · refine ⟨v, hv, fun ⟨t, ht⟩ ↦ hvx ⟨t, Fin.ext ?_⟩⟩
        have h : ((retraction n).app _ x t).val = v.val := congrArg Fin.val ht
        rw [retraction_app_val] at h
        split_ifs at h <;> omega
    · obtain ⟨w, hw, hwx⟩ := (mem_horn_iff_notMem_range _ _).1 hx
      have hw₀ : w = 0 := by
        fin_cases w
        · rfl
        · exact absurd rfl hw
      refine ⟨⟨n + 1, by omega⟩, fun h ↦ absurd (congrArg Fin.val h) (by simp), fun ⟨t, ht⟩ ↦ ?_⟩
      have h : ((retraction n).app _ x t).val = n + 1 := congrArg Fin.val ht
      rw [retraction_app_val] at h
      have h₁ : (x.1 t).val = 1 := by
        have := (x.1 t).isLt
        have : x.1 t ≠ 0 := fun h ↦ hwx ⟨t, h.trans hw₀.symm⟩
        rw [Ne, Fin.ext_iff, Fin.val_zero] at this
        omega
      split_ifs at h with h' <;> omega)

@[reassoc]
private lemma retractionHorn_ι :
    retractionHorn.{u} n ≫ Subcomplex.ι _ = Subcomplex.ι _ ≫ retraction n :=
  Subcomplex.lift_ι _ _

noncomputable def hornLastRetract :
    RetractArrow Λ[n + 2, Fin.last (n + 2)].ι
      ((Λ[1, 1] : (Δ[1] : SSet.{u}).Subcomplex).unionProd Λ[n + 2, Fin.last (n + 2)]).ι where
  i := Arrow.homMk (retractionSectionHorn n) (retractionSection n) rfl
  r := Arrow.homMk (retractionHorn n) (retraction n) rfl
  retract := by
    refine Arrow.hom_ext _ _ ((cancel_mono (Subcomplex.ι _)).1 ?_) (retractionSection_retraction n)
    have e : retractionSectionHorn.{u} n ≫ retractionHorn n ≫ Subcomplex.ι _ = Subcomplex.ι _ := by
      rw [retractionHorn_ι, retractionSectionHorn_ι_assoc, retractionSection_retraction,
        Category.comp_id]
    exact (Category.assoc _ _ _).trans (e.trans (Category.id_comp _).symm)

theorem lift_const_comp_hornLastRetract_r_right (v : Fin (n + 3))
    (hv : v ≠ (Fin.last (n + 1)).castSucc) :
    CartesianMonoidalCategory.lift (𝟙 Δ[1]) (stdSimplex.map (SimplexCategory.const ⦋1⦌ _ v)) ≫
      (hornLastRetract.{u} n).r.right = stdSimplex.map (SimplexCategory.const ⦋1⦌ _ v) :=
  yonedaEquiv.injective (stdSimplex.ext _ _ fun t ↦ Fin.ext (by
    rw [yonedaEquiv_comp]
    refine (retraction_app_val n _ t).trans (if_neg fun h ↦ hv (Fin.ext ?_))
    exact h.2))

theorem lift_const_last_comp_hornLastRetract_r_right :
    CartesianMonoidalCategory.lift (𝟙 Δ[1])
        (stdSimplex.map (SimplexCategory.const ⦋1⦌ _ (Fin.last (n + 1)).castSucc)) ≫
      (hornLastRetract.{u} n).r.right = yonedaEquiv.symm
        (stdSimplex.edge (n + 2) (Fin.last (n + 1)).castSucc (Fin.last (n + 2)) (Fin.le_last _)) :=
  yonedaEquiv.injective (stdSimplex.ext _ _ fun t ↦ Fin.ext (by
    rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
    refine (retraction_app_val n _ t).trans ?_
    fin_cases t
    · exact if_neg fun h ↦ Nat.zero_ne_one h.1
    · exact if_pos ⟨rfl, rfl⟩))

theorem hornLastRetract_i_right : (hornLastRetract.{u} n).i.right =
    CartesianMonoidalCategory.lift (stdSimplex.map (SimplexCategory.const _ ⦋1⦌ 0)) (𝟙 _) :=
  rfl

end Retraction

section Converse

variable (n : ℕ)

private lemma preimage_horn_δ_last :
    (Λ[n + 2, Fin.last (n + 2)] : (Δ[n + 2] : SSet.{u}).Subcomplex).preimage
      (stdSimplex.δ (Fin.last (n + 2))) = ∂Δ[n + 1] := by
  ext ⟨⟨d⟩⟩ y
  rw [Subcomplex.preimage_obj, Set.mem_preimage, mem_horn_iff_notMem_range,
    mem_boundary_iff_notMem_range]
  have hy (t) : (((stdSimplex.δ (Fin.last (n + 2))).app _ y : Δ[n + 2] _⦋d⦌) t).val = (y t).val :=
    congrArg Fin.val (Fin.succAbove_last_apply (y t))
  refine ⟨fun ⟨v, hv, hvy⟩ ↦ ?_, fun ⟨v, hvy⟩ ↦ ⟨v.castSucc, Fin.castSucc_ne_last v,
    fun ⟨t, ht⟩ ↦ hvy ⟨t, Fin.ext ((hy t).symm.trans (congrArg Fin.val ht))⟩⟩⟩
  have hv' : v.val < n + 2 := by
    have := v.isLt
    have : v.val ≠ n + 2 := fun h ↦ hv (Fin.ext h)
    omega
  exact ⟨⟨v.val, hv'⟩, fun ⟨t, ht⟩ ↦ hvy ⟨t, Fin.ext ((hy t).trans (congrArg Fin.val ht))⟩⟩

private lemma unionProd_horn_sup_range :
    (Λ[1, 1] : (Δ[1] : SSet.{u}).Subcomplex).unionProd Λ[n + 2, Fin.last (n + 2)] ⊔
        Subcomplex.range (𝟙 Δ[1] ⊗ₘ stdSimplex.δ (Fin.last (n + 2))) =
      (Λ[1, 1] : (Δ[1] : SSet.{u}).Subcomplex).unionProd ∂Δ[n + 2] := by
  refine le_antisymm (sup_le ?_ ?_) ?_
  · refine sup_le_sup (Subcomplex.prod_monotone le_rfl fun _ y hy ↦ ?_) le_rfl
    obtain ⟨v, -, hv⟩ := (mem_horn_iff_notMem_range _ _).1 hy
    exact (mem_boundary_iff_notMem_range _).2 ⟨v, hv⟩
  · rintro ⟨⟨d⟩⟩ _ ⟨x, rfl⟩
    refine (Subcomplex.mem_unionProd_iff _ _ _).2 (Or.inl ?_)
    rw [mem_boundary_iff_notMem_range]
    refine ⟨Fin.last _, fun ⟨t, ht⟩ ↦ ?_⟩
    exact Fin.castSucc_ne_last _ ((Fin.succAbove_last_apply (x.2 t)).symm.trans ht)
  · rintro ⟨⟨d⟩⟩ x hx
    rcases (Subcomplex.mem_unionProd_iff _ _ _).1 hx with hx | hx
    · obtain ⟨v, hvx⟩ := (mem_boundary_iff_notMem_range _).1 hx
      by_cases hv : v = Fin.last _
      · subst hv
        obtain ⟨θ, hθ⟩ := SimplexCategory.eq_comp_δ_of_not_surjective'
          (stdSimplex.objEquiv x.2) (Fin.last _) fun t h ↦ hvx ⟨t, h⟩
        refine Or.inr ⟨(x.1, stdSimplex.objEquiv.symm θ), Prod.ext rfl ?_⟩
        exact stdSimplex.objEquiv.injective hθ.symm
      · exact Or.inl ((Subcomplex.mem_unionProd_iff _ _ _).2
          (Or.inl ((mem_horn_iff_notMem_range _ _).2 ⟨v, hv, hvx⟩)))
    · exact Or.inl ((Subcomplex.mem_unionProd_iff _ _ _).2 (Or.inr hx))

private instance : Mono (𝟙 Δ[1] ⊗ₘ stdSimplex.δ.{u} (Fin.last (n + 2))) := by
  rw [NatTrans.mono_iff_mono_app]
  intro k
  have h := (NatTrans.mono_iff_mono_app (stdSimplex.δ.{u} (Fin.last (n + 2)))).1 inferInstance k
  rw [mono_iff_injective] at h ⊢
  intro x y hxy
  have h₁ := congrArg Prod.fst hxy
  have h₂ := congrArg Prod.snd hxy
  exact Prod.ext h₁ (h h₂)

private lemma preimage_unionProd_horn :
    ((Λ[1, 1] : (Δ[1] : SSet.{u}).Subcomplex).unionProd Λ[n + 2, Fin.last (n + 2)]).preimage
      (𝟙 Δ[1] ⊗ₘ stdSimplex.δ (Fin.last (n + 2))) = (Λ[1, 1]).unionProd ∂Δ[n + 1] := by
  rw [Subcomplex.preimage_unionProd, Subcomplex.preimage_id, preimage_horn_δ_last]

private lemma prismLastEdge_comp_restrictMap :
    prismLastEdge n ≫ restrictMap _ (preimage_unionProd_horn.{u} n) ≫ (hornLastRetract n).r.left =
      yonedaEquiv.symm (horn.edge (n + 2) (Fin.last (n + 2)) (Fin.last (n + 1)).castSucc
        (Fin.last (n + 2)) (Fin.le_last _) (by simp)) := by
  refine (cancel_mono (Subcomplex.ι _)).1 ?_
  have e : prismLastEdge.{u} n ≫ Subcomplex.ι _ ≫ (𝟙 Δ[1] ⊗ₘ stdSimplex.δ (Fin.last (n + 2))) =
      CartesianMonoidalCategory.lift (𝟙 Δ[1])
        (stdSimplex.map (SimplexCategory.const ⦋1⦌ _ (Fin.last (n + 1)).castSucc)) := by
    rw [prismLastEdge, Subcomplex.lift_ι_assoc, CartesianMonoidalCategory.lift_map,
      Category.comp_id]
    refine congrArg (CartesianMonoidalCategory.lift (𝟙 Δ[1])) ((Functor.map_comp stdSimplex
      (SimplexCategory.const ⦋1⦌ ⦋n + 1⦌ _) (SimplexCategory.δ (Fin.last (n + 2)))).symm.trans
        (congrArg stdSimplex.map ?_))
    rw [SimplexCategory.const_comp]
    exact congrArg _ (Fin.succAbove_last_apply _)
  refine (Category.assoc _ _ _).trans ((congrArg (prismLastEdge n ≫ ·) ((Category.assoc _ _ _).trans
    (congrArg (restrictMap _ _ ≫ ·) (hornLastRetract.{u} n).r.w))).trans ?_)
  refine (congrArg (prismLastEdge n ≫ ·) (restrictMap_ι_assoc _ _ _)).trans ?_
  rw [← Category.assoc, ← Category.assoc, Category.assoc (prismLastEdge n), e]
  exact (lift_const_last_comp_hornLastRetract_r_right n).trans rfl

private lemma eq_σ_zero_comp {Y Z : SSet.{u}} (i : Y ⟶ Z) [Mono i] (g : Δ[1] ⟶ Y) (c : Δ[0] ⟶ Z)
    (h : g ≫ i = stdSimplex.σ 0 ≫ c) : g = stdSimplex.σ 0 ≫ stdSimplex.δ 0 ≫ g := by
  refine (cancel_mono i).1 ?_
  rw [Category.assoc, Category.assoc, h, ← Category.assoc (stdSimplex.δ 0),
    stdSimplex.δ_comp_σ_self' (n := 0) (j := 0) (i := 0) rfl, Category.id_comp]

private lemma isCartesianEdge_of_hasLift_unionProd {X S : SSet.{u}} (p : X ⟶ S) [InnerFibration p]
    (f : Δ[1] ⟶ X)
    (H : ∀ (n : ℕ) (a : ((Λ[1, 1] : (Δ[1] : SSet.{u}).Subcomplex).unionProd (∂Δ[n + 1]) :
        SSet.{u}) ⟶ X) (b : Δ[1] ⊗ Δ[n + 1] ⟶ S)
        (sq : CommSq a (Λ[1, 1].unionProd ∂Δ[n + 1]).ι p b), prismLastEdge n ≫ a = f → sq.HasLift) :
    IsCartesianEdge p f := by
  refine (isCartesianEdge_iff_forall_pullback p f).2 fun k b f' hf' ↦ ?_
  have : InnerFibration (pullback.snd p b) :=
    ⟨innerFibrations.of_isPullback (IsPullback.of_hasPullback p b) (mem_innerFibrations p)⟩
  have : InnerFibration (stdSimplex.isoNerve.{u} k).hom := ⟨innerFibrations.of_isIso _⟩
  have := quasicategory_of_innerFibration (stdSimplex.isoNerve.{u} k).hom
  have := quasicategory_of_innerFibration (pullback.snd p b)
  have H' (n : ℕ) (a : ((Λ[1, 1] : (Δ[1] : SSet.{u}).Subcomplex).unionProd (∂Δ[n + 1]) :
      SSet.{u}) ⟶ pullback p b) (β : Δ[1] ⊗ Δ[n + 1] ⟶ Δ[k])
      (sq : CommSq a (Λ[1, 1].unionProd ∂Δ[n + 1]).ι (pullback.snd p b) β)
      (ha : prismLastEdge n ≫ a = f') : sq.HasLift := by
    obtain ⟨l⟩ := (H n (a ≫ pullback.fst p b) (β ≫ b) ⟨by
      rw [Category.assoc, pullback.condition, ← Category.assoc, sq.w, Category.assoc]⟩
      (by rw [← Category.assoc, ha, hf'])).exists_lift
    refine ⟨⟨⟨pullback.lift l.l β l.fac_right, pullback.hom_ext ?_ ?_,
      pullback.lift_snd _ _ _⟩⟩⟩
    · rw [Category.assoc, pullback.lift_fst, l.fac_left]
    · rw [Category.assoc, pullback.lift_snd, sq.w]
  refine (isCartesianEdge_iff_hasLift_horn _ f').2 fun n h β sq hedge ↦ ?_
  let R := hornLastRetract.{u} n
  have wF : (R.r.left ≫ h) ≫ pullback.snd p b = Subcomplex.ι _ ≫ R.r.right ≫ β := by
    rw [Category.assoc, sq.w, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ β) R.r.w
  have hA := preimage_unionProd_horn.{u} n
  have sq₁ : CommSq (restrictMap _ hA ≫ R.r.left ≫ h) (Subcomplex.ι _) (pullback.snd p b)
      ((𝟙 Δ[1] ⊗ₘ stdSimplex.δ (Fin.last (n + 2))) ≫ R.r.right ≫ β) :=
    ⟨by rw [Category.assoc, wF, restrictMap_ι_assoc]⟩
  have hl₁ : prismLastEdge n ≫ restrictMap _ hA ≫ R.r.left ≫ h = f' := by
    rw [← Category.assoc, ← Category.assoc, Category.assoc (prismLastEdge n),
      prismLastEdge_comp_restrictMap, yonedaEquiv_symm_comp, hedge, Equiv.symm_apply_apply]
  obtain ⟨l₁⟩ := (H' n _ _ sq₁ hl₁).exists_lift
  obtain ⟨a', ha', wa'⟩ := exists_extension _ hA _ _ wF l₁.l l₁.fac_left l₁.fac_right
  have hsup := unionProd_horn_sup_range.{u} n
  let a'' := Subcomplex.homOfLE hsup.ge ≫ a'
  have hle : (Λ[1, 1] : (Δ[1] : SSet.{u}).Subcomplex).unionProd Λ[n + 2, Fin.last (n + 2)] ≤
      (Λ[1, 1]).unionProd ∂Δ[n + 2] := hsup ▸ le_sup_left
  let eA : Δ[1] ⟶ ((Λ[1, 1] : (Δ[1] : SSet.{u}).Subcomplex).unionProd
      Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) :=
    Subcomplex.lift (prismLastEdge (n + 1) ≫ Subcomplex.ι _) (by
      rw [Subcomplex.range_eq_ofSimplex, Subcomplex.ofSimplex_le_iff]
      refine (Subcomplex.mem_unionProd_iff _ _ _).2 (Or.inl ((mem_horn_iff_notMem_range _ _).2
        ⟨0, (Fin.last_pos : 0 < Fin.last (n + 2)).ne, fun ⟨t, ht⟩ ↦ ?_⟩))
      exact (Fin.last_pos : 0 < Fin.last (n + 2)).ne' ht)
  have e₁ : prismLastEdge (n + 1) ≫ Subcomplex.homOfLE hsup.ge =
      eA ≫ Subcomplex.homOfLE le_sup_left :=
    (cancel_mono (Subcomplex.ι _)).1 (by
      rw [Category.assoc, Category.assoc, Subcomplex.homOfLE_ι, Subcomplex.homOfLE_ι,
        Subcomplex.lift_ι])
  have hdeg : prismLastEdge (n + 1) ≫ a'' = (eA ≫ R.r.left) ≫ h := by
    rw [Category.assoc, ← ha', ← Category.assoc, e₁, Category.assoc]
  have hg : (eA ≫ R.r.left) ≫ Subcomplex.ι _ =
      stdSimplex.σ 0 ≫ stdSimplex.map (SimplexCategory.const ⦋0⦌ _ (Fin.last (n + 2))) := by
    have wr : R.r.left ≫ Λ[n + 2, Fin.last (n + 2)].ι = Subcomplex.ι _ ≫ R.r.right := R.r.w
    rw [Category.assoc, wr, ← Category.assoc, Subcomplex.lift_ι, Category.assoc,
      prismLastEdge, Subcomplex.lift_ι_assoc]
    refine (lift_const_comp_hornLastRetract_r_right n (Fin.last (n + 2))
      (Fin.castSucc_ne_last _).symm).trans ?_
    refine (congrArg stdSimplex.map (SimplexCategory.const_fac_thru_zero _ _ _)).trans
      ((Functor.map_comp stdSimplex _ _).trans ?_)
    exact congrArg (· ≫ _) (congrArg stdSimplex.map (SimplexCategory.eq_const_to_zero _).symm)
  have hc : IsCartesianEdge (pullback.snd p b) (prismLastEdge (n + 1) ≫ a'') := by
    have h₀ := SSet.isCartesianEdge_id (pullback.snd p b)
      (yonedaEquiv (stdSimplex.δ 0 ≫ (eA ≫ R.r.left) ≫ h))
    rw [Edge.id_edge, ← stdSimplex.σ_comp_yonedaEquiv_symm, Equiv.symm_apply_apply] at h₀
    rwa [hdeg, eq_σ_zero_comp _ _ _ hg, Category.assoc, Category.assoc]
  have sq₂ : CommSq a'' (Λ[1, 1].unionProd ∂Δ[n + 2]).ι (pullback.snd p b) (R.r.right ≫ β) :=
    ⟨by rw [Category.assoc, wa', ← Category.assoc, Subcomplex.homOfLE_ι]⟩
  obtain ⟨L⟩ := (IsCartesianEdge.hasLift_unionProd _ hc (n + 1) a'' _ sq₂ rfl).exists_lift
  have e₂ : Subcomplex.ι _ ≫ L.l = R.r.left ≫ h :=
    ((Subcomplex.homOfLE_ι_assoc hle L.l).symm.trans
      (congrArg (Subcomplex.homOfLE hle ≫ ·) L.fac_left)).trans
        ((Subcomplex.homOfLE_comp_assoc _ _ _).trans ha')
  have wi : Λ[n + 2, Fin.last (n + 2)].ι ≫ R.i.right = R.i.left ≫ Subcomplex.ι _ := R.i.w.symm
  refine ⟨⟨⟨R.i.right ≫ L.l, ?_, ?_⟩⟩⟩
  · rw [← Category.assoc, wi, Category.assoc, e₂, ← Category.assoc]
    exact (congrArg (· ≫ h) (congrArg Arrow.Hom.left R.retract)).trans (Category.id_comp h)
  · rw [Category.assoc, L.fac_right, ← Category.assoc]
    exact (congrArg (· ≫ β) (congrArg Arrow.Hom.right R.retract)).trans (Category.id_comp β)

end Converse

theorem isCartesianEdge_iff_hasLift_unionProd {X S : SSet.{u}} (p : X ⟶ S) [InnerFibration p]
    (f : Δ[1] ⟶ X) :
    IsCartesianEdge p f ↔
      ∀ (n : ℕ)
        (a : ((Λ[1, 1] : (Δ[1] : SSet.{u}).Subcomplex).unionProd (∂Δ[n + 1]) : SSet.{u}) ⟶ X)
        (b : Δ[1] ⊗ Δ[n + 1] ⟶ S) (sq : CommSq a (Λ[1, 1].unionProd ∂Δ[n + 1]).ι p b),
        prismLastEdge n ≫ a = f → sq.HasLift :=
  ⟨fun hf n a b sq ha ↦ hf.hasLift_unionProd p n a b sq ha,
    isCartesianEdge_of_hasLift_unionProd p f⟩

end SSet
