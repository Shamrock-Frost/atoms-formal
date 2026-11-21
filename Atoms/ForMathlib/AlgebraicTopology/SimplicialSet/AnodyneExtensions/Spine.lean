import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits
import Mathlib.AlgebraicTopology.SimplicialSet.Path
import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.Subcomplex

open CategoryTheory Limits MorphismProperty Simplicial

universe u

namespace SSet

namespace stdSimplex

def facesOutside (n : ℕ) (S : Finset (Fin (n + 1))) : (Δ[n] : SSet.{u}).Subcomplex :=
  ⨆ (j : Fin (n + 1)) (_ : j ∉ S), face {j}ᶜ

@[simp]
theorem mem_facesOutside_iff {n : ℕ} (S : Finset (Fin (n + 1))) {d : ℕ}
    (x : (Δ[n] : SSet.{u}) _⦋d⦌) :
    x ∈ (facesOutside n S).obj _ ↔ ∃ j ∉ S, ∀ k, x k ≠ j := by
  simp [facesOutside]

theorem preimage_facesOutside {n : ℕ} (S : Finset (Fin (n + 2))) (i : Fin (n + 2)) (hi : i ∈ S) :
    (facesOutside.{u} (n + 1) S).preimage (stdSimplex.δ i) =
      facesOutside n (S.preimage i.succAbove (Fin.succAbove_right_injective.injOn)) := by
  ext ⟨d⟩ x
  induction d using SimplexCategory.rec with | _ d => ?_
  simp only [Subcomplex.preimage_obj, Set.mem_preimage, mem_facesOutside_iff, Finset.mem_preimage]
  constructor
  · rintro ⟨j, hj, hx⟩
    obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq (x := j) (y := i) (by rintro rfl; exact hj hi)
    exact ⟨j, hj, fun k hk ↦ hx k (by rw [← hk]; rfl)⟩
  · rintro ⟨j, hj, hx⟩
    exact ⟨i.succAbove j, hj, fun k hk ↦ hx k (Fin.succAbove_right_injective hk)⟩

theorem facesOutside_singleton {n : ℕ} (b : Fin (n + 1)) :
    facesOutside.{u} n {b} = Λ[n, b] := by
  rw [horn_eq_iSup]
  ext ⟨d⟩ x
  induction d using SimplexCategory.rec with | _ d => ?_
  simp

theorem facesOutside_sup_face {n : ℕ} (S : Finset (Fin (n + 1))) (i : Fin (n + 1)) :
    facesOutside.{u} n S ⊔ face {i}ᶜ = facesOutside n (S.erase i) := by
  ext ⟨d⟩ x
  induction d using SimplexCategory.rec with | _ d => ?_
  simp only [Subfunctor.max_obj, Set.mem_union, mem_facesOutside_iff, mem_face_iff,
    Finset.mem_compl, Finset.mem_singleton, Finset.mem_erase]
  constructor
  · rintro (⟨j, hj, hx⟩ | hx)
    · exact ⟨j, fun h ↦ hj h.2, hx⟩
    · exact ⟨i, fun h ↦ h.1 rfl, hx⟩
  · rintro ⟨j, hj, hx⟩
    by_cases hji : j = i
    · subst hji
      exact Or.inr hx
    · exact Or.inl ⟨j, fun h ↦ hj ⟨hji, h⟩, hx⟩

end stdSimplex

open stdSimplex

private lemma innerAnodyneExtensions_homOfLE_sup_face {n : ℕ} (i : Fin (n + 2))
    (A : (Δ[n + 1] : SSet.{u}).Subcomplex)
    (h : innerAnodyneExtensions (A.preimage (stdSimplex.δ i)).ι) :
    innerAnodyneExtensions (Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ face {i}ᶜ)) := by
  have h' := (innerAnodyneExtensions.arrow_mk_iso_iff
    (Subcomplex.preimageιArrowIso (stdSimplex.δ i) A)).1 h
  rw [range_δ] at h'
  have sq : Subcomplex.BicartSq (A ⊓ face {i}ᶜ) A (face {i}ᶜ) (A ⊔ face {i}ᶜ) :=
    { sup_eq := rfl, inf_eq := rfl }
  exact innerAnodyneExtensions.of_isPushout sq.isPushout h'

theorem innerAnodyneExtensions_facesOutside_ι {n : ℕ} (S : Finset (Fin (n + 1)))
    (hS : ∃ a b c, a < b ∧ b < c ∧ a ∉ S ∧ b ∈ S ∧ c ∉ S) :
    innerAnodyneExtensions (stdSimplex.facesOutside n S).ι := by
  induction n with
  | zero =>
    obtain ⟨a, b, -, hab, -⟩ := hS
    exact absurd hab (by omega)
  | succ m ihm =>
    induction S using Finset.strongInduction with
    | H S ih =>
    obtain ⟨a, b, c, hab, hbc, ha, hb, hc⟩ := hS
    by_cases hSb : S = {b}
    · subst hSb
      rw [facesOutside_singleton]
      exact innerAnodyneExtensions.horn_ι (lt_of_le_of_lt (Fin.zero_le a) hab)
        (lt_of_lt_of_le hbc (Fin.le_last c))
    obtain ⟨i, hi, hib⟩ : ∃ i ∈ S, i ≠ b := by
      by_contra! h
      exact hSb (Finset.eq_singleton_iff_unique_mem.2 ⟨hb, h⟩)
    have h₁ := innerAnodyneExtensions_homOfLE_sup_face i (facesOutside (m + 1) S) (by
      rw [preimage_facesOutside S i hi]
      obtain ⟨α, rfl⟩ := Fin.exists_succAbove_eq (x := a) (y := i) (by rintro rfl; exact ha hi)
      obtain ⟨β, rfl⟩ := Fin.exists_succAbove_eq (x := b) (y := i) (Ne.symm hib)
      obtain ⟨γ, rfl⟩ := Fin.exists_succAbove_eq (x := c) (y := i) (by rintro rfl; exact hc hi)
      exact ihm _ ⟨α, β, γ, Fin.succAbove_lt_succAbove_iff.1 hab,
        Fin.succAbove_lt_succAbove_iff.1 hbc, by simpa using ha, by simpa using hb,
        by simpa using hc⟩)
    have h₂ : innerAnodyneExtensions (facesOutside (m + 1) S ⊔ face {i}ᶜ).ι := by
      rw [facesOutside_sup_face]
      exact ih _ (Finset.erase_ssubset hi) ⟨a, b, c, hab, hbc, by simp [ha], by simp [hb, hib.symm],
        by simp [hc]⟩
    exact innerAnodyneExtensions.comp_mem _ _ h₁ h₂

def spineSubcomplex : (n : ℕ) → (Δ[n] : SSet.{u}).Subcomplex
  | 0 => ⊤
  | n + 1 => ⨆ i : Fin (n + 1), stdSimplex.face {i.castSucc, i.succ}

theorem spineSubcomplex_zero : spineSubcomplex.{u} 0 = ⊤ := rfl

theorem spineSubcomplex_succ (n : ℕ) :
    spineSubcomplex.{u} (n + 1) = ⨆ i : Fin (n + 1), stdSimplex.face {i.castSucc, i.succ} := rfl

theorem mem_spineSubcomplex_iff {n d : ℕ} (x : (Δ[n] : SSet.{u}) _⦋d⦌) :
    x ∈ (spineSubcomplex n).obj _ ↔ ∀ k, (x k : ℕ) ≤ x 0 + 1 := by
  have hmono := stdSimplex.monotone_apply x
  cases n with
  | zero =>
    simp only [spineSubcomplex_zero, Subfunctor.top_obj, Set.top_eq_univ, Set.mem_univ, true_iff]
    intro k
    have := (x k).isLt
    omega
  | succ n =>
    simp only [spineSubcomplex_succ, Subfunctor.iSup_obj, Set.mem_iUnion,
      stdSimplex.mem_face_iff, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff,
      Fin.val_castSucc, Fin.val_succ]
    constructor
    · rintro ⟨i, hi⟩ k
      have := hi k
      have := hi 0
      omega
    · intro h
      refine ⟨⟨min (x 0) n, by omega⟩, fun k ↦ ?_⟩
      have h0 : (x 0 : ℕ) ≤ x k := hmono (Fin.zero_le k)
      have := h k
      have := (x k).isLt
      simp only
      omega

private lemma preimage_spineSubcomplex_δ_last (n : ℕ) :
    (spineSubcomplex.{u} (n + 1)).preimage (stdSimplex.δ (Fin.last (n + 1))) =
      spineSubcomplex n := by
  ext ⟨d⟩ x
  induction d using SimplexCategory.rec with | _ d => ?_
  simp only [Subcomplex.preimage_obj, Set.mem_preimage, mem_spineSubcomplex_iff]
  change (∀ k, ((Fin.last (n + 1)).succAbove (x k) : ℕ) ≤
    (Fin.last (n + 1)).succAbove (x 0) + 1) ↔ _
  simp only [Fin.succAbove_last, Fin.val_castSucc]

private lemma preimage_spineSubcomplex_δ_zero (n : ℕ) :
    (spineSubcomplex.{u} (n + 1)).preimage (stdSimplex.δ 0) = spineSubcomplex n := by
  ext ⟨d⟩ x
  induction d using SimplexCategory.rec with | _ d => ?_
  simp only [Subcomplex.preimage_obj, Set.mem_preimage, mem_spineSubcomplex_iff]
  change (∀ k, ((x k).succ : ℕ) ≤ (x 0).succ + 1) ↔ _
  simp only [Fin.val_succ, add_le_add_iff_right]

private lemma preimage_face_last_δ_zero (n : ℕ) :
    (face.{u} {Fin.last (n + 1)}ᶜ).preimage (stdSimplex.δ 0) = face {Fin.last n}ᶜ := by
  ext ⟨d⟩ x
  induction d using SimplexCategory.rec with | _ d => ?_
  simp only [Subcomplex.preimage_obj, Set.mem_preimage, mem_face_iff, Finset.mem_compl,
    Finset.mem_singleton]
  change (∀ k, (x k).succ ≠ Fin.last (n + 1)) ↔ _
  simp only [ne_eq, Fin.succ_eq_last_succ]

private lemma spineSubcomplex_one : spineSubcomplex.{u} 1 = ⊤ := by
  ext ⟨d⟩ x
  induction d using SimplexCategory.rec with | _ d => ?_
  simp only [mem_spineSubcomplex_iff, Subfunctor.top_obj, Set.top_eq_univ, Set.mem_univ,
    iff_true]
  intro k
  have := (x k).isLt
  omega

private lemma innerAnodyneExtensions_top_ι {n : ℕ} :
    innerAnodyneExtensions (⊤ : (Δ[n] : SSet.{u}).Subcomplex).ι :=
  innerAnodyneExtensions.of_isIso (Subcomplex.topIso _).hom

private lemma face_last_sup_spineSubcomplex_sup_face_zero (n : ℕ) :
    face {Fin.last (n + 2)}ᶜ ⊔ spineSubcomplex.{u} (n + 2) ⊔ face {0}ᶜ =
      facesOutside (n + 2) {0, Fin.last (n + 2)}ᶜ := by
  ext ⟨d⟩ x
  induction d using SimplexCategory.rec with | _ d => ?_
  simp only [Subfunctor.max_obj, Set.mem_union, mem_spineSubcomplex_iff, mem_face_iff,
    mem_facesOutside_iff, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_not]
  constructor
  · rintro ((h | h) | h)
    · exact ⟨_, Or.inr rfl, h⟩
    · by_cases h0 : (x 0 : ℕ) = 0
      · refine ⟨_, Or.inr rfl, fun k hk ↦ ?_⟩
        have := h k
        rw [hk] at this
        simp only [Fin.val_last] at this
        omega
      · refine ⟨_, Or.inl rfl, fun k hk ↦ h0 ?_⟩
        have : (x 0 : ℕ) ≤ x k := stdSimplex.monotone_apply x (Fin.zero_le k)
        rw [hk] at this
        simpa using this
    · exact ⟨_, Or.inl rfl, h⟩
  · rintro ⟨j, (rfl | rfl), h⟩
    · exact Or.inr h
    · exact Or.inl (Or.inl h)

private lemma innerAnodyneExtensions_face_last_sup_spineSubcomplex_ι (n : ℕ) :
    innerAnodyneExtensions (face {Fin.last (n + 1)}ᶜ ⊔ spineSubcomplex.{u} (n + 1)).ι := by
  induction n with
  | zero =>
    rw [spineSubcomplex_one, sup_top_eq]
    exact innerAnodyneExtensions_top_ι
  | succ n ih =>
    have h₁ := innerAnodyneExtensions_homOfLE_sup_face 0
      (face {Fin.last (n + 2)}ᶜ ⊔ spineSubcomplex.{u} (n + 2)) (by
        rw [Subcomplex.preimage_max, preimage_face_last_δ_zero, preimage_spineSubcomplex_δ_zero]
        exact ih)
    have h₂ : innerAnodyneExtensions
        (face {Fin.last (n + 2)}ᶜ ⊔ spineSubcomplex.{u} (n + 2) ⊔ face {0}ᶜ).ι := by
      rw [face_last_sup_spineSubcomplex_sup_face_zero]
      refine innerAnodyneExtensions_facesOutside_ι _ ⟨0, 1, Fin.last _, ?_, ?_, ?_, ?_, ?_⟩
      · exact Fin.lt_def.2 (by simp)
      · exact Fin.lt_def.2 (by simp)
      · simp
      · simp [Fin.ext_iff]
      · simp
    exact innerAnodyneExtensions.comp_mem _ _ h₁ h₂

theorem innerAnodyneExtensions_spineSubcomplex_ι (n : ℕ) :
    innerAnodyneExtensions (spineSubcomplex.{u} n).ι := by
  induction n with
  | zero => exact innerAnodyneExtensions_top_ι
  | succ n ih =>
    have h₁ := innerAnodyneExtensions_homOfLE_sup_face (Fin.last (n + 1))
      (spineSubcomplex.{u} (n + 1)) (by rw [preimage_spineSubcomplex_δ_last]; exact ih)
    have h₂ : innerAnodyneExtensions
        (spineSubcomplex.{u} (n + 1) ⊔ face {Fin.last (n + 1)}ᶜ).ι := by
      rw [sup_comm]
      exact innerAnodyneExtensions_face_last_sup_spineSubcomplex_ι n
    exact innerAnodyneExtensions.comp_mem _ _ h₁ h₂

namespace spineSubcomplex

theorem multicoequalizerDiagram (n : ℕ) :
    Subcomplex.MulticoequalizerDiagram (spineSubcomplex.{u} (n + 1))
      (fun i : Fin (n + 1) ↦ face {i.castSucc, i.succ})
      (fun i j ↦ face {i.castSucc, i.succ} ⊓ face {j.castSucc, j.succ}) where
  iSup_eq := rfl
  eq_inf _ _ := rfl

noncomputable def isColimit (n : ℕ) :
    IsColimit ((multicoequalizerDiagram.{u} n).multicofork.toLinearOrder.map
      Subcomplex.toSSetFunctor) :=
  (multicoequalizerDiagram n).isColimit'

def spineId (n : ℕ) : Path (spineSubcomplex.{u} n : SSet) n :=
  (spineSubcomplex n).liftPath (stdSimplex.spineId n)
    (fun _ ↦ (mem_spineSubcomplex_iff _).2 fun k ↦ by fin_cases k; simp)
    (fun i ↦ (mem_spineSubcomplex_iff _).2 fun k ↦ by fin_cases k <;> simp)

@[simp]
theorem spineId_map_ι (n : ℕ) : (spineId.{u} n).map (spineSubcomplex n).ι = stdSimplex.spineId n :=
  rfl

private lemma yonedaEquiv_facePairIso_hom_homOfLE {n : ℕ} (i : Fin (n + 1)) :
    yonedaEquiv ((facePairIso.{u} i.castSucc i.succ i.castSucc_lt_succ).hom ≫
      Subcomplex.homOfLE (le_iSup (fun i : Fin (n + 1) ↦ face {i.castSucc, i.succ}) i :
        _ ≤ spineSubcomplex (n + 1))) = (spineId (n + 1)).arrow i := by
  apply Subtype.ext
  ext k
  fin_cases k <;> rfl

private lemma faceSingletonIso_hom_homOfLE_facePairIso_inv {n : ℕ} (a b v : Fin (n + 1))
    (hab : a < b) (hv : v = a ∨ v = b) :
    (faceSingletonIso.{u} v).hom ≫ Subcomplex.homOfLE (by
        rw [face_le_face_iff]; rcases hv with rfl | rfl <;> simp) ≫
      (facePairIso a b hab).inv = stdSimplex.δ (if v = a then 1 else 0) := by
  rw [← cancel_mono ((facePairIso a b hab).hom ≫ (face {a, b}).ι)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rcases hv with rfl | rfl
  · rw [if_pos rfl]
    apply yonedaEquiv.injective
    ext k
    fin_cases k
    rfl
  · rw [if_neg hab.ne']
    apply yonedaEquiv.injective
    ext k
    fin_cases k
    rfl

variable {Z : SSet.{u}}

private lemma desc_compat {n : ℕ} (p : Z.Path (n + 1)) (i j : Fin (n + 1))
    (V : (Δ[n + 1] : SSet.{u}).Subcomplex) (h₁ : V ≤ face {i.castSucc, i.succ})
    (h₂ : V ≤ face {j.castSucc, j.succ})
    (hV : V = ⊥ ∨ V ≤ face {i.succ} ∧ j.castSucc = i.succ) :
    Subcomplex.homOfLE h₁ ≫ (facePairIso.{u} i.castSucc i.succ i.castSucc_lt_succ).inv ≫
        yonedaEquiv.symm (p.arrow i) =
      Subcomplex.homOfLE h₂ ≫ (facePairIso.{u} j.castSucc j.succ j.castSucc_lt_succ).inv ≫
        yonedaEquiv.symm (p.arrow j) := by
  obtain rfl | ⟨hv, hj⟩ := hV
  · exact Subsingleton.elim _ _
  have k₁ : face {i.succ} ≤ face.{u} {i.castSucc, i.succ} := by simp [face_le_face_iff]
  have k₂ : face {i.succ} ≤ face.{u} {j.castSucc, j.succ} := by simp [face_le_face_iff, hj]
  have e₁ := faceSingletonIso_hom_homOfLE_facePairIso_inv.{u} _ _ i.succ i.castSucc_lt_succ
    (Or.inr rfl)
  have e₂ := faceSingletonIso_hom_homOfLE_facePairIso_inv.{u} _ _ i.succ j.castSucc_lt_succ
    (Or.inl hj.symm)
  rw [if_neg (Fin.castSucc_lt_succ).ne'] at e₁
  rw [if_pos hj.symm] at e₂
  rw [← Subcomplex.homOfLE_comp hv k₁, ← Subcomplex.homOfLE_comp hv k₂, Category.assoc,
    Category.assoc]
  congr 1
  rw [← cancel_epi (faceSingletonIso i.succ).hom, reassoc_of% e₁, reassoc_of% e₂,
    stdSimplex.δ_comp_yonedaEquiv_symm, stdSimplex.δ_comp_yonedaEquiv_symm, p.arrow_tgt,
    p.arrow_src, hj]

private lemma edge_inf_edge {n : ℕ} (i j : Fin (n + 1)) (hij : i < j) :
    face.{u} {i.castSucc, i.succ} ⊓ face {j.castSucc, j.succ} = ⊥ ∨
      face.{u} {i.castSucc, i.succ} ⊓ face {j.castSucc, j.succ} ≤ face {i.succ} ∧
        j.castSucc = i.succ := by
  rw [face_inter_face]
  by_cases hj : j.castSucc = i.succ
  · refine Or.inr ⟨?_, hj⟩
    rw [face_le_face_iff]
    intro k
    simp only [Finset.inf_eq_inter, Finset.mem_inter, Finset.mem_insert,
      Finset.mem_singleton, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
    rw [Fin.lt_def] at hij
    simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at hj
    omega
  · refine Or.inl ?_
    rw [← face_empty]
    congr 1
    ext k
    simp only [Finset.inf_eq_inter, Finset.mem_inter, Finset.mem_insert,
      Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and, Fin.ext_iff,
      Fin.val_castSucc, Fin.val_succ]
    rw [Fin.lt_def] at hij
    simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at hj
    omega

private noncomputable def multicofork {n : ℕ} (p : Z.Path (n + 1)) :
    Multicofork ((multicoequalizerDiagram.{u} n).multispanIndex.toLinearOrder.map
      Subcomplex.toSSetFunctor) :=
  Multicofork.ofπ _ Z
    (fun i ↦ (facePairIso.{u} i.castSucc i.succ i.castSucc_lt_succ).inv ≫
      yonedaEquiv.symm (p.arrow i))
    (fun ⟨⟨i, j⟩, (hij : i < j)⟩ ↦
      desc_compat p i j _ inf_le_left inf_le_right (edge_inf_edge i j hij))

private noncomputable def desc {n : ℕ} (p : Z.Path (n + 1)) :
    (spineSubcomplex.{u} (n + 1) : SSet) ⟶ Z :=
  (isColimit.{u} n).desc (multicofork p)

private lemma homOfLE_desc {n : ℕ} (p : Z.Path (n + 1)) (i : Fin (n + 1)) :
    Subcomplex.homOfLE (le_iSup (fun i : Fin (n + 1) ↦ face.{u} {i.castSucc, i.succ}) i :
        _ ≤ spineSubcomplex (n + 1)) ≫ desc p =
      (facePairIso.{u} i.castSucc i.succ i.castSucc_lt_succ).inv ≫ yonedaEquiv.symm (p.arrow i) :=
  (isColimit.{u} n).fac (multicofork p) (.right i)

private lemma hom_ext {n : ℕ} {f g : (spineSubcomplex.{u} (n + 1) : SSet) ⟶ Z}
    (h : ∀ i : Fin (n + 1), Subcomplex.homOfLE (le_iSup
      (fun i : Fin (n + 1) ↦ face.{u} {i.castSucc, i.succ}) i : _ ≤ spineSubcomplex (n + 1)) ≫ f =
        Subcomplex.homOfLE (le_iSup _ i) ≫ g) : f = g :=
  Multicofork.IsColimit.hom_ext (isColimit.{u} n) h

private noncomputable def homEquivSucc (n : ℕ) (Z : SSet.{u}) :
    ((spineSubcomplex.{u} (n + 1) : SSet) ⟶ Z) ≃ Z.Path (n + 1) where
  toFun g := (spineId (n + 1)).map g
  invFun := desc
  left_inv g := by
    refine hom_ext fun i ↦ ?_
    rw [homOfLE_desc, Iso.inv_comp_eq]
    apply yonedaEquiv.injective
    rw [Equiv.apply_symm_apply]
    exact (congrArg (g.app _) (yonedaEquiv_facePairIso_hom_homOfLE i)).symm
  right_inv p := by
    refine Path.ext' fun i ↦ ?_
    change (desc p).app _ ((spineId (n + 1)).arrow i) = _
    rw [← yonedaEquiv_facePairIso_hom_homOfLE]
    refine (congrArg (fun f ↦ yonedaEquiv ((facePairIso.{u} i.castSucc i.succ
      i.castSucc_lt_succ).hom ≫ f)) (homOfLE_desc p i)).trans ?_
    simp only [Iso.hom_inv_id_assoc, Equiv.apply_symm_apply]

private lemma obj₀Equiv_symm_zero :
    stdSimplex.obj₀Equiv.symm 0 = yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by
  ext k
  fin_cases k
  rfl

private noncomputable def homEquivZero (Z : SSet.{u}) :
    ((spineSubcomplex.{u} 0 : SSet) ⟶ Z) ≃ Z.Path 0 where
  toFun g := (spineId 0).map g
  invFun p := (Subcomplex.topIso _).hom ≫ yonedaEquiv.symm (p.vertex 0)
  left_inv g := by
    have e : (Subcomplex.topIso (Δ[0] : SSet.{u})).inv ≫ (Subcomplex.topIso _).hom ≫
        yonedaEquiv.symm (((spineId 0).map g).vertex 0) = (Subcomplex.topIso _).inv ≫ g := by
      rw [Iso.inv_hom_id_assoc]
      apply yonedaEquiv.injective
      rw [Equiv.apply_symm_apply]
      exact congrArg (g.app _) (Subtype.ext obj₀Equiv_symm_zero)
    exact (cancel_epi (Subcomplex.topIso (Δ[0] : SSet.{u})).inv).1 e
  right_inv p := by
    ext
    change (yonedaEquiv.symm (p.vertex 0)).app _ (stdSimplex.obj₀Equiv.symm 0) = _
    rw [obj₀Equiv_symm_zero, yonedaEquiv_symm_app_id]

theorem bicartSq_two : Subcomplex.BicartSq.{u} (face {1}) (face {0, 1}) (face {1, 2})
    (spineSubcomplex 2) where
  sup_eq := by
    rw [spineSubcomplex_succ]
    apply le_antisymm
    · exact sup_le (le_iSup_of_le 0 le_rfl) (le_iSup_of_le 1 le_rfl)
    · refine iSup_le fun i => ?_
      fin_cases i
      · exact le_sup_left
      · exact le_sup_right
  inf_eq := by simp [face_inter_face]

def ι₀₁ : Δ[1] ⟶ (spineSubcomplex.{u} 2 : SSet) :=
  Subcomplex.lift (stdSimplex.δ 2) (by
    rw [Subcomplex.range_eq_ofSimplex, Subcomplex.ofSimplex_le_iff, mem_spineSubcomplex_iff]
    decide)

def ι₁₂ : Δ[1] ⟶ (spineSubcomplex.{u} 2 : SSet) :=
  Subcomplex.lift (stdSimplex.δ 0) (by
    rw [Subcomplex.range_eq_ofSimplex, Subcomplex.ofSimplex_le_iff, mem_spineSubcomplex_iff]
    decide)

@[reassoc (attr := simp)]
theorem ι₀₁_ι : ι₀₁.{u} ≫ (spineSubcomplex 2).ι = stdSimplex.δ 2 := rfl

@[reassoc (attr := simp)]
theorem ι₁₂_ι : ι₁₂.{u} ≫ (spineSubcomplex 2).ι = stdSimplex.δ 0 := rfl

theorem isPushout_two :
    IsPushout (stdSimplex.{u}.δ (0 : Fin 2)) (stdSimplex.{u}.δ (1 : Fin 2)) ι₀₁ ι₁₂ := by
  apply bicartSq_two.{u}.isPushout.of_iso' (faceSingletonIso _) (facePairIso _ _ (by simp))
    (facePairIso _ _ (by simp)) (Iso.refl _)
  all_goals decide

end spineSubcomplex

open spineSubcomplex in
noncomputable def spineSubcomplexHomEquiv : (n : ℕ) → (Z : SSet.{u}) →
    ((spineSubcomplex.{u} n : SSet) ⟶ Z) ≃ Z.Path n
  | 0, Z => homEquivZero Z
  | n + 1, Z => homEquivSucc n Z

theorem spineSubcomplexHomEquiv_apply (n : ℕ) {Z : SSet.{u}}
    (g : (spineSubcomplex.{u} n : SSet) ⟶ Z) :
    spineSubcomplexHomEquiv n Z g = (spineSubcomplex.spineId n).map g := by
  cases n <;> rfl

end SSet
